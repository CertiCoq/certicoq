
(** coqide -R /path/to/SquiggleLazyEq SquiggleLazyEq 
https://github.com/aa755/SquiggleLazyEq

*)


Require Import Arith BinNat String List Omega 
  Program Psatz.
Open Scope N_scope.
Opaque N.add.
Opaque N.sub.


Require Import Morphisms.
(*
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
*)

(* MathClasses or Extlib may habe a much richer theory and implementation *)
Require Import Coq.Classes.DecidableClass.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import SquiggleLazyEq.export.
Require Import SquiggleLazyEq.UsefulTypes.
Require Import SquiggleLazyEq.list.
Require Import SquiggleLazyEq.LibTactics.
Require Import SquiggleLazyEq.tactics.
Require Import SquiggleLazyEq.lmap.

Open Scope nat_scope.

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

(* see the file SquiggleLazyEq.varImplPeano for an instantiation of NVar *)
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

Inductive L4Opid : Set :=
 | NLambda
 | NFix (nMut : nat) (** number of functions that are mutually defined*)
 | NDCon (dc : dcon) (nargs : nat)
 | NApply
 | NProj (selector :nat) (** which one to project out*)
 | NLet
 | NMatch (dconAndNumArgs : list (dcon * nat)).


Definition OpBindingsL4 (nc : L4Opid) : list nat :=
  match nc with
  | NLambda    => [1]
  | NFix nMut => repeat 1 nMut
  | NDCon _ nargs    => repeat 0 nargs
  | NApply     => [0,0]
  | NProj _ => [0]
  | NLet => [0,1]
  | NMatch numargsInBranches => 0::(List.map snd numargsInBranches)
  end.

Definition decc: forall x y : L4Opid,
{x = y} + {x <> y}.
Proof using.
   repeat(decide equality).
Defined.

Require Import SquiggleLazyEq.alphaeq.


Definition CoqL4GenericTermSig : GenericTermSig :=
{| 
  Opid := L4Opid;
  OpBindings := OpBindingsL4;
  opid_dec := decc;
|}.


Notation BTerm := (@BTerm NVar CoqL4GenericTermSig).
Notation NTerm := (@NTerm NVar CoqL4GenericTermSig).
Notation oterm := (@oterm NVar CoqL4GenericTermSig).

Definition Lam_e (v : NVar) (b : NTerm) : NTerm :=
  oterm NLambda [bterm [v] b].

Definition Let_e (v : NVar) (e1 e2 : NTerm) : NTerm :=
  oterm NLet [(bterm [] e1);(bterm [v] e2)].

Definition App_e (f a : NTerm) :=
  oterm NApply [bterm [] f , bterm [] a].

Definition Con_e (dc : dcon) (args : list NTerm) : NTerm :=
  oterm (NDCon dc (length args)) (List.map (bterm []) args).

Definition Proj_e (arg : NTerm) (selector : nat)  : NTerm :=
  oterm (NProj selector) [bterm [] arg].

(** fix (\xf. (\x..,,)) *)
Definition Fix_e (xf : NVar) (args : list NTerm) : NTerm :=
  oterm (NFix (length args)) (List.map (bterm [xf]) args).

Definition Match_e (discriminee : NTerm) (brs : list branch) : NTerm :=
  oterm (NMatch (List.map (fun b => (fst b, num_bvars (snd b))) brs))
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


Definition Fix_e' (lbt : list BTerm) : NTerm :=
  oterm (NFix (length lbt)) lbt.


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
| eval_Fix_e : forall es, eval (Fix_e' es) (Fix_e' es)
| eval_Proj_e : forall xf e es n xl bl,
                  eval e (Fix_e' es) ->
                  select n es = Some (bterm [xf] (Lam_e xl bl)) ->
                  eval (Proj_e e n) ((Lam_e xl bl){xf:=Fix_e' es}).

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


Lemma find_branch_some: forall  {s} (d:N) (m:nat) (bs :list (@branch s)) b,
  find_branch d m bs = Some b
  -> LIn (d,b) bs /\ LIn b (map snd bs) /\ num_bvars b = m
  /\ find (fun a : branch => (d =? fst a)%N && (m =? num_bvars (snd a))) bs = Some (d, b).
Proof using.
  unfold find_branch. intros ? ? ? ? ? .
  destFind; intros Hdf; [| inverts Hdf].
  destruct bss as [dd bt].
  inverts Hdf.
  repnd.
  apply Decidable_sound in Heqsnl.
  simpl in Heqsnl.
  inverts Heqsnl. dands; auto.
  apply in_map_iff. eexists; split; eauto;  simpl; auto.
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
    rewrite (combine_map_fst es vs) by assumption.
    rewrite (combine_map_snd es vs) at 1 by assumption.
    repeat rewrite flat_map_map.
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
    apply find_branch_some in H. repnd.
    unfold num_bvars in H. simpl in H.
    rewrite dom_sub_combine in Hf;[| auto]. 
    rewrite in_app_iff in *.
    apply or_comm.
    dorn Hf;[left|right].
    + apply in_flat_map.
      exists (bterm lv nt). repnd. split;[| assumption].
      apply in_map_iff. eexists; split; eauto; simpl; auto.
    + apply IHHe1. apply in_sub_free_vars in Hf. exrepnd.
      apply in_flat_map. exists (bterm [] t).
      split;[| assumption]. apply in_map.
      apply in_sub_keep_first in Hf0. apply proj1 in Hf0.
      apply sub_find_some in Hf0. apply in_combine_r in Hf0.
      assumption.

- intros ? Hf. unfold subst.
  apply_clear IHHe. unfold subst in Hf.
  rewrite eqsetv_free_vars_disjoint in Hf.
   simpl in Hf.
  rewrite in_app_iff in *.
  dorn Hf. 
  + unfold compose. repnd.
    apply select_in in H. apply in_flat_map. eexists; split; eauto.
  + rewrite memvar_dmemvar in Hf. 
    if_splitH Hf; simpl in Hf; autorewrite with list in *;[|firstorder].
    assumption.
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
| fix_is_value : forall es, is_value (Fix_e' es).

(** Show that evaluation always yields a value. *)
Lemma eval_yields_value' :
  (forall e v, eval e v -> is_value v).
Proof using.
  intros ? ? He ; induction He ; simpl ; intros;
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
    rewrite (combine_map_snd es vs) by assumption.
    setoid_rewrite (combine_map_fst es vs) at 1;[|assumption].
    intros Hntwf ? Hin1.
    apply in_map_iff in Hin1. exrepnd.
    simpl in *. subst.
    eapply H1;eauto.
    apply Hntwf. apply in_map_iff; eexists; split; eauto; simpl; auto.
  + simpl in *. rewrite map_map in *. unfold compose, num_bvars in *. simpl in *.
    rewrite repeat_map_len in *. congruence.
- ntwfauto. apply IHHe2. ntwfauto.
- ntwfauto. apply IHHe2. destruct e'. simpl in *.
  ntwfauto.
  + rewrite list_nil_btwf in Hntwf0.
    apply in_combine_r in Hsub. auto.
  + apply find_branch_some in H. repnd.
    repnd. rewrite <- (bt_wf_iff l).
    apply Hntwf. auto.
- ntwfauto. 
  subst.
  apply select_in in H.
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
  rewrite (combine_map_snd es vs) by assumption.
  rewrite (combine_map_fst es vs) at 1 by assumption.
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
  apply find_branch_some in H as Hf.
  repnd.
  destruct e' as [lv nt].
  simpl in *.
  unfold num_bvars in Hf. simpl in *.
  rewrite dom_range_combine;[| auto].
  split;[|tauto].
  eapply varsOfClassSubset;[| apply Hn].
  intros ? Hin.
  rewrite flat_map_map.
  apply in_flat_map. eexists.
  split;[apply Hf0|].
  unfold compose.
  simpl.
  rewrite allvars_bterm.
  apply in_app_iff. tauto.

- remember (Lam_e xl bl) as r. clear Heqr.
  unfold Fix_e', Proj_e in *.
  apply ssubst_allvars_varclass_nb.
  apply select_in in H.
  rwsimplAll.
  split;[| tauto].
  repnd.
  eapply varsOfClassSubset;[| apply IHHe; auto].
  intros ? Hin.
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


Inductive L5Opid : Set :=
 | CLambda 
 | CKLambda
 | CFix (nMut : nat) (** number of functions that are mutually defined*)
 | CDCon (dc : dcon) (nargs : nat)
 | CHalt 
 | CRet (** application of a continuation lambda ([CKLambda]) *)
 | CCall (** a bit like apply in source language *)
 | CProj (selector :nat) (** which one to project out*)
 | CMatch (dconAndNumArgs : list (dcon * nat))
 (** each member of the list corresponds to a branch. 
    it says how many variables are bound in that branch*).

Definition CPSOpBindings (c : L5Opid) 
    : list nat :=
  match c with
  | CLambda    => [2] (* user lambda, also binds a continuation *)
  | CKLambda    => [1] (* continuation lambda  *)
  | CFix nMut => repeat 1 nMut
  | CDCon _ nargs    => repeat 0 nargs
  | CHalt => [0]
  | CRet => [0,0]
  | CCall => [0,0,0]
  | CProj _ => [0,0]
  | CMatch numargsInBranches => 0::(List.map snd numargsInBranches)
  end.


Definition cdecc: forall x y : L5Opid,
{x = y} + {x <> y}.
Proof using.
  repeat(decide equality).
Defined.


Definition CPSGenericTermSig : GenericTermSig :=
{| 
  Opid := L5Opid;
  OpBindings := CPSOpBindings;
  opid_dec := cdecc;
|}.


Notation CBTerm := (@terms.BTerm NVar CPSGenericTermSig).
Notation CTerm := (@terms.NTerm NVar CPSGenericTermSig).
Notation coterm := (@terms.oterm NVar CPSGenericTermSig).

Definition Lam_c (v vk : NVar) (b : CTerm) : CTerm :=
  coterm CLambda [bterm [v; vk] b].

Definition KLam_c (v : NVar) (b : CTerm) : CTerm :=
  coterm CKLambda [bterm [v] b].

Definition Ret_c (f a : CTerm) :=
  coterm CRet [bterm [] f , bterm [] a].

Definition Halt_c (v : CTerm) :=
  coterm CHalt [bterm [] v].

Definition Call_c (f k a : CTerm) :=
  coterm CCall [bterm [] f , bterm [] k , bterm [] a].

Definition Con_c (dc : dcon) (args : list CTerm) : CTerm :=
  coterm (CDCon dc (length args)) (List.map (bterm []) args).

Definition Proj_c (arg: CTerm) (selector : nat) (cont: CTerm)  : CTerm :=
  coterm (CProj selector) [bterm [] arg, bterm [] cont].

(** do we need a continuation variable as well? *)
Definition Fix_c (xf : NVar) (args : list CTerm) : CTerm :=
  coterm (CFix (length args)) (List.map (bterm [xf]) args).

Definition Fix_c' (lbt : list CBTerm) : CTerm :=
  coterm (CFix (length lbt)) lbt.

Definition Match_c (discriminee : CTerm) (brs : list branch) : CTerm :=
  coterm (CMatch (List.map (fun b => (fst b, num_bvars (snd b))) brs))
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
(*
 eval_Proj_c : forall lbt i k v' xf fn kv,  
(** [kv] must be disjoint from free variables of fn. add it to not break alpha equality *)  
                  select i lbt = Some (bterm [xf] (KLam_c kv (Ret_c (vterm kv) fn))) ->   
                  eval_c (Ret_c k (fn{xf:=Fix_c' lbt})) v' ->  
                  eval_c (Proj_c (Fix_c' lbt) i k) v'. *)

| eval_Proj_c : forall lbt i k v' xf fn, 
(* fn is a value, which will have a val_outer (defined below) in the intended usecase*)
                  select i lbt = Some (bterm [xf] fn) -> 
                  eval_c (Ret_c (fn{xf:=Fix_c' lbt}) k) v' ->
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
          (* expensive test. need memoization *)
        | NLambda => true
        | NFix _ => true
        | NDCon _ _ => ball (List.map (is_valueb ∘ get_nt) lb)
        | NApply => false
        | NProj _ => false
        | NLet => false
        | NMatch _ => false
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

(*
Lemma is_valueb_sound :
  (forall e,  is_valueb e = true -> nt_wf e-> is_value e).
Proof using.
  intros ? Hisv Hnt.
  destruct e; [constructor|].
  inverts Hnt as Hbt Hnb.
  destruct o;[destruct c | destruct n]; simpl in Hnb; try inverts Hisv.
- dnumvbars Hnb l. constructor. 
- Print is_value.

 econstructor. dnumvbars Hnb l. constructor. 
  induction H; auto. simpl. rewrite map_map.
  unfold compose. simpl. 
  rewrite ball_map_true. auto.
Qed.
*)
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
                    bterm vars (cps_cvt e)) es.

  Fixpoint cps_cvt_val' (e:NTerm) : CTerm :=
    match e with
      | vterm n => vterm n
      |   terms.oterm NLambda [bterm [x] b] => 
          cps_cvt_lambda x b
      | terms.oterm (NDCon d l) lb => 
          let fb := (fun b => 
                      bterm []
                            (cps_cvt_val' (get_nt b))) in
            coterm (CDCon d l) (List.map fb lb)
      | terms.oterm (NFix nargs) lb =>
          coterm (CFix nargs)
             (cps_cvt_fn_list' lb)
      | _ => coterm CLambda (map ((bterm []) ∘ vterm)  (free_vars e))
          (* ill-formed term, which will not arise from the prev. phase.
            This choice, which is also ill-formed,
            is just to ensure that the free variables are same as
            that of the the input *)
    end.

  Fixpoint cps_cvts_chain (vs: list NVar )(es:list BTerm) (c:CTerm) :  CTerm :=
    match es with
      | nil => c
      | (bterm _ e)::es =>
        match vs with
        | [] => Ret_c (cps_cvt e) (KLam_c nvarx (cps_cvts_chain [] es c)) (* impossible *)
        | kvh :: kvt => Ret_c (cps_cvt e) (KLam_c kvh (cps_cvts_chain kvt es c))
        end
    end.


  Definition cps_cvt_branch  (kv : CTerm) (bt: BTerm) : CBTerm :=
    match bt with
    | bterm vars nt =>
        (bterm vars (Ret_c (cps_cvt nt) kv))
    end.

 Definition cps_cvt_branches  (kv : CTerm) : (list BTerm) -> list CBTerm :=
  List.map (cps_cvt_branch kv).

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
    | terms.oterm NApply [bterm [] e1; bterm [] e2] => 
        cps_cvt_apply cps_cvt (cps_cvt e1) e2
    | terms.oterm (NDCon d nargs) es => 
        let kvars := contVars (S (length es)) in
        let k := hd nvarx kvars  in
        let tlkv := tail kvars  in
        KLam_c k (cps_cvts_chain cps_cvt tlkv es (Ret_c (vterm k)
                                                          (Con_c d (map vterm tlkv))))
    | terms.oterm (NMatch brl) ((bterm [] discriminee)::brr) => 
      let kvars := contVars 2 in 
      let k := nth 0 kvars nvarx in
      let kd := nth 1 kvars nvarx in
      let brrc :=  (bterm [] (vterm kd))::(cps_cvt_branches cps_cvt (vterm k) brr) in
      KLam_c k (Ret_c (cps_cvt discriminee)
                      (KLam_c kd (coterm (CMatch brl) brrc) ))


      (* translate as if it were App_e (Lam_e x e2) e1. See [cps_cvt_let_as_app_lam] below.
         Unlike the general cas of App, here the function is already a value *)
    | terms.oterm NLet [bterm [] e1, bterm [x] e2] => 
      let cpsLam := (val_outer (cps_cvt_lambda cps_cvt x e2)) in
        cps_cvt_apply cps_cvt cpsLam e1

    | terms.oterm (NProj i) [bterm [] e] =>
      let kvars := contVars  2 in 
      let k := nth 0 kvars nvarx in  
      let ke := nth 1 kvars nvarx in  
        KLam_c k (Ret_c (cps_cvt e) 
                        (KLam_c ke (Proj_c (vterm ke) i (vterm k))))
    | _ => coterm CLambda (map ((bterm []) ∘ vterm)  (free_vars e))
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
    apply ssubst_aux_trivial_disj.
    intros ? ? Hin. simpl in *. in_reasoning; inverts Hin.
    unfold closed in Hb. simpl in Hb.
    autorewrite with core list in Hb.
    rewrite nil_remove_nvars_iff in Hb.
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
    rewrite nil_remove_nvars_iff in Hb.
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
  autorewrite with list in *.
  varsOfClassSimpl.
  rewrite Hyp; [
    | eapply size_subterm3; eauto
    | ntwfauto
    | tauto
      ].
  apply proj2, userVarsContVar in Hin.
  refl.
Qed.


(* get rid of it. must not depend on the return value on ill formed cases.
cps_cvt_val will  never be called for non-values. So add is_value as a hypothesis*)
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
  destruct o; try illFormedCase;
    [clear Hind| clear Hind|]; inverts Hwf as Hbt Hnb;
    simpl in Hnb.
(* lambda case *)
- simpl.
  dnumvbars Hnb bt.
  erewrite <- cps_cvt_val_aux_fvars_aux; eauto.
  simpl. autorewrite with list SquiggleLazyEq.
  rewrite cons_as_app.
  rewrite <- remove_nvars_app_l, remove_nvars_app_r.
  autorewrite with list SquiggleLazyEq.
  setoid_rewrite remove_nvars_nop at 2; auto.
  rwsimpl Hs. pose proof Hs as Hsb. unfold all_vars in Hs. rwsimpl Hs.
  apply disjoint_sym. apply userVarsContVar. repnd.
  rewrite Hyp; simpl; auto; try omega.
  simpl in Hbt.
  dLin_hyp. inverts Hyp0.
  auto.
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

Lemma cps_cvt_constr_fvars_aux : forall lbt lkv c,
  (forall es, 
     (size es < S (addl (map size_bterm lbt)))
      -> nt_wf es 
      -> varsOfClass (all_vars es) USERVAR
      -> eq_set (free_vars (cps_cvt es)) (free_vars es))
  -> length lbt = length lkv 
  -> (forall b, LIn b lbt -> (bt_wf b /\ get_vars b = []))
    -> varsOfClass (flat_map all_vars_bt lbt) USERVAR
    -> disjoint lkv (flat_map all_vars_bt lbt)
    -> eq_set (free_vars (cps_cvts_chain cps_cvt lkv lbt c))
            ((flat_map free_vars_bterm lbt) ++ (remove_nvars  lkv (free_vars c))).
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
  destruct o; illFormedCase;
  inverts Hwf as Hbt Hnb; simpl in Hnb.
(** data constructor when not all subterms are values *)
  + 
    repeat progress (autorewrite with list allvarsSimpl in Hs; 
      simpl in Hs).
    addContVarsSpec (S (Datatypes.length lbt)) Hs kv.
    rename lvcvf into lkv. simpl.
    simpl. repnd.
    simpl in *.
    rewrite  cps_cvt_constr_fvars_aux; 
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
    unfold cps_cvt_branches.
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

Lemma cps_cvt_constr_fvars : forall lnt lkv c,
   length lnt = length lkv 
   -> lforall nt_wf lnt
   -> varsOfClass (flat_map all_vars lnt) USERVAR
   -> disjoint lkv (flat_map all_vars lnt)
   -> eq_set (free_vars (cps_cvts_chain cps_cvt lkv (map (bterm []) lnt) c))
            ((flat_map free_vars lnt) ++ (remove_nvars  lkv (free_vars c))).
Proof using.
  intros. rewrite cps_cvt_constr_fvars_aux; rwsimplC; auto.
- intros. apply cps_cvt_aux_fvars; auto.
- intros ? Hin. apply in_map_iff in Hin. exrepnd. subst. simpl.
  auto. 
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

Corollary cps_cvt_closed : forall e,
  nt_wf e
  -> varsOfClass (all_vars e) USERVAR 
  -> closed e
  -> closed (cps_cvt  e).
Proof using.
  intros ? ? Hwf Hcl.
  unfold closed in *.
  symmetry.
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
  symmetry.
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
  rewrite map_map.
  f_equal.
  apply eq_maps.
  intros bt Hin.
  destruct bt as [lv nt].
  unfold compose.
  simpl.
  eapply Hind; eauto.
Qed.


  
Ltac dnumvbars2 H lbt btt :=
  match type of H with
  | map num_bvars _ = _ :: _ =>
      let bt := fresh btt in
      let btlv := fresh bt "lv" in
      let btnt := fresh bt "nt" in
      let Hbt := fresh bt "H" in
      destruct lbt as [| bt lbt]; [ inverts H | inverts H as Hbt H ]; [  ]; destruct bt as (btlv, btnt);
       unfold num_bvars in Hbt; simpl in Hbt; dlist_len_name btlv btlv; try dnumvbars2 H lbt btt
  | map num_bvars _ = [] => destruct lbt; [ clear H | inverts H ]
  end.


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
  destruct c; split; intros H; inverts H; simpl; auto;
   try apply lam_is_value; try apply fix_is_value; try apply H.
  + apply (f_equal (map (@num_bvars _ _)) ) in H1. unfold num_bvars at 1 in H1.
    simpl in H1.
    symmetry in H1. 
    dnumvbars2 H1 lbt btt. constructor.    
  + apply (f_equal (map (@num_bvars _ _)) ) in H2. unfold num_bvars at 1 in H2.
    simpl in H2.
    symmetry in H1. 
    dnumvbars2 H1 lbt btt. constructor.    
      let bt := fresh btt in
      let btlv := fresh bt "lv" in
      let btnt := fresh bt "nt" in
      let Hbt := fresh bt "H" in
      destruct lbt as [| bt lbt]; [ inverts H | inverts H as Hbt H ]; [  ]; destruct bt as (btlv, btnt);
       unfold num_bvars in Hbt; simpl in Hbt; dlist_len_name btlv btlv.

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
  [ | destruct o; try (complete (inverts Hev)) ; inverts Hwf as Hbt Hnb; simpl in Hnb];
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
Proof using.
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
-> varsOfClass (dom_sub sub ++ flat_map all_vars (range sub)) USERVAR
->  forall lbt lkv c,
  (forall es, 
     (size es <  S (addl (map size_bterm lbt)))
      -> cps_ssubst_commutes es cps_cvt)
  -> length lbt = length lkv
  -> (forall b, LIn b lbt -> (bt_wf b /\ get_vars b = []))
    -> varsOfClass (flat_map all_vars_bt lbt) USERVAR 
    -> disjoint (lkv++free_vars c) (dom_sub sub)
   -> let sf := (map_sub_range (cps_cvt_val' cps_cvt) sub) in
     (ssubst_aux (cps_cvts_chain cps_cvt lkv lbt c)  sf)
       = cps_cvts_chain cps_cvt lkv  (map (fun t : BTerm => ssubst_bterm_aux t sub) lbt) 
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
              try (inverts Hd); simpl in Hnb] | assumption] ].
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

(* closedness assumptions can weakened *)
Lemma val_outer_eval : forall (v1 v2 k:CTerm) ,
closed v1
-> closed k
->
  (eval_c (Ret_c (val_outer v1) k ) v2 <->
   eval_c (Ret_c  k             v1) v2).
Proof using.
  intros ? ? ? Hcv Hck.
  unfold val_outer.
  rewrite eval_ret.
  simpl. unfold subst.
  rewrite ssubstRet_c.
  rewrite ssubst_vterm.
  simpl. rewrite <- beq_var_refl.
  rewrite ssubst_trivial2_cl; auto;[refl| intros; repeat (in_reasoning); cpx].
Qed.


Lemma cps_val_ret_flip : forall (v : NTerm) (k v2:CTerm) ,
  is_value v
  -> varsOfClass (all_vars v) USERVAR
  -> isprogram v
  -> closed k
  -> (eval_c (Ret_c (cps_cvt v) k) v2 <->
     eval_c (Ret_c  k (cps_cvt_val v)) v2).
Proof using.
  intros ? ? ? Hv Hc Hvc Hp.
  apply cps_val in Hv.
  rewrite Hv. clear Hv.
  apply val_outer_eval; auto.
  destruct Hvc.
  apply cps_cvt_val_closed; auto.
Qed.

Lemma val_outer_ssubst : forall t sub,
(flat_map free_vars (range sub)) = []
-> disjoint [contVar] (dom_sub sub)
-> ssubst (val_outer t) sub = val_outer (ssubst t sub).
Proof.
  intros ? ? H1dis H2dis.
  change_to_ssubst_aux8; try rewrite H1dis; auto.
  apply val_outer_ssubst_aux. auto.
Qed.


Ltac prepareForEvalRet Hc Hs :=
  match goal with
  [|- context [Ret_c (KLam_c ?v _) ?k]] => assert (closed k) as Hc;
    [|  assert (sub_range_sat [(v , k)] closed) as Hs by
        (intros ? ? ?; in_reasoning; cpx)]
  end.

Lemma cps_cvt_corr_app_let_common_part:
forall 
(x kv kv0 kv1 : NVar)
(e2 e1' v2 v : NTerm)
(k v' : CTerm)
(Hvc : varsOfClass (all_vars e2 ++ [x] ++ all_vars e1' ++ all_vars v2) USERVAR)
(He1 : eval e2 v2)
(He2 : eval (ssubst e1' [(x, v2)]) v)
(IHHe2 : forall k : CTerm,
        free_vars k = [] -> forall v' : CTerm, eval_c (Ret_c (cps_cvt e2) k) v' <-> eval_c (Ret_c (cps_cvt v2) k) v')
(Hcle : isprogram e2 /\ isprogram_bt (bterm [x] e1') /\ closed k /\ closed v2)
(Hvcnr : no_repeats [kv, kv0, kv1])
(Hcvdis : disjoint [contVar, kv, kv0, kv1] (all_vars e2 ++ x :: all_vars e1')) 
(Hcsss : (closed (KLam_c kv0 (Ret_c (cps_cvt e2) (KLam_c kv1 (Call_c (vterm kv0) k (vterm kv1))))))),
eval_c
  (Ret_c (val_outer (cps_cvt_lambda cps_cvt x e1'))
     (KLam_c kv0 (Ret_c (cps_cvt e2) (KLam_c kv1 (Call_c (vterm kv0) k (vterm kv1)))))) v' <->
eval_c (Ret_c (cps_cvt (ssubst e1' [(x, v2)])) k) v'.
Proof using.
  intros. unfold isprogram, isprogram_bt, closed, closed_bt in *. repnd.
  rwsimpl Hvc. simpl in *.
  unfold  val_outer, cps_cvt_lambda.
  rewrite eval_ret. simpl.
  unfold subst.
  rewrite ssubstRet_c by assumption.
  rewrite ssubst_vterm. simpl ssubst_aux.
  progress autorewrite with SquiggleLazyEq.
  match goal with
  [|- context [Ret_c _ (ssubst ?k _)]] => assert (closed k) as Hclk;
    [|  assert (sub_range_sat [(kv0 , k)] closed) as Hcs by
        (intros ? ? ?; in_reasoning; cpx)]
  end.
    unfold closed. simpl. autorewrite with list core SquiggleLazyEq.
    symmetry.
    rewrite cps_cvt_aux_fvars;
      [| apply' eval_preseves_wf He1; ntwfauto; fail
       | try tauto].
    rewrite remove_nvars_app_r.
    rewrite cons_as_app.
    repeat rewrite <- remove_nvars_app_l.
    autorewrite with SquiggleLazyEq.
    rewrite remove_nvars_comm. rwHyps. refl.

  rewrite substLam_cTrivial2 by assumption.
  rewrite eval_ret. simpl.
  unfold subst.
  rewrite ssubstRet_c by assumption.
  rewrite ssubstKlam_c; [| try assumption| noRepDis].
  rewrite ssubstCall_c by assumption.
  do 2 rewrite ssubst_vterm. simpl.
  rewrite <- beq_var_refl.
  rewrite not_eq_beq_var_false;[| noRepDis].
  rewrite ssubst_trivial2_cl;[| assumption | 
      symmetry; rewrite cps_cvt_aux_fvars; [ rwHyps; refl | ntwfauto| tauto]].
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
    
    simpl.
    autorewrite with list core SquiggleLazyEq using rwHyps. refl.
    rwHyps. rwsimplC. autorewrite with list core SquiggleLazyEq.
  clear Hcs.
  rewrite IHHe2 by assumption. clear IHHe2.
  rewrite cps_val_ret_flip; auto;[|eauto using eval_yields_value'| tauto | split; auto; 
      eauto using eval_preseves_wf].
  rewrite eval_ret.
  simpl. unfold subst.
  rewrite ssubstCall_c by assumption.
  rewrite ssubst_vterm. simpl ssubst_aux.
  rewrite <- beq_var_refl.
  pose proof Hcle as Hcleb.
  apply cps_cvt_val_closed in Hcle; eauto using eval_preseves_wf; try tauto.
  unfold closed in Hcle.
  do 2 (rewrite ssubst_trivial2_cl;[|intros; repeat in_reasoning; cpx | 
    assumption
      ]).
  rewrite eval_call.
  rewrite ssubstRet_c. repnd.
  rewrite <- ssubst_sub_filter2 with (l:=[contVar]).
  Focus 3. 
    rewrite cps_cvt_aux_fvars;
       [disjoint_reasoningv2
         |(apply' eval_preseves_wf He1; 
                      ntwfauto) 
        | assumption]; fail.

  Focus 2. unfold disjoint_bv_sub. unfold cps_cvt_val.
     intros ? ? Hin. 
     repeat in_reasoning; inverts Hin;
     rwHyps; auto.
     
  rewrite ssubst_vterm. simpl.
  autorewrite with SquiggleLazyEq.
  rewrite not_eq_beq_var_false;[| apply disjoint_neq; disjoint_reasoningv2].
  rewrite <- (eval_c_ssubst_commute);[refl
     | apply' eval_preseves_wf He1; 
                      ntwfauto; eauto using eval_preseves_wf
     | | | | rwsimplC; try tauto ]; 
    intros ? ? Hin; rewrite in_single_iff in Hin;
    inverts Hin; subst;auto;
        [eapply eval_yields_value'; eauto
        | ntwfauto; eauto using eval_preseves_wf].
Qed.


Lemma eval_vals_r:   forall es vs
(H : Datatypes.length es = Datatypes.length vs)
(H0 : forall e v : NTerm, LIn (e, v) (combine es vs) -> eval e v),
 ball (map (is_valueb ∘ get_nt) (map (bterm []) vs)) = true.
Proof using.
  intros.
  apply ball_map_true.
  intros ? Hin.
  rewrite (combine_map_snd es vs) in Hin by assumption.
  rewrite map_map in Hin.
  apply in_map_iff in Hin. exrepnd.
  unfold compose. inverts Hin1.
  simpl.
  apply is_valueb_corr.
  eapply eval_yields_value'; eauto.
Qed.


    
Lemma eval_valueb_noop : forall a b,
  eval a b
  -> is_valueb a = true
  -> a= b.
Proof using.
  intros ? ? He Hv.
  induction He; inverts Hv; auto.
  f_equal.
  apply combineeq;[assumption|].
  intros ? ? Hin.
  apply H1; auto.
  rewrite map_map in H3.
  rewrite ball_map_true in H3.
  rewrite (combine_map_fst es vs) in H3; auto. 
  unfold compose in H3. simpl in H3.
  apply H3. apply in_map_iff. eexists; split; simpl; eauto.
  refl.
Qed.
     
Lemma eval_vals_l:   forall es vs
(H : Datatypes.length es = Datatypes.length vs)
(H0 : forall e v : NTerm, LIn (e, v) (combine es vs) -> eval e v),
ball (map (is_valueb ∘ get_nt) (map (bterm []) es)) = true
-> es=vs.
Proof using.
  intros ? ? ? ? Hb.
  eapply eval_Con_e with (d:=0%N) in H0; eauto.
  apply eval_valueb_noop in H0;[| assumption].
  inverts H0.
  apply map_eq_injective in H3; auto.
  intros ? ? ?. congruence.
Qed.







Lemma ssubst_aux_cps_cvts' : forall (lbt : list BTerm) lkv  (c: CTerm) sub,
lforall bt_wf lbt
-> varsOfClass (flat_map all_vars_bt lbt) USERVAR
-> length lkv = length lbt
-> disjoint (lkv ++ flat_map all_vars_bt lbt) (dom_sub sub)
-> ssubst_aux (cps_cvts_chain cps_cvt lkv lbt c) sub
=           cps_cvts_chain cps_cvt lkv  lbt (ssubst_aux c sub).
Proof using.
  simpl.
  induction lbt as [| b lbt Hind]; auto;[]; intros ? ? ? Hwf Hvc Hl Hd.
  simpl. destruct b as [lb nt].
  destruct lkv; simpl in *; inverts Hl.
  unfold Ret_c, KLam_c.
  autorewrite with SquiggleLazyEq.
  unfold lforall in Hwf. simpl in *.
  dLin_hyp. ntwfauto.
  rwsimpl Hvc.
  autorewrite with SquiggleLazyEq in Hd.
  rwsimpl Hd.
  rewrite ssubst_aux_trivial_disj;
      [auto 
        | disjoint_reasoningv2;[]; rewrite cps_cvt_aux_fvars; auto].
  Focus 2. rwsimplAll. disjoint_reasoningv.
  repeat f_equal.
  rewrite sub_filter_disjoint1;[|disjoint_reasoningv2].
  apply Hind; auto;[tauto|].
  disjoint_reasoningv.
Qed.



  
(** Useful for rewriting. *)
Lemma eval_match :
  forall d vs bs v' c,
    find_branch d ((List.length vs)) bs = Some c -> 
    (eval_c (Match_c (Con_c d vs) bs) v' <-> eval_c (apply_bterm c vs) v').
Proof using.
  intros ? ? ? ? ? Hf; split ; intros;[| econstructor; eauto].
  inverts H. apply map_eq_injective in H4; [| intros ? ? ?; congruence].
  eapply list_pair_ext in H5; eauto;[subst; congruence|].
  apply (f_equal (map fst)) in H0.
  do 2 rewrite map_map in H0.
  simpl in H0.
  apply H0.
Qed.

Lemma eval_matchg :
  forall d vs lbt ld v' c len,
    find_branch d (length vs) (combine (map fst ld) lbt) = Some c -> 
    map num_bvars lbt = map snd ld -> 
    length vs = len -> 
    let o :=  (CMatch ld) in
    let cc :=  coterm (CDCon d len) (map (bterm []) vs) in
    (eval_c (coterm o ((bterm [] cc)::lbt)) v' <-> eval_c (apply_bterm c vs) v').
Proof using.
  intros ? ? ? ? ? ? ? Hf Hm Hl.
  simpl.
  rewrite <- eval_match;[| apply Hf].
  unfold Match_c, Con_c.
  apply eq_subrelation;[eauto with typeclass_instances|].
  pose proof Hm as Hmb. subst.
  apply (f_equal (@length _)) in Hmb.
  autorewrite with list in *.
  do 4 f_equal;[|].
- apply list_pair_ext;
  rewrite map_map; simpl;[|].
  + rewrite <- combine_map_fst;
    autorewrite with list; auto.
  + symmetry. rewrite <- map_map.
    rewrite <- combine_map_snd;
    autorewrite with list; auto.
- rewrite <- combine_map_snd;
  autorewrite with list in *; auto.
Qed.

Lemma eval_proj :
  forall (lbt : list CBTerm) (i : nat) (k v' : CTerm) (xf: NVar) (fn : CTerm) len,
    select i lbt = Some (bterm [xf] fn) ->
    len = length lbt ->
  let Fix := coterm (CFix len) lbt in
  eval_c (Proj_c Fix i k) v' <-> eval_c (Ret_c (fn {xf := Fix}) k) v'.
Proof using.
  intros ?  ? ? ? ? ? ? Hf Hl; simpl; subst; split ; intros;[| econstructor; eauto].
  inverts H. simpl in *. unfold Fix_c', subst in *. congruence. 
Qed.


Lemma cps_cvt_branch_subst_aux: forall (kv : CTerm) (bt : BTerm) sub,
  isprogram_bt bt
  -> varsOfClass (all_vars_bt bt) USERVAR
  -> sub_range_sat sub closed
  -> disjoint (dom_sub sub) (all_vars_bt bt)
  -> ssubst_bterm_aux (cps_cvt_branch cps_cvt kv bt) sub
      = (cps_cvt_branch cps_cvt (ssubst_aux kv sub) bt).
Proof using.
  intros ? ? ? Hb Hu Hs Hd.
  destruct bt as [lv nt].
  simpl.
  f_equal.
  unfold Ret_c.
  rwsimplAll.
  rewrite sub_filter_disjoint1 at 2;[| disjoint_reasoningv].
  repeat f_equal.
  apply ssubst_aux_trivial_disj.
  rewrite <- dom_sub_sub_filter.
  destruct Hb.
  rewrite cps_cvt_aux_fvars;[| ntwfauto| tauto].
  unfold closed_bt in H.
  simpl in H.
  apply disjoint_remove_nvars_l.
  rwHyps.
  auto.
Qed.

Lemma cps_cvt_branch_subst: forall (kv : CTerm) (bt : BTerm) sub,
  isprogram_bt bt
  -> varsOfClass (all_vars_bt bt) USERVAR
  -> sub_range_sat sub closed
  -> disjoint (dom_sub sub) (all_vars_bt bt)
  -> ssubst_bterm (cps_cvt_branch cps_cvt kv bt) sub
      = (cps_cvt_branch cps_cvt (ssubst kv sub) bt).
Proof using.
  intros.
  change_to_ssubst_aux8.
  rewrite (snd ssubst_ssubst_aux_nb).
  - apply cps_cvt_branch_subst_aux; auto.
  - change_to_ssubst_aux8. auto.
Qed.

Lemma cps_cvt_branch_fvars: forall (kv : CTerm) (bt : BTerm),
  disjoint (free_vars kv) (get_vars bt)
  -> isprogram_bt bt
  -> varsOfClass (all_vars_bt bt) USERVAR
  -> eq_set
        (free_vars_bterm (cps_cvt_branch cps_cvt kv bt))
        (free_vars_bterm bt ++ free_vars kv).
Proof using.
  intros ? ? Hd Hp hv.
  destruct bt as [lv nt].
  simpl.
  rwsimplAll.
  destruct Hp.
  rewrite cps_cvt_aux_fvars;[| ntwfauto| tauto].
  rewrite remove_nvars_app_r.
  f_equiv.
  rewrite remove_nvars_nop; auto.
Qed.

Lemma cps_cvt_branches_subst: forall (kv : CTerm) (lbt : list BTerm) sub,
  lforall bt_wf lbt
  -> (flat_map free_vars_bterm lbt=[])
  -> varsOfClass (flat_map all_vars_bt lbt) USERVAR
  -> sub_range_sat sub closed
  -> disjoint (dom_sub sub) (flat_map all_vars_bt lbt)
  -> map (fun t => ssubst_bterm t sub) (cps_cvt_branches cps_cvt kv lbt)
      = (cps_cvt_branches cps_cvt (ssubst kv sub) lbt).
Proof using.
  intros ? ? ? Hef hf Hvc Hsr Hd.
  unfold cps_cvt_branches.
  rewrite map_map.
  apply eq_maps.
  intros ? Hin.
  rewrite disjoint_flat_map_r in Hd.
  rewrite flat_map_empty in hf.
  apply cps_cvt_branch_subst; eauto with subset.
  split; unfold closed_bt; eauto.
Qed.


Lemma cps_cvt_branches_fvars: forall (kv : CTerm) (lbt : list BTerm),
  disjoint (free_vars kv) (flat_map get_vars lbt)
  -> lforall bt_wf lbt
  -> (flat_map free_vars_bterm lbt=[])
  -> varsOfClass (flat_map all_vars_bt lbt) USERVAR
  -> eq_set
        (flat_map free_vars_bterm (cps_cvt_branches cps_cvt kv lbt))
        (flat_map free_vars_bterm lbt ++ flat_map (fun _ => (free_vars kv)) lbt).
Proof using.
  intros ? ? Hd Hw Hc hv.
  unfold cps_cvt_branches.
  rewrite flat_map_map.
  rewrite disjoint_flat_map_r in Hd.
  rewrite flat_map_empty in Hc.
  erewrite eqset_flat_maps.
  Focus 2.
    intros. apply cps_cvt_branch_fvars; eauto with subset.
    split; unfold closed_bt; eauto.
  rewrite flat_map_fapp.
  refl.
Qed.

Lemma eval_c_constr_move_in : forall k d v' es vs ws lkv
(Hl: Datatypes.length vs = Datatypes.length es)
(Hlv: Datatypes.length es = Datatypes.length lkv)
(Hev : forall e v : NTerm, LIn (e, v) (combine es vs) -> eval e v)
(Hind: forall e v : NTerm,
       LIn (e, v) (combine es vs) ->
       forall k : CTerm,
       closed k -> forall v' : CTerm, eval_c (Ret_c (cps_cvt e) k) v' <-> eval_c (Ret_c (cps_cvt v) k) v')
(Hcws : (flat_map free_vars es)++(flat_map free_vars ws) = [])
(Hclkk : closed k)
(Hwf :  lforall nt_wf  es)
(Hvc : varsOfClass (flat_map all_vars es) USERVAR)
(Hdis : disjoint lkv (flat_map all_vars es))
(Hnr : no_repeats lkv)
,
eval_c
  (cps_cvts_chain cps_cvt lkv (map (bterm []) es)
            (Ret_c k (Con_c d (ws ++ (map vterm lkv)) ) ) ) v' <->
eval_c
  (Ret_c k
     (Con_c d 
        (ws ++ (map cps_cvt_val vs)) ) ) v'.
Proof using.
  induction es; intros ; simpl in *; dlist_len_name vs v; dlist_len_name lkv kv; [refl|].
  simpl.
  simpl in *.
  dLin_hyp.
  simpl in *.
  repeat rewrite app_eq_nil_iff in Hcws. repnd.
  rewrite cons_as_app in Hwf.
  apply lforallApp in Hwf. repnd.
  rwsimpl Hvc. repnd.
  match goal with
  [|- context [Ret_c _ ?k]] => assert (closed k) as Hclk;
    [|  assert (sub_range_sat [(contVar , k)] closed) as Hcs by
        (intros ? ? ?; in_reasoning; cpx)]
  end.
    unfold closed. simpl. autorewrite with list.
    symmetry.
    rewrite cps_cvt_constr_fvars; rwHyps; auto;[| disjoint_reasoningv2; fail].
    simpl. rwHyps. simpl. rwsimplC. rewrite flat_map_app. rwHyps.
    simpl. setoid_rewrite cons_as_app at 2. rewrite remove_nvars_app_r.
    rwsimplC. rewrite remove_nvars_comm. rwsimplC. refl.

  rewrite Hyp by (simpl; auto).
  unfold lforall in Hwf0. simpl in Hwf0.
  dLin_hyp.
  rewrite cps_val_ret_flip;[| | | split|]; try  unfold isprogram; eauto using eval_yields_value', 
    eval_preseves_varclass, eval_preseves_wf,eval_preserves_closed;[].
  rewrite eval_ret.
  simpl. unfold subst.
  assert (closed (cps_cvt_val v)) by (apply cps_cvt_val_closed; eauto using eval_yields_value', 
    eval_preseves_varclass, eval_preseves_wf,eval_preserves_closed).
  unfold closed in *.
  change_to_ssubst_aux8;[ |simpl; rwHyps; simpl; auto].
  Hint Rewrite @list_nil_btwf : SquiggleLazyEq.
  rewrite ssubst_aux_cps_cvts'; simpl; autorewrite with list; auto; unfold lforall; rwsimplC; auto;
    [| noRepDis2].
  autorewrite with SquiggleLazyEq. simpl.
  rewrite map_map.
  unfold compose. simpl.
  autorewrite with SquiggleLazyEq.
  do 2 rewrite <- snoc_append_r.
  do 2 rewrite snoc_as_append.
  do 2 rewrite map_app.
  rewrite map_ssubst_aux; simpl; rwHyps; auto.
  rewrite map_ssubst_aux;[| rwsimplC; noRepDis2].
  rewrite ssubst_aux_trivial_disj;[|rwHyps; auto].
  autorewrite with SquiggleLazyEq.
  change ([bterm [] (cps_cvt_val v)]) with (map (bterm []) [cps_cvt_val v]).
  rewrite <- map_app.
  Hint Rewrite @flat_map_app : SquiggleLazyEq.
  rewrite <- IHes with (lkv:=lkv); simpl; rwsimplC; rwHyps; try noRepDis2.
  unfold Con_c.
  rewrite length_app.
  rewrite length_app.
  simpl. rewrite plus_assoc_reverse.
  simpl.
  rewrite <- map_app.
  rwsimplC.
  refl.
Qed.

Ltac apply' H1 H2 :=
  let H3 := fresh in
  (pose proof (H1 H2) as H3; clear H2; pose proof H3 as H2; clear H3) ||
  (pose proof (H1 _ H2) as H3; clear H2; pose proof H3 as H2; clear H3) ||
  (pose proof (H1 _ _ H2) as H3; clear H2; pose proof H3 as H2; clear H3) ||
  (pose proof (H1 _ _ _ H2) as H3; clear H2; pose proof H3 as H2; clear H3) ||
  (pose proof (H1 _ _ _ _ H2) as H3; clear H2; pose proof H3 as H2; clear H3) ||
  (pose proof (H1 _ _ _ _ _ H2) as H3; clear H2; pose proof H3 as H2; clear H3) ||
  (pose proof (H1 _ _ _ _ _ _ H2) as H3; clear H2; pose proof H3 as H2; clear H3) ||
  (pose proof (H1 _ _ _ _ _ _ _ H2) as H3; clear H2; pose proof H3 as H2; clear H3) ||
  (pose proof (H1 _ _ _ _ _ _ _ _ H2) as H3; clear H2; pose proof H3 as H2; clear H3) ||
  (pose proof (H1 _ _ _ _ _ _ _ _ _ H2) as H3; clear H2; pose proof H3 as H2; clear H3) ||
  (pose proof (H1 _ _ _ _ _ _ _ _ _ _ H2) as H3; clear H2; pose proof H3 as H2; clear H3).


Ltac unfoldSubst :=
  unfold ssubst; simpl;
  fold (@ssubst NVar _ _ _ CPSGenericTermSig);
  fold (@ssubst_bterm NVar _ _ _ CPSGenericTermSig);
  fold (@ssubst NVar _ _ _ CoqL4GenericTermSig);
  fold (@ssubst_bterm NVar _ _ _ CoqL4GenericTermSig).

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
  pose proof He1 as He1wf.
  apply' eval_preseves_wf He1wf.
  dimp He1wf;clear He1wf;[ ntwfauto|]. rename hyp into He1wf.
  specialize (IHHe1 ltac:(ntwfauto) Hvc0  Hcle0).
  specialize (IHHe2 ltac:(ntwfauto) Hvc Hcle).
  specialize (IHHe3 ltac:(ntwfauto; eauto using eval_preseves_wf)).
  (* IHHe3 needs more work : 2 more hyps *)
  applydup (eval_preseves_varclass USERVAR) in He1 as Hvs1;[| assumption].
  applydup (eval_preseves_varclass USERVAR) in He2 as Hvs2;[| assumption].
  unfold Lam_e in Hvs1.
  rwsimpl Hvs1. repnd.
  dest_imp IHHe3 HH;[apply ssubst_allvars_varclass_nb;  rwsimplC; try tauto|].

  (* IHHe3 has 1 more hyp *)
  applydup eval_preserves_closed in He1 as Hss;[| assumption].
  applydup eval_preserves_closed in He2 as Hss2;[| assumption].
  unfold subst, closed in *. simpl in *. autorewrite with list in *.
  setoid_rewrite fvars_ssubst1 in IHHe3;[| intros; repeat in_reasoning; cpx].
  dest_imp IHHe3 HH.

  rewrite <- IHHe3;[| assumption]. clear IHHe3.

  (* now, work on simplifying LHS slowly until it becomes equal to rhs *)
  (* first, e1 will be evaluated to a lambda *) 
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
  do 2 (rewrite not_eq_beq_var_false;[| noRepDis]).
  do 2 (rewrite ssubst_trivial2_cl;[|assumption|];
          [| unfold closed; symmetry;rewrite cps_cvt_aux_fvars; [| ntwfauto|]; 
           try rewrite Hcle0 ; try rewrite Hcle ; [ tauto | eauto ] ] ).

  clear Hcs.
  match goal with
  [|- context [Ret_c _ ?k]] => assert (closed k) as Hclk
  end.
    unfold closed. simpl. autorewrite with list core SquiggleLazyEq SquiggleLazyEq2.
    symmetry.
    rewrite cps_cvt_aux_fvars;[| ntwfauto|]; try rewrite Hcle; [  | eauto ].
    simpl. rewrite Hcl.
    rewrite remove_nvars_nops;[| noRepDis].
    autorewrite with SquiggleLazyEq. refl.

  rewrite IHHe1; [| assumption]. 
  simpl. clear IHHe1.
  eapply cps_cvt_corr_app_let_common_part; unfold isprogram, isprogram_bt; dands; eauto;
    rwsimplC; try tauto; try ntwfauto.

  apply userVarsContVar in Hvc.
  applydup userVarsContVar in Hvs1.
  applydup userVarsContVar in Hvs0.
  apply userVarsContVars with (n:=3) in Hvs1.
  apply userVarsContVars with (n:=3) in Hvs0.
  rewrite <- Heqlvcvf in Hvs0, Hvs1.
  rewrite cons_as_app.
  remember ([kv, kv0, kv1]) as cv. clear Heqcv Heqlvcvf.
  noRepDis.

(* reduction inside constructor : eval_Con_e *)
- intros Hcle ? Hcl ?. rename H0 into Hev. rename H1 into Hind.
  Local Opaque cps_cvt_val'.
  unfold Con_e in *. simpl in *.
  rewrite (eval_vals_r es vs) by assumption.
  cases_if;
    [apply eval_vals_l in Hev; eauto;inverts Hev; refl |].
  (* now we are left with the case where not all subterms of the constructor are values *)
  pose proof Hev as Hevv.
  apply eval_Con_e with (d:=d) in Hevv;[| assumption].
  applydup eval_preserves_closed in Hevv as Hevvc;[| assumption].
  applydup eval_preseves_wf in Hevv as Hevvw;[| assumption].
  applydup (eval_preseves_varclass USERVAR) in Hevv as Hevvvc;[| assumption].
  applydup cps_cvt_val_closed in Hevvc as Hevcc; [| try assumption |try assumption].
  clear Hevv Hevvc Hevvw Hevvvc.
  rwsimplAll.
  addContVarsSpec (S (length es)) Hvc kv.
  simpl in *.
  unfold val_outer.
  do 2 rewrite eval_ret.
  simpl. unfold subst.
  rewrite ssubstRet_c.
  rewrite ssubst_vterm. simpl. rewrite <- beq_var_refl.
  symmetry. symmetry in H.
  rewrite ssubst_trivial2_cl;[ | intros; repeat (in_reasoning); cpx| assumption].
  change_to_ssubst_aux8;[| simpl; rwHyps; simpl; auto].
  remember (Con_c d (map vterm lvcvf)) as c.
  rewrite ssubst_aux_cps_cvts'; simpl; autorewrite with list; auto;
    [ | inverts Hwf; assumption | rwsimplC; try tauto| noRepDis2].
  rwsimplC.
  subst c.
  rewrite ssubst_aux_trivial_disj;[| rwsimplC; noRepDis2].
  Local Transparent cps_cvt_val'.
  simpl. rewrite map_map.
  unfold closed in *.
  rwsimpl Hcle.
  symmetry.
  ntwfauto. clear HntwfSig.
  rwsimpl Hntwf.
  rewrite (eval_c_constr_move_in k d v' es vs nil); auto;
    [unfold Con_c; rwsimplC; rewrite map_map;refl
      | | rwsimplC; auto | noRepDis2 | noRepDis2].
  intros ? ? Hinn.
  applydup in_combine_l in Hinn.
  rewrite flat_map_empty in Hcle.
  apply Hind; auto;[].
  eapply varsOfClassSubset;[| apply Hvc].
  apply subset_flat_map_r. auto.

(* eval_Let_e *)
- intros Hcle ? Hcl ?.
   unfold Let_e in *. simpl.
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
  applydup userVarsContVar in Hvc as Hvcdiss.
  autorewrite with SquiggleLazyEq in *. repnd.
  specialize (IHHe1 ltac:(ntwfauto) Hvc0  Hcle0).
  specialize (IHHe2 ltac:(apply' eval_preseves_wf He1; 
                      ntwfauto; eauto using eval_preseves_wf)).
  (* IHHe3 needs more work : 2 more hyps *)
  applydup (eval_preseves_varclass USERVAR) in He1 as Hvs1;[| assumption].
  rewrite cons_as_app in Hvc.
  rwsimpl Hvc.
  dest_imp IHHe2 HH;[apply ssubst_allvars_varclass_nb;  rwsimplC; tauto|].

  rename e2 into e1'.
  rename IHHe2 into IHHe3.
  applydup eval_preserves_closed in He1 as Hss;[| assumption].
  unfold subst, closed in *. simpl in *. autorewrite with list in *.
  setoid_rewrite fvars_ssubst1 in IHHe3;[| intros; repeat in_reasoning; cpx].
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
  do 3 rewrite ssubst_vterm. simpl ssubst_aux.
  rewrite <- beq_var_refl.
  do 2 (rewrite not_eq_beq_var_false;[| noRepDis]).
  change (val_outer (cps_cvt_lambda cps_cvt x e1')) with
            (cps_cvt (Lam_e x e1')).
  (rewrite ssubst_trivial2_cl;[|assumption|];
          [| unfold closed, Lam_e in * ; symmetry;
               rewrite cps_cvt_aux_fvars; simpl; [lcongruence | ntwfauto| rwsimplAll; tauto] ] ).
  (rewrite ssubst_trivial2_cl;[|assumption|];
          [| unfold closed in *; symmetry;rewrite cps_cvt_aux_fvars; [congruence | ntwfauto| tauto]] ).

  eapply cps_cvt_corr_app_let_common_part; unfold isprogram, isprogram_bt; dands; eauto;
    rwsimplC; try tauto; try ntwfauto;
    [rewrite cons_as_app; rewrite disjoint_app_l; split;tauto|].
  
  unfold closed. simpl. autorewrite with core list SquiggleLazyEq using rwHyps.
  symmetry. rewrite cps_cvt_aux_fvars; simpl; auto.
  rwHyps. simpl. rewrite remove_nvars_app_l. 
  simpl. autorewrite with SquiggleLazyEq. refl.

(* eval_Match_e *)

- intros Hcle ? Hcl ?.
  unfold Match_e in *.
  remember (Con_e d vs) as con.
  simpl in *.
(*  applydup userVarsContVar in Hvc as Hvcdiss. *)
  addContVarsSpec 2 Hvc kv.
  rwsimpl Hvc.
  rwsimpl Hcvdis.
(*  rwsimpl Hvcdiss. *)
  simpl.
  (* now lets fulfil the assumptions in the induction hypotheses *)
  unfold closed in *.
  rwsimpl Hcle.
  apply app_eq_nil in Hcle. repnd.
  specialize (IHHe1 ltac:(ntwfauto) Hvc0  Hcle0).
  apply find_branch_some in H as H. rename H into Hfr.

  unfold num_bvars in Hfr.
  destruct e' as [blv bnt].
  simpl in Hfr.
  repnd.
  assert (nt_wf e) as Hwfe by  ntwfauto.
  assert (nt_wf bnt) as Hwfbnt by ntwfauto.
  applydup eval_preseves_wf in He1 as Hcwf;[| assumption].
  applydup (eval_preseves_varclass USERVAR) in He1 as Hcvc;[| ntwfauto].
  applydup (eval_preserves_closed) in He1 as Hc;[| ntwfauto].
  pose proof Hcle as Hcleb.
  rewrite flat_map_empty in Hcleb.
  subst.
  unfold Con_e in Hcvc.
  rwsimpl Hcvc.
  unfold Con_e, closed in Hc. simpl in Hc.
  rwsimpl Hc.
  dimp IHHe2.
    apply ssubst_wf_iff;[| auto].
    apply sub_range_sat_range.
    rewrite dom_range_combine by assumption.
    ntwfauto. autorewrite with SquiggleLazyEq in Hntwf. assumption.
  rename hyp into Hwfs. specialize (IHHe2 Hwfs).
  
  dimp IHHe2.
    apply ssubst_allvars_varclass_nb. simpl.
    rewrite dom_range_combine by assumption.
    rwsimplC. split; eauto with subset.
  rename hyp into Hvcs. specialize (IHHe2 Hvcs).

  dimp IHHe2.
    apply closed_bt_implies; [ apply Hcleb; assumption 
                              | apply flat_map_empty ; auto 
                              | unfold num_bvars; simpl; omega].
  rename hyp into Hcss. specialize (IHHe2 Hcss).

  rewrite <- IHHe2;[| assumption]. clear IHHe2.
  rewrite eval_ret.
  simpl. unfold subst. 
  assert (sub_range_sat [(kv, k)] closed) as Hcs by
    (intros ? ? ?; in_reasoning; cpx).
  rewrite ssubstRet_c.
  rewrite ssubstKlam_c; [| try assumption| noRepDis].
  unfoldSubst.
  fold (@ssubst NVar _ _ _ CPSGenericTermSig).
  fold (@ssubst_bterm NVar _ _ _ CPSGenericTermSig).
  rewrite ssubst_trivial2_cl;[|assumption| unfold closed; apply cps_cvt_closed; auto].
  (rewrite not_eq_beq_var_false;[| noRepDis]).
  inverts Hwf as Hwfb Hwfs. simpl in Hwfb. dLin_hyp.
  rewrite cps_cvt_branches_subst; simpl; auto;[| disjoint_reasoningv2].
  rewrite <- beq_var_refl.
  clear Hcs.
  match goal with
  [|- context [Ret_c _ ?k]] => assert (closed k) as Hclk;
    [|  assert (sub_range_sat [(contVar , k)] closed) as Hcs by
        (intros ? ? ?; in_reasoning; cpx)]
  end.
  
    unfold closed. simpl. autorewrite with list core SquiggleLazyEq SquiggleLazyEq2.
    simpl. symmetry.
    rewrite cps_cvt_branches_fvars; simpl; rwHyps; auto.
    rewrite repeat_nil. refl.

  rewrite IHHe1 by assumption.
  let tac :=auto;unfold Con_e; unfold isprogram, closed; rwsimplC;auto in
  rewrite cps_val_ret_flip; [|  eauto using eval_yields_value'| tac | tac | tac].

  prepareForEvalRet Hclkk Hcsss.

    let tac := unfold Con_e, closed; rwsimplC;auto in
      apply cps_cvt_val_closed; [assumption | tac | tac].
  
  rewrite eval_ret.
  Local Opaque cps_cvt_val. simpl. unfold subst.
  unfoldSubst.
  rewrite <- beq_var_refl.
  rewrite cps_cvt_branches_subst; simpl; auto;[| disjoint_reasoningv2].
  rewrite ssubst_trivial2_cl by assumption.
  Local Transparent cps_cvt_val. simpl.
  rewrite <- map_map.
  unfold cps_cvt_branches.
  rewrite eval_matchg; rwsimplC; auto.
  Focus 3.
    repeat rewrite map_map.
    apply eq_maps.
    intros ? _. destruct (snd x); refl; fail.

  Focus 2.
    repeat rewrite map_map. simpl.
    rewrite combine_map.
    unfold find_branch.
    erewrite find_map_same_compose;[ simpl; refl | | apply Hfr].
    intros. unfold compose. simpl. destruct (snd a). refl.
    
  unfold apply_bterm. simpl.
  unfold ssubst at 1. simpl.
  fold (@ssubst _ _ _ _ CPSGenericTermSig).
  apply eq_subrelation;[auto with typeclass_instances|].
  repeat rewrite map_map.
  unfold Ret_c.
  unfold closed in Hclkk.
  simpl in Hclkk.
  repeat rewrite map_map in Hclkk.
  rewrite flat_map_map in Hclkk. unfold compose in Hclkk. simpl in Hclkk.
  symmetry in Hclkk.
  erewrite eq_flat_maps in Hclkk;[| intros; apply remove_nvars_nil_l].
  simpl.
  repeat f_equal.
  Focus 2.
    apply ssubst_trivial2_cl; auto.
    apply sub_range_sat_range.
    rewrite dom_range_combine;[| rwsimplC; auto].
    setoid_rewrite <- flat_map_empty.
    rewrite flat_map_map.
    auto.

  clear Hclkk Hcss Hvcs.
  apply eval_yields_value' in He1.  inverts He1 as He1 _ Hmm.
  apply map_eq_injective in Hmm;[| intros ? ? ?; congruence]. subst.
  rewrite <- map_sub_range_combine.
  apply eval_c_ssubst_commute; 
    try (rewrite sub_range_sat_range);try (rewrite dom_range_combine;[| rwsimplC; auto]); auto.
  + inverts Hcwf as Hcwf _. autorewrite with SquiggleLazyEq in Hcwf. auto.
  + setoid_rewrite <- flat_map_empty. auto.
  + rewrite dom_sub_combine ;[| rwsimplC; auto]. rwsimplC. dands; eauto with subset.

(* eval_Proj_e *)
- intros Hcle ? Hcl ?. rename He into Hev.
  ntwfauto. clear HntwfSig.  remember (Lam_e xl bl) as lam.
  simpl. 
  Local Opaque cps_cvt cps_cvt_val'.
  unfold Proj_e, Fix_e', closed in *.
  simpl in *.
  rwsimpl Hcle.
  rwsimpl Hvc.
  applydup eval_preserves_closed in Hev as Hevvc;[| assumption].
  applydup eval_preseves_wf in Hev as Hevvw;[| assumption].
  applydup (eval_preseves_varclass USERVAR) in Hev as Hevvvc;[| tauto].
  applydup cps_cvt_val_closed in Hevvc as Hevcc; [| try assumption |try assumption].
  apply proj2 in Hvc.
  addContVarsSpec 2 Hvc kv.
  unfold closed in *. simpl in *.
  pose proof Hevvc as Hevvcl.
  rewrite flat_map_empty in Hevvcl.
  pose proof H as Hsel.
  apply select_in in H.
  specialize (Hevvcl _ H).
  pose proof Hevvw as  Hevvwb.
  inverts Hevvw as Hwfes _.
  specialize (Hwfes _ H). inverts Hwfes.
  rwsimpl Hevvvc.
  
  symmetry.
  match goal with 
  [|- context [cps_cvt ?x]] => assert (is_value x) as Hisv
  end.
    subst. rewrite ssubst_ssubst_aux;[| simpl; rwHyps; simpl; auto].
    constructor; fail.
  symmetry.
  do 1 rewrite eval_ret.
  simpl. unfold subst.  
  do 1 rewrite ssubstRet_c.
  assert (forall x, sub_range_sat [(x, k)] closed) as Hcs by
    (intros ? ? ? ?; in_reasoning; cpx).
  rewrite ssubstKlam_c; simpl; auto; [| noRepDis2].
  simpl.
  rewrite ssubst_trivial2_cl;[ | apply Hcs | apply cps_cvt_closed; auto].
  unfold Proj_c.
  unfold ssubst at 1. simpl. 
  do 1 rewrite <- beq_var_refl.
  do 1 (rewrite not_eq_beq_var_false;[| noRepDis]).
  rewrite IHHe; auto;[| rwsimplC; rwHyps; auto].
  let tac :=auto;unfold Con_e; unfold isprogram, closed; rwsimplC; rwHyps; auto in
    rewrite cps_val_ret_flip; [|  eauto using eval_yields_value'| tac | tac | tac].
  prepareForEvalRet Hclkk Hcsss;
    [apply cps_cvt_val_closed; auto; rwsimplC; auto|].
  rewrite eval_ret. simpl. unfold subst.
  unfoldSubst. rewrite <- beq_var_refl.
  rewrite ssubst_trivial2_cl by assumption.
  setoid_rewrite eval_proj; try setoid_rewrite map_length; auto;[|].
  Focus 2.
    unfold cps_cvt_fn_list'. erewrite select_map;[| apply Hsel]. simpl. refl.
  simpl. unfold subst.
  match goal with
  [|- context [ (_,?ft)]  ] => 
    change ft with (cps_cvt_val (oterm (NFix (Datatypes.length es)) es))
  end.
  apply eq_subrelation;[auto with typeclass_instances|].
  do 2 f_equal.
  apply select_in in Hsel.
  rewrite <- eval_c_ssubst_commute; auto;
  try complete (prove_sub_range_sat; auto; constructor).
  rwsimplC. dands; eauto with subset.
Qed.

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
  f_equal;
     [ |rewrite <- snd_split_as_map, combine_split; try rewrite map_length; auto].
  f_equal.
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
      assert (alpha_eq (Ret_c  l k) (Ret_c r nt2)) as Hal
        by (unfold Ret_c; repeat prove_alpha_eq4)
  end.
  apply IHHe in Hal. 
  exrepnd.
  eexists. split;[ | apply Hal0].
  pose proof (conj Hn1 Hl) as Hs. rewrite Hlf in Hs.
  apply select_selectbt in Hs.
  setoid_rewrite eval_proj; eauto.
  apply Hal1.
Qed.

Require Import Coq.Classes.Morphisms.

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


(** [SquiggleLazyEq.substitution.change_bvars_alpha] 
   gets the job done, but it was written
   without any consideration whatsoever to efficiency. Need to
   rewrite it (in the SquiggleLazyEq library) to be efficient.
   
   *)
Definition cps_cvt_unique_bvars :=
 (change_bvars_alpha []) ∘ cps_cvt.

Lemma cps_cvt_unique_alpha : forall (t:NTerm),
  alpha_eq (cps_cvt_unique_bvars t) (cps_cvt t).
Proof using.
  intros.
  symmetry.
  apply change_bvars_alpha_spec.
Qed.

Corollary cps_cvt_unique_corr : forall e v,
  nt_wf e ->
  varsOfClass (all_vars e) USERVAR -> 
  eval e v ->
  closed e ->
  forall k, closed k ->
    forall v',
      eval_cα (Ret_c (cps_cvt_unique_bvars e) k) v' <->
        eval_cα (Ret_c (cps_cvt_unique_bvars v) k) v'.
Proof using.
  intros.
  do 2 rewrite cps_cvt_unique_alpha.
  unfold eval_cα.
  setoid_rewrite cps_cvt_corr at 1; eauto;[].
  refl.
Qed.


Section TypePreservingCPS.
(* if [x] has type [A], then [cps_cvt x] has type [forall {F:Type} (contVar: A -> F), F],
  or, forall {F:Type}, (A -> F)-> F.
So, cps_cvt is the realizer of Godel's double negation transformation, at least for variables.  
   *)
Example cps_cvt_var : forall x,
  cps_cvt (vterm x)
  = KLam_c contVar (Ret_c (vterm contVar) (vterm x)).
Proof using. refl. Qed.

Example cps_cvt_lam : forall x b,
(* suppose [Lam_e x b] has type [A -> B]
[b] has type [B]. [cps_cvt b] has type [forall {F}, ((B -> F) -> F)], by the variable case above,
 and substitution lemma.
because cv2 is applied to  [cps_cvt b], the type of [cv2] must be [B->F], and the type of application
must be [F].
So, the type of [(Lam_c x cv2 (Ret_c (cps_cvt b) (vterm cv2)))] should then be 
[forall {F}, A-> (B->F) -> F].
By using the above var case and substitution lemma, the type of the whole thing (which prepends va_outer),
is [forall {F' F}, ((A-> (B->F) -> F) -> F') -> F']

In the literature in type-preserving CPS translation, they have only one \bot symbol for F.
How do they manage the need above for an F and an F'. There is no reason they should be the same.
Also, to be fully explicit, we should add the type lambdas explicitly, and correspondingly add the instances
in the application case.
*)
  let cv1 := contVar in
  let cv2 := contVar in
  cps_cvt (Lam_e x b)
  = KLam_c cv1 (Ret_c (vterm cv1) (Lam_c x cv2 (Ret_c (cps_cvt b) (vterm cv2))) ).
Proof using. refl. Qed.

(* if [d] is a [bool], and [ct] is of type [A] and [cf] is of type [B], then the result
 this match expression has type [if d then A esle B]*)
Definition depMatchExample (ct cf d : NVar): NTerm :=
  Match_e (vterm d) [(1%N, bterm [] (vterm ct)) ; (2%N, bterm [] (vterm cf))].

Example cps_cvt_depmatch : forall (ct cf d : NVar),
(*
they are computationally equivalent. see [val_outer_eval] below/
*)
  (forall k v, Ret_c (val_outer v) k=  Ret_c k v)
  ->
  cps_cvt (depMatchExample ct cf d) = vterm d.  
(* replacing the result of simpl at RHS causes type inference issues *)
Proof using. intros. simpl.
  set (kv0:= nth 0 (contVars 2) nvarx).
  set (kv1:= nth 1 (contVars 2) nvarx).
  unfold num_bvars. simpl. 

(* [kv0] is applied to both [ct] and [cf]. So, it should have type
  forall {FA FB}, if d then (A -> FA) else (B -> FB)
  [KLam_c kv _] is being applied to [vterm d]. So, [kv1] should have type [bool].
  So, the overall type is:
  forall {FA FB}, 
  (if d then (A -> FA) else (B -> FB)) -> (if d then FA else FB)
  
  *)
Abort.
  
End TypePreservingCPS.


End VarsOf2Class.




(** coqide -R /path/to/SquiggleLazyEq SquiggleLazyEq 
https://github.com/aa755/SquiggleLazyEq

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

Lemma N_plus_minus:
  forall n:N, n > 0 -> (n - 1 + 1) = (n + 1 - 1).
Proof.
  intros.
  induction n using N.peano_ind; intros; lia.
Qed.

Lemma N_plus_minus_eq:
  forall n:N, (n + 1 - 1) = n.
Proof.
  induction n using N.peano_ind; intros; lia.
Qed.

Lemma N_i_plus_1:
  forall i:N, (i + 1) = (1 + i).
  induction i using N.peano_ind; intros; lia.
Qed.
Lemma N_i11:
  forall i, (i + 1 + 1) = (1 + i + 1).
Proof.
  induction i using N.peano_ind; intros; lia.
Qed.

Class Eq (A:Type) :=
  {
    eq_dec : forall (x y:A), {x = y} + {x<>y}
  }.

Instance NEq : Eq N := { eq_dec := N.eq_dec }.
Instance NatEq : Eq nat := { eq_dec := eq_nat_dec }.

Definition lt_dec (x y:N) : {x < y} + { x >= y}.
  refine (match x <? y as z return (x <? y) = z -> {x < y} + {x >= y} with
            | true => fun H => left _ (proj1 (N.ltb_lt x y) H)
            | false => fun H => right _
          end eq_refl).
  intro. unfold N.ltb in *. rewrite H0 in H. discriminate.
Defined.

(**************************)
(** * Source Expressions. *)
(**************************)

Require Import SquiggleLazyEq.alphaeq.

Definition dcon := N.
Definition branch {s} : Set := (dcon * (@BTerm s))%type.

(** Find a branch in a match expression corresponding to a given constructor
    and arity. *)
Fixpoint find_branch {s} (d:N) (m:nat) (matcht :list (@branch s)) : 
    option BTerm 
  := 
  let obr :=
  find 
    (fun a : (@branch s) =>
      let (dcon, btrm) := a in (Nat.eqb (num_bvars btrm) m) && (N.eqb d dcon)) matcht in
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
Proof.
  repeat(decide equality).
Defined.

Definition decnc:
forall
  x y : CoqNonCanonicalOp, {x = y} + {x <> y}.
Proof.
  repeat(decide equality).
Defined.

Definition CoqL4GenericTermSig : GenericTermSig :=
{| 
  CanonicalOp := CoqCanonicalOp;
  NonCanonicalOp := CoqNonCanonicalOp;
  OpBindingsCan := CoqOpBindingsCan;
  OpBindingsNCan := CoqOpBindingsNCan;
  canonical_dec := decc;
  ncanonical_dec := decnc
|}.


Notation BTerm := (@BTerm CoqL4GenericTermSig).
Notation NTerm := (@NTerm CoqL4GenericTermSig).
Notation oterm := (@oterm CoqL4GenericTermSig).
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
Proof.
  intros. simpl. autorewrite with list core. unfold subst.
  rewrite eqsetv_free_vars_disjoint.
  intros ? Hc.
  rewrite in_app_iff in *.
  simpl in Hc.
  dorn Hc;[left; firstorder|right].
  rewrite memvar_dmemvar in Hc.
  if_splitH Hc; simpl in Hc; autorewrite with list in *;firstorder.
Qed.

Lemma eval_reduces_fvars :
  forall e v, eval e v ->  subset (free_vars v) (free_vars e).
Proof.
  intros ? ? He. unfold closed. induction He; try auto;
  simpl in *;autorewrite with core list in *.
  (**Apply case*)
  -
    unfold subset.
    pose proof (subset_step_app x e1' v2) as H.
    pose proof (subset_trans _ _ _ _ IHHe3 H).
    clear H IHHe3. eapply subsetv_trans; eauto.
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

  - intros ? Hf. apply_clear IHHe2 in Hf.
    destruct e' as [lv nt].
    unfold apply_bterm in Hf. simpl in Hf.
    rewrite eqsetv_free_vars_disjoint in Hf.
    revert H. destFind; intro Hdf; [| discriminate].
    repnd.
    destruct bss as [xxx brbt]. simpl in Hdf. subst.
    apply andb_true_iff, proj1,beq_nat_true in Heqsnl.
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
Proof.
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
Proof.
  intros ? ? He ; induction He ; simpl ; intros ; 
  auto ; try constructor ; auto.
  - change vs  with (snd (es, vs)).
    rename H into Hl.
    apply combine_split in Hl.
    rewrite <- Hl.
    rewrite  snd_split_as_map.
    intros ? Hin.
    apply in_map_iff in Hin.
    exrepnd. simpl in *. subst.
    eauto.
  - unfold subst, lsubst.
    cases_if; simpl;[constructor|].
    match goal with 
    [|- context[fresh_vars 1 ?lv]] => destruct (fresh_vars 1 lv)
    end.
    repnd. dlist_len_name x a. simpl. constructor. 
Qed.

Ltac ntwfauto := 
simpl substitute in *;alphaeq.ntwfauto.

Lemma eval_preseves_wf :
  forall e v, eval e v ->  nt_wf e -> nt_wf v.
Proof.
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
    SearchAbout LIn map bterm.
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
  + revert H. destFind;intros Hyp; [| discriminate].
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


(**********************)
(** * CPS expressions *)
(**********************)


Inductive CPSCanonicalOp : Set :=
 | CLambda (** only abstracts a user var*)
 | CKLambda (** like Cont_c, only abstracts a cont var*)
 | CFix (nMut : nat) (** number of functions that are mutually defined*)
 | CDCon (dc : dcon) (nargs : nat).

Definition CPSOpBindingsCan (c : CPSCanonicalOp) 
    : list nat :=
  match c with
  | CLambda    => [1]
  | CKLambda    => [1]
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
Proof.
  repeat(decide equality).
Defined.

Definition cdecnc:
forall
  x y : CPSNonCanonicalOp, {x = y} + {x <> y}.
Proof.
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


Notation CBTerm := (@terms.BTerm CPSGenericTermSig).
Notation CTerm := (@terms.NTerm CPSGenericTermSig).
Notation coterm := (@terms.oterm CPSGenericTermSig).
Notation CCan := (@opid.Can CPSGenericTermSig).
Notation CNCan := (@opid.NCan CPSGenericTermSig).

Definition Lam_c (v : NVar) (b : CTerm) : CTerm :=
  coterm (CCan CLambda) [bterm [v] b].

Definition KLam_c (v : NVar) (b : CTerm) : CTerm :=
  coterm (CCan CKLambda) [bterm [v] b].

Definition Ret_c (f a : CTerm) :=
  coterm (CNCan CRet) [bterm [] f , bterm [] a].

Definition Halt_c (v : CTerm) :=
  coterm (CNCan CRet) [bterm [] v].

Definition Call_c (f k a : CTerm) :=
  coterm (CNCan CCall) [bterm [] f , bterm [] k , bterm [] a].

Definition Con_c (dc : dcon) (args : list CTerm) : CTerm :=
  coterm (CCan (CDCon dc (length args))) (List.map (bterm []) args).

Definition Proj_c (arg: CTerm) (selector : nat) (cont: CTerm)  : CTerm :=
  coterm (CNCan (CProj selector)) [bterm [] arg, bterm [] cont].

(** do we need a continuation variable as well? *)
Definition Fix_c (xf : NVar) (args : list CTerm) : CTerm :=
  coterm (CCan (CFix (length args))) (List.map (bterm [xf]) args).

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

(** use simultaneous substitution? *)

| eval_Call_c : forall xk x c v1 v2 v',
                  eval_c (c {x:=v2}{xk:=v1}) v' -> 
                  eval_c (Call_c (KLam_c xk (Lam_c x c)) v1 v2) v'
| eval_Match_c : forall d vs bs c v',
                   find_branch d (List.length vs) bs = Some c ->
                   eval_c (apply_bterm c vs) v' -> 
                   eval_c (Match_c (Con_c d vs) bs) v'
| eval_Proj_c : forall xf cs i c k v',
                  select i cs = Some c -> 
                  (** CHECK! there was a Lam_c in the line below before*)
                  eval_c (Ret_c k (c{xf:=Fix_c xf cs})) v' ->
                  eval_c (Proj_c (Fix_c xf cs) i k) v'.
                  
Hint Constructors eval_c.

(** Useful for rewriting. *)
Lemma eval_ret :
  forall x c v v', eval_c (Ret_c (KLam_c x c) v) v' 
  <-> eval_c (c{x := v}) v'.
Proof.
  intros. split ; intro. inversion H. subst ; auto. constructor ; auto.
Qed.

(** Useful for rewriting. *)
Lemma eval_call : forall xk x c v1 v2 v',
   eval_c (Call_c (KLam_c xk (Lam_c x c)) v1 v2) v'
  <-> eval_c (c {x:=v2}{xk:=v1}) v'.
Proof.
  intros ; split ; intro; inversion H ; subst ; auto.
Qed.

(*
(** Useful for rewriting. *)
Lemma eval_match :
  forall d vs bs v' c,
    find_branch d (N.of_nat (List.length vs)) bs = Some c -> 
    (eval_c (Match_c (Con_c d vs) bs) v' <-> (eval_c (usubst_list c vs) v')).
Proof.
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
Proof.
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
          | NDCon _ _ => ball (List.map (is_valueb ∘ get_nt) lb)
          | _ => true
          end
      | opid.NCan _ => false
      end
   end.

Lemma is_valueb_corr :
  (forall e, is_value e -> is_valueb e = true).
Proof.
  intros ? H.
  induction H; auto. simpl. rewrite map_map.
  unfold compose. simpl. 
  rewrite ball_map_true. auto.
Qed.


(** The inner, naive CBV CPS translation.  This introduces a lot of 
    administrative reductions, but simple things first.  Importantly,
    things that are already values are treated a little specially.  
    This ensures a substitution property 
    [cps_cvt(e{x:=v}) = (cps_cvt e){x:=(cps_vt_val v)}].
 *)
 
Section CPS_CVT.
(** these are ALL vars, not just the free vars, of the top level term being converted*)
(** recursive call below *)
  Variable cps_cvt : (list NVar) -> NTerm -> CTerm (*val_c *).
  
      (* cont \k.(ret [e1] (cont \v1.(ret [e2] (cont \v2.call v1 k v2)))) *)
  Definition cps_cvt_apply (fve : list NVar) (ce1 : CTerm) (e2: NTerm) : CTerm :=
      let kvars := projT1 (fresh_vars 3 fve) in 
      let k := nth 0 kvars nvarx in  
      let k1 := nth 1 kvars nvarx in  
      let k2 := nth 2 kvars nvarx in  
       KLam_c k 
        (Ret_c ce1 (* e1 may not already be a lambda *)
               (KLam_c k1 (Ret_c (cps_cvt fve e2)
                                  (KLam_c k2 (Call_c (vterm k1) (vterm k) (vterm k2)))))).


(* [b] can have [x] free. thos occurrences should not get captured by continuation variable *)
  Definition cps_cvt_lambda (fve : list NVar) (x : NVar) (b: NTerm) : CTerm :=
          let fvee := (x::fve) in
          let kv := fresh_var fvee in
             KLam_c kv (Lam_c x (Ret_c (cps_cvt fvee b) (vterm kv))).

  (** the KLam_c was manually added. unlike now, Fix_c previously implicitly bound a var*)
  Definition cps_cvt_fn_list' (fve : list NVar) (es: list BTerm) : list CBTerm :=
    map (fun b => 
            let e := get_nt b in
            let vars := get_vars b in
            let kv := fresh_var (vars ++ fve) in 
                    bterm vars (KLam_c kv (Ret_c (cps_cvt (vars ++ fve) e) (vterm kv))) ) es.

  Fixpoint cps_cvt_val'(fve : list NVar) (e:NTerm) : CTerm :=
    match e with
      | vterm n => vterm n
      | terms.oterm (opid.Can NLambda) [bterm [x] b] => 
          cps_cvt_lambda fve x b
      | terms.oterm (opid.Can (NDCon d l)) lb => 
          let fb := (fun b => 
                      bterm (get_vars b) 
                            (cps_cvt_val' ((get_vars b) ++ fve) (get_nt b))) in
            coterm (CCan (CDCon d l)) (List.map fb lb)
      | terms.oterm (opid.Can (NFix nargs)) lb =>
          terms.oterm (CCan (CFix nargs))
             (cps_cvt_fn_list' fve lb)
      | _ => coterm (CCan CLambda) (map ((bterm []) ∘ vterm)  (free_vars e))
          (* ill-formed term, which will not arise from the prev. phase.
            This choice, which is also ill-formed,
            is just to ensure that the free variables are same as
            that of the the input *)
    end.

  Fixpoint cps_cvts' (fve : list NVar) (vs: list NVar )(es:list BTerm) (c:CTerm) :  CTerm :=
    match es with
      | nil => c
      | (bterm _ e)::es =>
        match vs with
        | [] => Ret_c (cps_cvt fve e) (KLam_c nvarx (cps_cvts' fve [] es c)) (* impossible *)
        | kvh :: kvt => Ret_c (cps_cvt fve e) (KLam_c kvh (cps_cvts' fve kvt es c))
        end
    end.


  Definition cps_cvt_branch' (fve : list NVar) (kv : NVar) (bt: BTerm) : CBTerm :=
    match bt with
    | bterm vars nt =>
        (bterm vars (Ret_c (cps_cvt (vars ++ fve) nt) (vterm kv)))
    end.

 Definition cps_cvt_branches' (fve : list NVar) (kv : NVar) : (list BTerm) ->
    list CBTerm :=
  List.map (cps_cvt_branch' fve kv).

End CPS_CVT.

Section CPSFvars.


Fixpoint cps_cvt_aux (fve : list NVar) (e:NTerm) {struct e}: CTerm :=
  let val_outer ce :=
    let kv := fresh_var fve in 
      KLam_c kv (Ret_c (vterm kv) ce) in
  if is_valueb e 
  then val_outer (cps_cvt_val' cps_cvt_aux fve e) 
    else
  match e with
    | terms.oterm (opid.NCan NApply) [bterm [] e1; bterm [] e2] => 
        cps_cvt_apply cps_cvt_aux fve (cps_cvt_aux fve e1) e2
    | terms.oterm (opid.Can (NDCon d nargs)) es => 
        let kvars := projT1 (fresh_vars (S (length es)) fve) in
        let k := hd nvarx kvars  in
        let tlkv := tail kvars  in
        KLam_c k (cps_cvts' cps_cvt_aux fve tlkv es (Ret_c (vterm k)
                                                          (Con_c d (map vterm tlkv))))
    | terms.oterm (opid.NCan (NMatch brl)) ((bterm [] discriminee)::brr) => 
      let kvars := projT1 (fresh_vars 2 (fve ++ (flat_map get_vars brr))) in 
      let k := nth 0 kvars nvarx in
      let kd := nth 1 kvars nvarx in
      let brrc :=  (bterm [] (vterm kd))::(cps_cvt_branches' cps_cvt_aux fve k brr) in
      KLam_c k (Ret_c (cps_cvt_aux fve discriminee)
                      (KLam_c kd 
                              (coterm (CNCan (CMatch brl)) brrc)))
    | terms.oterm (opid.NCan NLet) [bterm [] e1, bterm [x] e2] => 
      let cpsLam := (val_outer (cps_cvt_lambda cps_cvt_aux fve x e2)) in
        cps_cvt_apply cps_cvt_aux fve cpsLam e1
      
      (* translate as if it were App_e (Lam_e x e2) e1. unlike the general cas of App, here the function
        is already a value *)

    | terms.oterm (opid.NCan (NProj i)) [bterm [] e] =>
      let kvars := projT1 (fresh_vars 2 fve) in 
      let k := nth 0 kvars nvarx in  
      let ke := nth 1 kvars nvarx in  
        KLam_c k (Ret_c (cps_cvt_aux fve e) 
                        (KLam_c ke (Proj_c (vterm ke) i (vterm k))))
    | _ => coterm (CCan CLambda) (map ((bterm []) ∘ vterm)  (free_vars e))
          (* ill-formed term, which will not arise from the prev. phase.
            This choice, which is also ill-formed,
            is just to ensure that the free variables are same as
            that of the the input *)
  end.
End CPSFvars.

Definition cps_cvt (e:NTerm) : CTerm :=
  let fve := free_vars e in (* the var library can have a way to compress a list of vars to a range, and have an alternate more efficient free vars function*)
   cps_cvt_aux fve e.

Definition cps_cvt_val (e:NTerm) : CTerm :=
  let fve := free_vars e in 
  cps_cvt_val' cps_cvt_aux fve e.
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

Lemma cps_cvt_let_as_app_lam : forall e1 x e2 lv,
  cps_cvt_aux lv (Let_e x e1 e2)
  = cps_cvt_aux lv (App_e (Lam_e x e2) e1).
Proof.
  intros. reflexivity.
Qed.


Lemma cps_val :
  forall (v:NTerm) (lv : list NVar), 
  closed v (* remove and change equality to alpha equality*)
  ->
  let k := fresh_var lv in
  is_value v -> 
  (cps_cvt_aux lv v) = 
    KLam_c k (Ret_c (vterm k) (cps_cvt_val' cps_cvt_aux lv v)).
Proof.
  simpl. intros ? ? Hcl Hisv.
  induction Hisv; intros; simpl;
  unfold cps_cvt; try rewrite Hcl;
  simpl in *; auto.
  rewrite (fun l => proj2 (ball_true l));
    [reflexivity|].
  intros ?. simpl.
  rewrite map_map. unfold compose. simpl.
  intros Hin. apply in_map_iff in Hin. exrepnd. subst.
  apply is_valueb_corr. eauto.
Qed.



Lemma lsubstRet_c : forall sub a b, 
  sub_range_sat sub closed
  -> lsubst (Ret_c a b) sub = Ret_c (lsubst a sub) (lsubst b sub).
Proof.
  intros.
  change_to_lsubst_aux4.
  simpl. autorewrite with SquiggleLazyEq.
  reflexivity.
Qed.

Lemma lsubstKlam_c : forall sub x b, 
  sub_range_sat sub closed
  -> disjoint [x] (dom_sub sub)
  -> lsubst (KLam_c x b) sub = KLam_c x (lsubst b sub).
Proof.
  intros.
  change_to_lsubst_aux4.
  simpl. rewrite sub_filter_disjoint1;[| disjoint_reasoningv].
  reflexivity.
Qed.

Lemma substKlam_cTrivial : forall x (b t : CTerm),
  closed t
  -> lsubst (KLam_c x b) [(x,t)] = KLam_c x b.
Proof.
  intros ? ? ? H.
  change_to_lsubst_aux4;[ |simpl; rewrite H; disjoint_reasoningv; tauto].
  simpl. rewrite memvar_singleton. rewrite <- beq_var_refl.
  simpl. rewrite lsubst_aux_nil.
  reflexivity.
Qed.


Lemma substKlam_cTrivial2 : forall x xx (b t : CTerm),
  closed t
  -> closed (KLam_c x b)
  -> lsubst (KLam_c x b) [(xx,t)] = KLam_c x b.
Proof.
  intros ? ? ? ? H Hb.
  change_to_lsubst_aux4;[ |simpl; rewrite H; disjoint_reasoningv; tauto].
  simpl. rewrite memvar_singleton.
  rewrite beq_deq. cases_if.
  - simpl. rewrite lsubst_aux_nil.
    reflexivity.
  - unfold KLam_c. do 3 f_equal.
    apply lsubst_aux_trivial_cl.
    intros ? ? Hin. in_reasoning. inverts Hin.
    split; [assumption|].
    unfold closed in Hb. simpl in Hb.
    autorewrite with core list in Hb.
    rw nil_remove_nvars_iff in Hb.
    firstorder.
Qed.

Lemma lsubstCall_c : forall sub a b d, 
  sub_range_sat sub closed
  -> lsubst (Call_c a b d) sub = Call_c (lsubst a sub) (lsubst b sub) (lsubst d sub).
Proof.
  intros.
  change_to_lsubst_aux4.
  simpl. autorewrite with SquiggleLazyEq.
  reflexivity.
Qed.


Section CPSFV.
Local Lemma cps_cvt_val_aux_fvars_aux : forall o lbt,
  (forall es lvs, 
    (size es) < size (oterm o lbt)
    -> nt_wf es 
    -> subset (free_vars es) lvs 
    -> eqset (free_vars (cps_cvt_aux lvs es)) (free_vars es))
-> nt_wf (oterm o lbt)
-> 
forall lv : list NVar,
subset (flat_map free_vars_bterm lbt) lv ->
eqset (flat_map free_vars_bterm (cps_cvt_fn_list' cps_cvt_aux lv lbt))
  (flat_map free_vars_bterm lbt).
Proof.
  intros ? ? Hyp Hwf ? Hs.
  unfold cps_cvt_fn_list'. rewrite flat_map_map.
  apply eqset_flat_maps.
  intros bt Hin.
  destruct bt as [lvb nt]. unfold compose.
  simpl.
  autorewrite with list SquiggleLazyEq.
  rewrite remove_nvars_app_r, remove_nvars_eq.
  simpl in Hs.
  autorewrite with list in *.
  rewrite Hyp; [
    | eapply size_subterm3; eauto
    | ntwfauto
    | eapply subset_flat_map_lbt; eauto
      ].
  rewrite subsetv_flat_map in Hs.
  specialize (Hs _ Hin).
  simpl in Hs.
  unfold subset in Hs.
  setoid_rewrite in_remove_nvars in Hs.
  apply eqsetv_prop.
  intros.
  pose proof (fresh_var_not_in (lvb ++ lv)) as Hf.
  repeat rewrite in_remove_nvars.
  repeat rewrite in_single_iff in *. split; cpx.
  clear Hyp.
  simpl in Hf.
  intros Hx. applydup_clear Hs in Hx.
  repeat(split; try tauto).
  intros Hss. subst.
  rewrite in_app_iff in *.
   tauto.
Qed.

Local Ltac 
illFormedCase :=
 (try reflexivity; try (simpl;rewrite flat_map_vterm; reflexivity)).


Lemma cps_cvt_val_aux_fvars : forall e,
  (forall es lvs, 
     (size es) < size e  
    -> nt_wf es 
    -> subset (free_vars es) lvs 
    -> eqset (free_vars (cps_cvt_aux lvs es)) (free_vars es))
  -> nt_wf e 
  -> forall lv, subset (free_vars e) lv 
  -> eqset (free_vars (cps_cvt_val' cps_cvt_aux lv e)) (free_vars e).
Proof.
  intros ? Hyp.
  nterm_ind e as [v | o lbt Hind] Case;[eauto|].
  intros Hwf ? Hs. simpl in Hs.
  destruct o;[| illFormedCase].
  destruct c;[clear Hind| clear Hind|].
(* apply case *)
- simpl.
  destructlbt lbt illFormedCase.
  destructbtdeep2 b illFormedCase.
(*  destructlbt lbt illFormedCase. this causes error, but unfolding it, as below, succeeds*)
  repeat (
  let b := fresh "b" in
  destruct lbt as [| b lbt];illFormedCase; []).
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
  apply properEqsetvRemove; eauto.
  rewrite Hind; eauto; [|ntwfauto; fail|].
  + intros.  apply Hyp; eauto. eapply lt_trans; eauto.
    eapply size_subterm3; eauto.
  + eapply subset_flat_map_lbt; eauto.
Qed.

Hint Rewrite <- beq_var_refl : SquiggleLazyEq.

Lemma size_pos : forall {gts} t, 
  0<(@size gts t).
Proof.
  intros. destruct t; simpl; omega.
Qed.

(** will be used for both the [App_e] ane [Let_e] case *)
Lemma cps_cvt_apply_fvars : forall e1 e2,
  (forall es lvs, 
     (S (size es)) < (size (App_e e1 e2))
    -> nt_wf es 
    -> subset (free_vars es) lvs 
    -> eqset (free_vars (cps_cvt_aux lvs es)) (free_vars es))
  -> nt_wf (App_e e1 e2)
  -> forall lv, subset (free_vars (App_e e1 e2)) lv 
  -> eqset (free_vars (cps_cvt_aux lv (App_e e1 e2))) (free_vars (App_e e1 e2)).
Proof.
  intros ? ? Hind Hwf ? Hs.
  simpl.
  destruct (fresh_vars 3 lv) as [fvs Hfr]. 
  simpl. repnd. 
  dlist_len_name fvs kv. simpl.
  simpl in Hs.
  autorewrite with list SquiggleLazyEq in *.
  repeat (rewrite not_eq_beq_var_false;[| noRepDis]).
  repeat rewrite remove_nvars_app_r.
  setoid_rewrite remove_nvars_comm at 2.
  repeat rewrite remove_nvars_app_l.
  rewrite remove_nvars_eq, app_nil_r.
  apply subsetv_app_l in Hs. repnd.
  pose proof (size_pos e2).
  pose proof (size_pos e1).
  do 2 (rewrite Hind; [ | simpl; omega | ntwfauto | assumption]).
  unfold subset in *.
  apply disjoint_sym in Hfr1.
  eapply subset_disjoint in Hs0; eauto.
  eapply subset_disjoint in Hs; eauto.
  clear Hind.
  rewrite (fun l1 l2 => proj1 (remove_nvars_unchanged l1 l2));[|noRepDis].
  rewrite (fun l1 l2 => proj1 (remove_nvars_unchanged l1 l2));[|noRepDis].
  reflexivity.
Qed.


(*
Ltac inauto:=
(repeat match goal with
[H: no_repeats [] |- _] => clear H
|[H: no_repeats (_::_) |- _] =>
  let Hnrd := fresh "Hnrd" in
  apply no_repeats_as_disjoint in H;
  destruct H as [Hnrd H]
end); disjoint_reasoningv; 
unfold subset in *;
unfold disjoint in *;
repeat (rewrite in_single_iff in * ); (* can this be removed? *)
repeat match goal with 
| [H:context[LIn _ (flat_map _ _) ] |- _] => setoid_rewrite in_flat_map in H
| [|- context[LIn _ (flat_map _ _)]] => setoid_rewrite in_flat_map
| [H:context[LIn  _ (map _ _)]|- _] => setoid_rewrite in_map_iff in H
| [H:context[_ = []]|- _] => apply null_iff_nil in H; unfold null in H; simpl in H
| [|- [_ = []]] => apply null_iff_nil; unfold null; simpl
| [|- context[LIn  _ (map _ _)]] => setoid_rewrite in_map_iff
end;
subst.
*)

Lemma cps_cvt_constr_fvars : forall lbt lkv c o,
  (forall es lvs, 
     (size es < size (oterm o lbt))
    -> nt_wf es 
    -> subset (free_vars es) lvs 
    -> eqset (free_vars (cps_cvt_aux lvs es)) (free_vars es))
  -> length lbt = length lkv 
  -> (forall b, LIn b lbt -> (bt_wf b /\ get_vars b = []))
  -> forall lv, 
    subset (free_vars (oterm o lbt)) lv 
    -> disjoint lkv lv
    -> eqset (free_vars (cps_cvts' cps_cvt_aux lv lkv lbt c))
            (free_vars (oterm o lbt) ++ (remove_nvars  lkv (free_vars c))).
Proof.
  induction lbt as [| b lbt IHlbt]; intros ? ? ? Hyp Hl Hf ? Hs Hdis;
    simpl in Hl; dlist_len_name lkv kv;[auto|].
  simpl in *.
  destruct b as [blv bnt].
  simpl.
  autorewrite with list SquiggleLazyEq.
  apply subsetv_app_l in Hs.
  rewrite IHlbt; eauto; [| intros; apply Hyp; eauto; omega |tauto | inauto; tauto].
  clear IHlbt.
  dLin_hyp. simpl in *. repnd. subst.
  autorewrite with SquiggleLazyEq in *.
  rewrite remove_nvars_app_r.
  rewrite remove_nvars_app_l.
  rewrite (fun l1 l2 => proj1 (remove_nvars_unchanged l1 l2));[|inauto;eauto].
  rewrite app_assoc.
  rewrite Hyp; auto; [omega| ntwfauto].
Qed.

Hint Rewrite flat_map_bterm_nil (fun gts => @flat_map_free_var_vterm gts)
  remove_nvars_eq : SquiggleLazyEq.

Lemma cps_cvt_aux_fvars : forall e lv,
  nt_wf e ->
  subset (free_vars e) lv ->
  eqset (free_vars (cps_cvt_aux lv e)) (free_vars e).
Proof.
  intros e.
(** Induction on size of the term. Subterm-based induction does not work in this approach.
    Recall that Let_e e1 (x.e2) is treated like App_e (Lam_e (x.e2)) e1.
    Note that (Lam_e (x.e2)) is not a structural subterm of (Let_e e1 (x.e2)).
    However, size (Lam_e (x.e2)) < (Let_e e1 (x.e2)), thus allowing us to invoke the 
    induction hypothesis on (Lam_e (x.e2))
 *)  
  induction e as [v | o lbt Hind] using NTerm_better_ind3;
  intros ? Hwf Hs;
  [ apply subsetv_singleton_l in Hs;
    simpl in *; autorewrite with core list SquiggleLazyEq;
    rewrite not_eq_beq_var_false; eauto using fresh_var_not_eq |].

Local Opaque cps_cvt_val' is_valueb. 
  simpl.  
  cases_if.
(* e is a value; use the lemma above *)
- simpl. autorewrite with SquiggleLazyEq.
Local Transparent cps_cvt_val' is_valueb. 
  rewrite cps_cvt_val_aux_fvars;[simpl; autorewrite with list| | ntwfauto | assumption].
  + rewrite remove_nvars_nop;[auto|].
    intros ? Hin. rewrite in_single_iff. intros Hc. subst.
    unfold subset in Hs.
    apply Hs in Hin. revert Hin. apply fresh_var_not_in.
  + intros ? ? Hss Hsv. destruct lbt;
      [destruct es; simpl in Hss; omega|];apply Hind; auto.
(* e is not a value *)
- destruct o as [c| nc];[destruct c | destruct nc ]; illFormedCase.
(** data constructor when not all subterms are values *)
  + destruct (fresh_vars (S (Datatypes.length lbt)) lv) as [lkv Hfr].
    simpl. repnd.
    dlist_len_name lkv kv; simpl in *.
    rewrite  cps_cvt_constr_fvars with (o:=(Can (NDCon dc nargs))); auto;
      [| | inauto].
    * simpl. autorewrite with list SquiggleLazyEq.
      rewrite memvar_dmemvar.
      cases_if;[inauto|].
      rewrite remove_nvars_app_r.
      autorewrite with list SquiggleLazyEq.
      rewrite remove_nvars_nop; [auto|inauto;eauto].
    * intros ? Hin.
      pose proof Hin as Hinb.
      split; [ntwfauto|].
      inverts Hwf as ? Hl.
      eapply map_eq_repeat_implies in Hl; eauto.
      unfold num_bvars in Hl.
      apply length_zero_iff_nil in Hl. assumption.

(** App_e *)
  +
    destruct lbt as [|b lbt]; illFormedCase;[].
    destructbtdeep2 b illFormedCase.
    destruct lbt as [|b lbt]; illFormedCase;[].
    destructbtdeep2 b illFormedCase.
    destruct lbt as [|b lbt]; illFormedCase;[].
    
    apply cps_cvt_apply_fvars; auto.
    intros; apply Hind; auto;[]. simpl in *. omega.

(** Proj_e *)
  +
    destruct lbt as [|b lbt]; illFormedCase;[].
    destructbtdeep2 b illFormedCase.
    destruct lbt as [|b lbt]; illFormedCase;[].
    destruct (fresh_vars 2 lv) as [lkv Hfr]. repnd. 
    simpl in *. dlist_len_name lkv kv; simpl in *.
    autorewrite with list SquiggleLazyEq in *.
    rewrite not_eq_beq_var_false;[|inauto; eauto].
    rewrite remove_nvars_app_r.
    rewrite Hind;[| omega | ntwfauto | assumption].
    autorewrite with list SquiggleLazyEq.
    rewrite remove_nvars_nop;[auto| inauto; eauto].

(** Let_e *)
  + destruct lbt as [|b lbt]; illFormedCase;[].
    destructbtdeep2 b illFormedCase.
    destruct lbt as [|b lbt]; illFormedCase;[].
    destructbtdeep2 b illFormedCase.
    destruct lbt as [|b lbt]; illFormedCase;[].
    
    unsimpl (cps_cvt_aux lv (Let_e blv1 bnt bnt0)).
    rewrite cps_cvt_let_as_app_lam.
    remember (Lam_e blv1 bnt0) as lam.
    simpl in Hs.
    autorewrite with list SquiggleLazyEq in Hs.
    apply subsetv_app_l in Hs.
    rewrite cps_cvt_apply_fvars;
      [
        | subst lam;
          intros;  simpl in *; apply Hind;[omega | ntwfauto |assumption]
        | subst lam; ntwfauto;in_reasoning; subst; ntwfauto
        | subst lam; simpl in *; autorewrite with list SquiggleLazyEq;
          apply subsetv_app_l; tauto
        ].
    subst lam. clear.
    simpl. autorewrite with list SquiggleLazyEq.
    apply eqsetv_prop. intros. repeat rewrite in_app_iff.
    tauto. 

(** Match_e *)
  + 
    destruct lbt as [|b lbt]; illFormedCase;[].
    destructbtdeep2 b illFormedCase.
    destruct (fresh_vars 2 (lv ++ flat_map get_vars lbt)) as [lkv Hfr]. repnd.
    Local Opaque size.
    simpl in *. dlist_len_name lkv kv; simpl in *.
    Local Transparent size.
    autorewrite with list SquiggleLazyEq in *.
    unfold cps_cvt_branches'.
    rewrite flat_map_map.
    unfold compose. simpl.
    apply subsetv_app_l in Hs. repnd.
    rewrite eqset_flat_maps with (g:=fun b => kv::(free_vars_bterm b)).
    * rewrite remove_nvars_flat_map. unfold compose.
      rewrite eqset_flat_maps with (g:=fun b => kv::(free_vars_bterm b));
        [| intros; rewrite remove_nvars_cons_r,
           memvar_singleton, not_eq_beq_var_false;[| inauto; tauto];
           rewrite remove_nvars_nop;[refl|inauto; eauto]].
      rewrite remove_nvars_app_r.
      rewrite Hind;[| simpl;omega | ntwfauto | assumption].
      clear Hind.
      rewrite remove_nvars_nop;[|inauto; eauto].
      rewrite remove_nvars_flat_map. unfold compose.
      rewrite eq_flat_maps with (g:=fun b => (free_vars_bterm b));[auto;fail|].
      intros.
      rewrite remove_nvars_cons_r, memvar_singleton.
      autorewrite with SquiggleLazyEq. 
      rewrite remove_nvars_nop;[refl|inauto; eauto].
      
    * intros ? Hin. destruct x as [xlv xnt]. simpl.
      autorewrite with SquiggleLazyEq.
      rw subset_flat_map in Hs. pose proof Hin as Hinb. apply_clear Hs in Hin.
      simpl in Hin. rewrite subsetv_remove_nvars in Hin.
      rewrite Hind;
        [|eapply size_subterm3; right; eauto 
         | ntwfauto 
         |  unfold subset in  Hin; setoid_rewrite in_app_iff in Hin;
            intros ? ?; apply in_app_iff; apply or_comm; auto].
      rewrite remove_nvars_app_r.
      rewrite remove_nvars_cons_r.
      autorewrite with SquiggleLazyEq.
      SearchAbout xnt.
      inverts Hwf. simpl in H3.
      rewrite memvar_dmemvar.
      cases_if;[inauto; provefalse; eauto |]. 
      setoid_rewrite cons_as_app at 2.
      unfold eqset, subset. setoid_rewrite in_app_iff.
      tauto.
Qed.

(* Print Assumptions cps_cvt_aux_fvars.
close under global context *)

Corollary cps_cvt_val_fvars : forall (e : NTerm) (lv : list NVar),
 nt_wf e
 -> subset (free_vars e) lv 
 -> eqset (free_vars (cps_cvt_val' cps_cvt_aux lv e)) (free_vars e).
Proof.
  intros ? ? Hwf Hs.
  rewrite cps_cvt_val_aux_fvars; auto.
  intros.
  rewrite cps_cvt_aux_fvars; auto.
Qed.

Corollary cps_cvt_val_closed : forall e lv,
  nt_wf e
  -> closed e
  -> closed (cps_cvt_val' cps_cvt_aux lv  e).
Proof.
  intros ? ? Hwf Hcl.
  unfold closed in *.
  apply null_iff_nil.
  unfold cps_cvt_val.
  rewrite cps_cvt_val_fvars; auto;
  rewrite Hcl; auto.
Qed.
End CPSFV.



Lemma eval_c_subst_commute : forall x v e,
nt_wf v
-> is_value v
-> closed v
-> forall (lv : list NVar),
  lsubst (cps_cvt_aux (x::lv) e) [(x, cps_cvt_val' cps_cvt_aux lv v)]
    = cps_cvt_aux lv (lsubst e [(x, v)]).
 Proof.
  intros ? ? ?. unfold closed.
  induction e as [xx | o lbt Hind] using NTerm_better_ind3;
  intros Hwf Hisv Hcl ?;
  [ |].
  - simpl. unfold lsubst, cps_cvt_val. simpl. 
    rewrite cps_cvt_val_closed;[| auto| auto]. simpl.
    autorewrite with SquiggleLazyEq. simpl.
    autorewrite with SquiggleLazyEq.
    cases_if; simpl;[|].
    Focus 2. unfold KLam_c. f_equal. f_equal. unfold Ret_c.
    (* this is unprovable. The LHS and RHS of = are only alpha equal.
    This lemma needs to be weakened. In the LHS term, 
    CPS conversion will avoid picking [x] as a continuation variable, to avoid capture.
    Note that [e] was a part of [Lam_e x e] in the theorem [cps_cvt_corr] below.
    Thus, [e] can have [x] free.

    The conversion in RHS can pick [x] as a continuation variable if [x] is not in [lv].
    Note that [(lsubst e [(x, v)])] is a closed term.

    Also, this lemma needs to be generalized for simultaneous substitution of 
    several variables to handle the [Match_e] case in the theorem [cps_cvt_corr]
    below.
      *)
 Admitted.

(** Once we establish that eval and eval_c respect alpha equality, we can get rid of 
closedness assumptions for e and k and make the proof easier.
A large part of the current proof is about reistablishing these while involking induction
hypothesis. when k (or e, because parts of e get into the continuation) is not closed,
alpha renaming may occur during substitution. *)  
Theorem cps_cvt_corr : forall e v,
  nt_wf e ->
  eval e v ->
  closed e -> (* implies subset (free_vars e) lv *)
  forall k, closed k ->
    forall v' lv, 
      eval_c (Ret_c (cps_cvt_aux lv e) k) v' <->
        eval_c (Ret_c (cps_cvt_aux lv v) k) v'.
Proof.
  intros ? ? Hwf He.  induction He; try (simpl ; tauto; fail); [| | | |].
  (* beta reduction case (eval_App_e) *)
- intros Hcle ? Hcl ? ?.
   unfold App_e. simpl.
   unfold cps_cvt_apply.
(* not doing this destruction may enable proofs by computation, but can cause
  trouble later when [] is generalized *)   
  destruct (fresh_vars 3 lv) as [kv Hflv]. simpl.
  repnd.  dlist_len_name kv kv. simpl.
  unfold closed in Hcle. simpl in Hcle.
  autorewrite with core list in Hcle.
  apply app_eq_nil in Hcle. repnd.
  specialize (IHHe1 $(ntwfauto)$ Hcle0).
  specialize (IHHe2 $(ntwfauto)$ Hcle).
  specialize (IHHe3 $(apply' eval_preseves_wf He1; 
                      ntwfauto; eauto using eval_preseves_wf)$).
  pose proof (subset_step_app x e1' v2) as Hsss.
  simpl in IHHe3. unfold subst in IHHe3.
  applydup eval_reduces_fvars in He1 as Hss.
  applydup eval_reduces_fvars in He2 as Hss2.
  unfold subset in Hss, Hss2.
  rewrite Hcle0 in Hss. apply subsetv_nil_r in Hss.
  rewrite Hcle in Hss2. apply subsetv_nil_r in Hss2.
  simpl in Hss, Hsss.
  autorewrite with list core in *.
  dimp IHHe3;
    [apply subsetv_nil_r; eapply transitivity;[apply Hsss|]; simpl; 
      apply subsetv_app_l;
     split;  apply subsetv_nil_r; eauto|].
  specialize (IHHe3 hyp).
  clear hyp.
  rewrite <- IHHe3;[| assumption]. clear IHHe3.
  rewrite eval_ret.
  simpl. unfold subst. 
  assert (sub_range_sat [(kv0, k)] closed) as Hcs by
    (intros ? ? ?; in_reasoning; cpx).
  rewrite lsubstRet_c by assumption.
  rewrite lsubstKlam_c; [| assumption| noRepDis].
  rewrite lsubstRet_c by assumption.
  rewrite lsubstKlam_c; [| assumption| noRepDis].
  rewrite lsubstCall_c by assumption.
  do 3 rewrite lsubst_vterm. simpl.
  rewrite <- beq_var_refl.
  rewrite not_eq_beq_var_false;[| noRepDis].
  rewrite not_eq_beq_var_false;[| noRepDis].
  rewrite lsubst_trivial3.
  Focus 2. 
    setoid_rewrite in_single_iff.
    intros ? ? ?. cpx. rewrite Hcl.
    split;[disjoint_reasoningv|].
    rewrite cps_cvt_aux_fvars;[| ntwfauto|]; rewrite Hcle0; [ tauto | eauto ].
  rewrite lsubst_trivial3.
  Focus 2. 
    setoid_rewrite in_single_iff.
    intros ? ? ?. cpx. rewrite Hcl.
    split;[disjoint_reasoningv|].
    rewrite cps_cvt_aux_fvars; [| ntwfauto|]; rewrite Hcle; [ tauto | eauto ].
    
  clear Hcs.
  match goal with
  [|- context [Ret_c _ ?k]] => assert (closed k) as Hclk;
    [|  assert (sub_range_sat [(fresh_var lv , k)] closed) as Hcs by
        (intros ? ? ?; in_reasoning; cpx)]
  end.
    unfold closed. simpl. autorewrite with list core.
    apply null_iff_nil.
    rewrite cps_cvt_aux_fvars;[| ntwfauto|];  rewrite Hcle; [  | eauto ].
    apply null_iff_nil. simpl. rewrite Hcl. simpl.
    unfold remove_nvars. simpl.
    repeat match goal with
    [ |- context [eq_var_dec ?a ?b] ] 
      => destruct (eq_var_dec a b); simpl; [try reflexivity| try noRepDis]
    end.

  rewrite IHHe1; [| assumption]. simpl. clear IHHe1.
  unfold cps_cvt_lambda.
  rewrite eval_ret. simpl.
  unfold subst.
  rewrite lsubstRet_c by assumption.
  rewrite lsubst_vterm. simpl.
  rename Hcs into Hcsss.
  simpl. rename Hclk into Hclkk.
  match goal with
  [|- context [Ret_c _ (lsubst ?k _)]] => assert (closed k) as Hclk;
    [|  assert (sub_range_sat [(kv1 , k)] closed) as Hcs by
        (intros ? ? ?; in_reasoning; cpx)]
  end.
    unfold closed. simpl. autorewrite with list core.
    apply null_iff_nil. pose proof Hss as Hssb.
    apply null_iff_nil, null_remove_nvars_subsetv in Hss.
    rewrite (cons_as_app _ x []).
    rewrite cps_cvt_aux_fvars;
      [| apply' eval_preseves_wf He1; ntwfauto; fail
       | rewrite cons_as_app;
          apply subset_app_r; inauto].
    apply null_iff_nil. simpl.
    rewrite remove_nvars_app_r, Hssb. simpl.
    rewrite remove_nvars_comm, remove_nvars_eq. reflexivity.

  rewrite substKlam_cTrivial2 by  assumption.
  autorewrite with SquiggleLazyEq.
  rewrite eval_ret. simpl.
  unfold subst.
  rewrite lsubstRet_c by assumption.
  rewrite lsubstKlam_c; [| assumption| noRepDis].
  rewrite lsubstCall_c by assumption.
  do 2 rewrite lsubst_vterm. simpl.
  rewrite <- beq_var_refl.
  rewrite not_eq_beq_var_false;[| noRepDis].
  rewrite lsubst_trivial2_cl;[| assumption | 
      apply null_iff_nil; rewrite cps_cvt_aux_fvars; [ | ntwfauto|]; rewrite Hcle; eauto].
  rewrite lsubst_trivial2_cl;[| assumption | assumption].
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
    simpl. autorewrite with list core.
    rewrite Hclkb, Hcl. simpl.
    rewrite remove_nvars_eq. reflexivity.
  
  clear Hcs.
  rewrite IHHe2 by assumption. clear IHHe2.
  pose proof (cps_val v2 lv Hss2) as Hv.
  simpl in Hv.
  dimp Hv;[eauto using eval_yields_value'|].
  clear Hv. rename hyp into Hv.
  unfold cps_cvt in Hv.
  rewrite Hv. clear Hv.
  rename Hclk into Hclk3b.
  match goal with
  [|- context [Ret_c _ ?k]] => assert (closed k) as Hclk;
    [assumption |  assert (sub_range_sat [(fresh_var lv , k)] closed) as Hcs by
        (intros ? ? ?; in_reasoning; cpx)]
  end.
  rewrite eval_ret. simpl. unfold subst. 
  rewrite lsubstRet_c by assumption.
  rewrite lsubst_vterm. simpl.
  assert (closed (cps_cvt_val' cps_cvt_aux lv v2)) as Hc2v by 
    (ntwfauto; eauto using cps_cvt_val_closed, eval_preseves_wf).
  rewrite lsubst_trivial2_cl; [| assumption | 
    try assumption
      ].
  clear Hcs.
  match goal with
  [|- context [Ret_c _ ?kk]] => 
      assert (sub_range_sat [(kv2 , kk)] closed)
       as Hcs by
        (intros ? ? ?; in_reasoning; cpx)
  end.

  autorewrite with SquiggleLazyEq.
  rewrite eval_ret.
  simpl. unfold subst.
  simpl.
  rewrite lsubstCall_c by assumption.
  rewrite lsubst_vterm. simpl.
  rewrite <- beq_var_refl. simpl.
  do 2 (rewrite lsubst_trivial2_cl;[| assumption | 
    assumption
      ]).
  rewrite eval_call. simpl.
  unfold subst.
  do 2 (rewrite lsubstRet_c by 
        (intros ? ? ?; in_reasoning; cpx)).
  rewrite lsubst_trivial2_cl;[|
     (intros ? ? ?; in_reasoning; cpx) | 
      ].
  Focus 2 .
    unfold closed. rewrite fvars_lsubst1; simpl;
      [| (intros ? ? ?; in_reasoning; cpx)].
    apply null_iff_nil.
    rewrite cps_cvt_aux_fvars; 
       [ apply null_iff_nil; assumption
        | apply' eval_preseves_wf He1; ntwfauto; fail | ].
    apply null_remove_nvars_subsetv, null_iff_nil.
    inauto.
    intros xx.  specialize (Hss xx). tauto.
  rewrite lsubst_vterm.
  simpl.
  pose proof (fresh_var_not_in (x::lv)) as Hf.
  simpl in Hf.
  rewrite not_eq_beq_var_false;[| auto].
  clear Hf.
  rewrite lsubst_vterm. 
  simpl. rewrite <- beq_var_refl.
  rewrite eval_c_subst_commute; auto;
    [refl
      | ntwfauto ; eauto using eval_preseves_wf
      |eapply eval_yields_value'; eauto].


(* constructor *)
- 
Abort.



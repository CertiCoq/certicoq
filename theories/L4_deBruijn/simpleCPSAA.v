
(** coqide -R /path/to/SquiggleLazyEq SquiggleLazyEq 
https://github.com/aa755/SquiggleLazyEq

This file does NOT fully compile yet.
*)

(** CPS conversion for a language with nominal style variable bindings.
We use the 
SquiggleLazyEq library for generically defined substitution, alpha equality (and soon, a contextual equivalence)
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


Class Substitute (v:Type) (t:Type) := { substitute : v -> NVar -> t -> t }.


(** Notation for substitution. *)
Notation "M { j := N }" := (substitute N j M) (at level 10, right associativity).

Instance ExpSubstitute : Substitute NTerm NTerm :=
  { substitute := fun rep x t => subst t x rep}.
(*
Instance ExpsSubstitute : Substitute exp (list exp) :=
  { substitute := substs}.
Instance BranchSubstitute : Substitute exp (dcon * N * exp) :=
  { substitute := subst_branch}.
Instance BranchesSubstitute : Substitute exp (list (dcon * N * exp)) := 
  { substitute := subst_branches}.
*)




(** Big-step evaluation for [exp]. *)
Inductive eval : NTerm -> NTerm -> Prop :=
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
| eval_Proj_e : forall xf e es n e',
                  eval e (Fix_e xf es) ->
                  select n es = Some e' ->
                  eval (Proj_e e n) (e'{xf:=Fix_e xf es}).

(** Evaluation preserves closedness.*)
Lemma eval_preserves_closed :
  forall e v, eval e v ->  closed e -> closed v.
Proof.
  intros ? ? He. unfold closed. induction He; try auto;
  simpl in *;autorewrite with core list in *.
  - intro Hc. 
    apply app_eq_nil in Hc. repnd.
    apply_clear IHHe1 in Hc0.
    apply_clear IHHe2 in Hc.
    apply IHHe3.
    unfold subst.
    rewrite fvars_lsubst1; auto.
    intros  ? ? Hin. in_reasoning. inverts Hin. subst. auto.

  - rename H into Hl. rename H0 into H1i. rename H1 into H2i.
    change es  with (fst (es, vs)).
    change vs  with (snd (es, vs)) at 2.
    apply combine_split in Hl.
    rewrite <- Hl.
    rewrite fst_split_as_map, snd_split_as_map.
    repeat rewrite flat_map_map.
    repeat rw flat_map_empty.
    intros Hf ? Hin. specialize (Hf _ Hin). unfold compose in *. 
    simpl in *. autorewrite with core list in *.
    destruct a.
    eauto.

  - simpl. intros Hf. apply IHHe2.
    unfold subst.
    apply app_eq_nil in Hf.
    rewrite fvars_lsubst1;[tauto|].
    unfold closed. simpl.
    intros ? ? Hin. dorn Hin;[| contradiction].
    inverts Hin. tauto.

  - intros Hf. apply_clear IHHe2.
    destruct e' as [lv nt].
    apply app_eq_nil in Hf. repnd.
    apply_clear IHHe1 in Hf0.
    rewrite flat_map_map in Hf.
    rw flat_map_empty in Hf.
    revert H. destFind; intro Hdf; [| discriminate].
    repnd.
    apply_clear Hf in Heqsnl0. invertsn Hdf.
    destruct bss as [xxx brbt]. simpl in Hdf. subst.
    apply andb_true_iff, proj1,beq_nat_true in Heqsnl.
    unfold compose in Heqsnl0. simpl in *.
    apply closed_bt_implies; auto;[|rewrite <- Heqsnl;refl].
    rewrite flat_map_map in Hf0.
    rw flat_map_empty in Hf0.
    cpx.

- intros Hf. unfold subst.
  apply_clear IHHe in Hf.
  rewrite fvars_lsubst1.
  + rewrite flat_map_map in Hf; simpl.
    rw flat_map_empty in Hf. unfold compose in Hf. simpl in Hf.
    apply select_in in H. eauto.
  + intros ? ? Hin. in_reasoning. inverts Hin. apply Hf.
Qed.

(** Characterize values *)
Inductive is_value : NTerm -> Prop :=
| var_is_value : forall i, is_value (vterm i)
| lam_is_value : forall x e, is_value (Lam_e x e)
| con_is_value : forall d es, are_values es -> is_value (Con_e d es)
(** Unlike in Nuprl, fix is a value.*)
| fix_is_value : forall xf es, is_value (Fix_e xf es)
with are_values : list NTerm -> Prop :=
| nil_are_values : are_values nil
| cons_are_values : forall e es, is_value e -> are_values es ->
                                 are_values (e::es).
Scheme is_value_ind2 := Induction for is_value Sort Prop
with are_values_ind2 := Induction for are_values Sort Prop.
Combined Scheme my_is_value_ind from is_value_ind2, are_values_ind2.
Hint Constructors is_value are_values.

(** Show that evaluation always yields a value. 
Lemma eval_yields_value' :
  (forall e v, eval e v -> is_value v) /\
  (forall es vs, evals es vs -> are_values vs).
Proof.
  apply my_eval_ind ; simpl ; intros ; auto ; try constructor ; auto.
Qed.
*)

Lemma eval_yields_value e v : eval e v -> is_value v.
Admitted.
Hint Resolve eval_yields_value.


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
| eval_Call_c : forall xk x c v1 v2 v',
                  eval_c (c {xk:=v1}{x:=v2}) v' -> 
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
  forall x c v v', eval_c (Ret_c (KLam_c x c) v) v' <-> eval_c (c{x := v}) v'.
Proof.
  intros. split ; intro. inversion H. subst ; auto. constructor ; auto.
Qed.

(** Useful for rewriting. 
Lemma eval_call :
  forall c v1 v2 v',
    eval_c (Call_c (Lam_c c) v1 v2) v' <-> eval_c (c{0:=v1}{0:=v2}) v'.
Proof.
  intros ; split ; intro. inversion H ; subst ; auto. constructor ; auto.
Qed.

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


(*
Definition are_valuesb := are_valuesb' is_valueb.
Lemma is_valueb_corr' :
  (forall e, is_valueb e = true <-> is_value e) /\
  (forall es, are_valuesb es = true <-> are_values es) /\
  (forall bs: list (branch exp), True).
Proof.
  apply my_exp_ind ; simpl ; intros ; split ; intros ; auto ;
  try discriminate. inversion H1. constructor. rewrite <- H. auto.
  inversion H0 ; subst. rewrite H. auto. inversion H1. inversion H1.
  inversion H0 ; try discriminate.
  destruct (is_valueb e) ; try discriminate. constructor. apply H ; auto.
  apply H0 ; auto. inversion H1 ; subst.
  destruct (is_valueb e). tauto. apply H. auto.
Qed.

Definition is_valueb_corr := proj1 is_valueb_corr'.
Definition are_valuesb_corr := proj1 (proj2 is_valueb_corr').
Hint Rewrite is_valueb_corr.
Hint Rewrite are_valuesb_corr.
Hint Resolve is_valueb_corr.
Hint Resolve are_valuesb_corr.

Fixpoint list_to_indices (es:list exp) : list val_c :=
  match es with
    | nil => nil
    | e::es => (KVar_c (N.of_nat (List.length es)))::(list_to_indices es)
  end.
*)
(** The inner, naive CBV CPS translation.  This introduces a lot of 
    administrative reductions, but simple things first.  Importantly,
    things that are already values are treated a little specially.  
    This ensures a substitution property 
    [cps_cvt(e{x:=v}) = (cps_cvt e){x:=(cps_vt_val v)}].
 *)
 
Notation "λ x . y" := (Lam_c x y) (at level 100).
Notation "λ' x . y" := (KLam_c x y) (at level 100).
Section CPS_CVT.
  (* recursive call below *)
  Variable cps_cvt : NTerm -> CTerm (*val_c *).
  
  Definition cps_cvt_bterm (b:BTerm) : CBTerm :=
  match b with
  | bterm vars nt => bterm vars (cps_cvt nt)
  end.

  (** the KLam_c was manually added. unlike now, fix previously implicitly bound var*)
  Definition cps_cvt_fn_list' (es: list BTerm) : list CBTerm :=
    map (fun b => 
            let e := get_nt b in
            let vars := get_vars b in 
            let kv := fresh_var (free_vars e) in 
                    bterm vars (KLam_c kv (Ret_c (cps_cvt e) (vterm kv))) ) es.

  Fixpoint cps_cvt_val' (e:NTerm) : CTerm :=
    match e with
      | vterm n => vterm n
      | terms.oterm (opid.Can NLambda) [bterm [x] b] => 
          let kv := fresh_var (free_vars b) in
             KLam_c kv (Lam_c x (Ret_c (cps_cvt b) (vterm kv)))
      | terms.oterm (opid.Can (NDCon d _)) lb => 
            Con_c d (List.map (cps_cvt_val' ∘ get_nt) lb)
      | terms.oterm (opid.Can (NFix nargs)) lb =>
          terms.oterm (CCan (CFix nargs))
             (cps_cvt_fn_list' lb)
      | _ => vterm nvarx (* impossible *)
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


  Definition cps_cvt_branch' (kv : NVar) (bt: BTerm) : CBTerm :=
    match bt with
    | bterm vars nt =>
        (bterm vars (Ret_c (cps_cvt nt) (vterm kv)))
    end.

 Definition cps_cvt_branches' (kv : NVar) : (list BTerm) ->
    list CBTerm :=
  List.map (cps_cvt_branch' kv).
    

End CPS_CVT.

(** make a wrapper that precomputes fve and passes to this function.  We dont want to do the fvar computation
recursively*)
Fixpoint cps_cvt (e:NTerm) : CTerm :=
  let fve := free_vars e in (* the var library can have a way to compress a list of vars to a range, and have an alternate more efficient free vars function*)
  if is_valueb e then let kv := fresh_var fve in KLam_c kv (Ret_c (vterm kv) (cps_cvt_val' cps_cvt e)) else
  match e with
    | terms.oterm (opid.NCan NApply) [bterm [] e1; bterm [] e2] => 
      (* cont \k.(ret [e1] (cont \v1.(ret [e2] (cont \v2.call v1 k v2)))) *)
      let kvars := projT1 (fresh_vars 3 fve) in 
      let k := nth 0 kvars nvarx in  
      let v1 := nth 1 kvars nvarx in  
      let v2 := nth 2 kvars nvarx in  
       KLam_c k 
        (Ret_c (cps_cvt e1) (* e1 may not already be a lambda *)
               (KLam_c v1 (Ret_c (cps_cvt e2)
                                  (KLam_c v2 (Call_c (vterm v1) (vterm k) (vterm v2))))))
    | terms.oterm (opid.Can (NDCon d nargs)) es => 
        let kvars := projT1 (fresh_vars (S (length es)) fve) in
        let k := hd nvarx kvars  in
        KLam_c k (cps_cvts' cps_cvt (tail kvars) es (Ret_c (vterm k)
                                                          (Con_c d (map vterm kvars))))
    | terms.oterm (opid.NCan (NMatch brl)) ((bterm [] discriminee)::brr) => 
      let kvars := projT1 (fresh_vars 2 fve) in 
      let k := nth 0 kvars nvarx in
      let kd := nth 1 kvars nvarx in
      let brrc :=  (bterm [] (vterm kd))::(cps_cvt_branches' cps_cvt k brr) in
      KLam_c k (Ret_c (cps_cvt discriminee)
                      (KLam_c kd 
                              (coterm (CNCan (CMatch brl)) brrc)))
    | terms.oterm (opid.NCan NLet) [bterm [] e1, bterm [x] e2] => 
      (* translate as if it were App_e (Lam_e e1) e2. unlike the general cas of App, here the function
        is already a value *)
      let kvars := projT1 (fresh_vars 3 fve) in 
      let k := nth 0 kvars nvarx in  
      let kvl := nth 1 kvars nvarx in  
      let v2 := nth 2 kvars nvarx in  
       KLam_c k (Ret_c (cps_cvt e2)
                       (KLam_c v2 (Call_c (KLam_c kvl (Lam_c x (Ret_c (cps_cvt e2) (vterm kvl))))
                                          (vterm k) 
                                          (vterm v2))))
    | terms.oterm (opid.NCan (NProj i)) [bterm [] e] =>
      let kvars := projT1 (fresh_vars 2 fve) in 
      let k := nth 0 kvars nvarx in  
      let ke := nth 1 kvars nvarx in  
        KLam_c k (Ret_c (cps_cvt e) 
                        (KLam_c ke (Proj_c (vterm ke) i (vterm k))))
    | _ => vterm nvarx (* impossible *)
  end.

Definition cps_cvt_val := cps_cvt_val' cps_cvt.
Definition cps_cvts := cps_cvts' cps_cvt.
Definition cps_cvt_vals := List.map cps_cvt_val.
Definition cps_cvt_branch := cps_cvt_branch' cps_cvt.
Definition cps_cvt_branches := cps_cvt_branches' cps_cvt.
Definition cps_cvt_fn_list := cps_cvt_fn_list' cps_cvt.

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

(** Relationship between specialized CPS conversion for values
    and the original translation. *)
Lemma are_values_append : forall es1 es2, (are_values es1 /\ are_values es2) <->
                                          are_values (es1 ++ es2).
Proof.
  induction es1 ; simpl ; intros ; split ; intro.
  destruct H ; auto.
  destruct H ; auto.
  destruct H. inversion H. subst. constructor ; auto. rewrite <- IHes1. auto.
  inversion H ; subst. rewrite <- IHes1 in H3. destruct H3. split ; auto.
Qed.
Hint Resolve are_values_append.
  
Lemma cps_val' :
  (forall e, is_value e ->
             cps_cvt e = Cont_c (Ret_c (KVar_c 0) (cps_cvt_val e))) /\
  (forall es, are_values es ->
     forall d es', are_values es' -> 
        cps_cvt (Con_e d (es' ++ es)) =
        Cont_c (Ret_c (KVar_c 0) (Con_c d (cps_cvt_vals (es' ++ es))))).
Proof.
  apply my_is_value_ind ; intros ; auto.
  specialize (H d nil). replace ([] ++ es) with es in H ; auto.
  repeat rewrite app_nil_r. simpl. fold are_valuesb.
  rewrite (proj2 (are_valuesb_corr es') H). auto.
  simpl. fold are_valuesb.
  rewrite (proj2 (are_valuesb_corr (es' ++ (e::es)))) ; auto.
  rewrite <- are_values_append. auto.
Qed.

Lemma cps_val :
  forall v, is_value v -> cps_cvt v = Cont_c (Ret_c (KVar_c 0) (cps_cvt_val v)).
Proof.
  intros. apply (proj1 cps_val'). auto.
Qed.

Lemma cps_vals :
  forall vs d, are_values vs ->
               cps_cvt (Con_e d vs) =
               Cont_c (Ret_c (KVar_c 0) (Con_c d (cps_cvt_vals vs))).
Proof.
  intros.
  specialize (proj2 cps_val' vs H d nil). simpl. auto.
Qed.

Lemma list_to_indices_wf :
  forall es i j, vals_wf i (j + (N.of_nat (length es))) (list_to_indices es).
Proof.
  Opaque N.of_nat.
  induction es ; simpl ; intros ; auto.
  repeat constructor. lia. 
  replace (j + (N.of_nat (S (length es)))) with ((1+j) + (N.of_nat (length es))) ; auto ; lia.
Qed.

(** The CPS translation produces continuation-closed terms. *)
Lemma cps_kvar_closed' :
  (forall i e, exp_wf i e ->
     val_wf i 0 (cps_cvt e) /\ (is_value e -> val_wf i 0 (cps_cvt_val e))) /\
  (forall i es, exps_wf i es ->
     (forall j c, cps_wf i (j + (N.of_nat (length es))) c ->
                  cps_wf i j (cps_cvts es c)) /\
     (are_values es -> vals_wf i 0 (cps_cvt_vals es)) /\
     (forall i', i = 2 + i' -> fn_list_wf i' 0 (cps_cvt_fn_list es))) /\
  (forall i bs, branches_wf i bs -> cpsbranches_wf i 2 (cps_cvt_branches bs)).
Proof.
  apply my_exp_wf_ind ; simpl ; intros ; auto.
  - repeat constructor ; auto.
  - destruct H. repeat constructor.
    apply (val_weaken _ _ _ H 0 2). apply (val_weaken _ _ _ H 0 1).
  - destruct H. destruct H0. split.
    + constructor. constructor.
      apply (val_weaken _ _ _ H 0 1).
      constructor. constructor.
      apply (val_weaken _ _ _ H0 0 2).
      repeat constructor.
    + intros. inversion H3.
  - destruct H. destruct H0. fold are_valuesb.
    generalize (are_valuesb_corr es). intro.
    destruct (are_valuesb es).
    + specialize (H0 (proj1 H2 eq_refl)). repeat constructor; try auto.
      * apply (vals_weaken _ _ _ H0 0 1). 
    + split.
      * constructor. apply H. repeat constructor. lia.
        replace (1+0) with 1 ; auto.
        eapply list_to_indices_wf.
      * intros. inversion H3 ; subst.
        destruct H2. specialize (H4 H5). discriminate.
  - destruct H. split.
    + repeat constructor ; auto. apply (val_weaken _ _ _ H 0 1).
    + intro. inversion H2.
  - destruct H ; destruct H0. split.
    + repeat constructor ; auto.
      apply (val_weaken _ _ _ H 0 1). apply (val_weaken _ _ _ H0 0 3).
    + intro. inversion H3.
  - destruct H. destruct H0. split. 
    + repeat constructor ; auto.
      specialize (H1 i eq_refl).
      apply (fn_list_weaken _ _ _ H1 0 1). 
    + intros. constructor. apply H1 ; auto.
  - destruct H. split. repeat constructor ; auto.
    apply (val_weaken _ _ _ H 0 1). intro. inversion H1.
  - split ; auto. intros. rewrite (N.add_0_r) in H. auto.
  - destruct H ; destruct H0. destruct H2. split ; intros.
    + repeat constructor. 
      * generalize (val_weaken _ _ _ H 0 j). rewrite (N.add_0_r). auto.
      * apply H0.
        replace (j + N.of_nat (S (length es)))
        with (1 + j + N.of_nat (length es)) in H4 ; auto. lia.
    + split ; intros.
      * inversion H4 ; subst ; auto.
      * subst. repeat constructor ; auto.
        apply (val_weaken _ _ _ H 0 1).  
  - constructor ; auto. destruct H. constructor.
    + apply (val_weaken _ _ _ H 0 2). 
    + constructor. lia.
Qed.

Lemma cps_kvar_closed i e : exp_wf i e -> val_wf i 0 (cps_cvt e).
  intros. specialize (proj1 cps_kvar_closed' _ _ H). tauto.
Qed.
Lemma cps_val_kvar_closed i e : exp_wf i e -> is_value e -> val_wf i 0 (cps_cvt_val e).
  intros. apply (proj2 (proj1 cps_kvar_closed' _ _ H) H0).
Qed.
Lemma cps_vals_kvar_closed i es : exps_wf i es -> are_values es -> vals_wf i 0 (cps_cvt_vals es).
  intros.
  apply (proj1 (proj2 (proj1 (proj2 cps_kvar_closed') i es H)) H0).
Qed.
Lemma cps_fn_list_closed i es : exps_wf (2 + i) es -> fn_list_wf i 0 (cps_cvt_fn_list es).
  intros.
  apply (proj2 (proj2 (proj1 (proj2 cps_kvar_closed') (2 + i) es H)) _ eq_refl).
Qed.
Lemma cps_branches_closed i bs : branches_wf i bs -> cpsbranches_wf i 2 (cps_cvt_branches bs).
  intros. apply (proj2 (proj2 cps_kvar_closed') i bs H).
Qed.
Hint Resolve cps_kvar_closed cps_val_kvar_closed cps_vals_kvar_closed cps_fn_list_closed.

(** Eliminate a continuation substitution when the index we are substituting
    for is out of range. *)
Lemma ksubst_closed :
  (forall i j (e:cps), cps_wf i j e -> forall k, k >= j -> forall v, e[k:=v] = e) /\
  (forall i j (w:val_c), val_wf i j w -> forall k, k >= j -> forall v, w[k:=v] = w) /\
  (forall i j (ws:list val_c), vals_wf i j ws -> forall k, k >= j -> forall v,ws[k:=v] = ws) /\
  (forall i j (bs:list (branch cps)), cpsbranches_wf i j bs ->
                                      forall k, k >= j -> forall v,bs[k:=v] = bs) /\
  (forall i j (cs:list cps), fn_list_wf i j cs -> forall k, k >= j -> forall v, cs[k:=v] = cs).
Proof.
  apply my_wf_ind ; intros ; simpl ; auto ; 
  repeat 
  match goal with
    | [ H : forall k, k >= ?j -> _, H1 : ?k >= ?j |- _ ] => rewrite (H _ H1) ; auto
    | _ => idtac
  end.
  fold ksubst_branches. rewrite H0 ; auto.
  repeat if_split.
  rewrite (H (1+k)) ; auto ; lia.
  rewrite (H (1+k)) ; auto ; lia.
  fold ksubst_vals. rewrite H ; auto.
  fold ksubst_fn_list. rewrite H ; auto.
  rewrite H ; auto. lia.
Qed.

Definition ksubst_closed_cps := proj1 ksubst_closed.
Definition ksubst_closed_val := proj1 (proj2 ksubst_closed).
Definition ksubst_closed_vals := proj1 (proj2 (proj2 ksubst_closed)).
Definition ksubst_closed_branches := proj1 (proj2 (proj2 (proj2 ksubst_closed))).
Definition ksubst_closed_fn_list := proj2 (proj2 (proj2 (proj2 ksubst_closed))).

(** Eliminate a user substitution when the index we are substituting for is
    out of range. *)
Lemma usubst_closed :
  (forall i j (e:cps), cps_wf i j e ->
       forall k, k >= i -> forall v, e{k:=v} = e) /\
  (forall i j (w:val_c), val_wf i j w ->
       forall k, k >= i -> forall v, w{k:=v} = w) /\
  (forall i j (ws:list val_c), vals_wf i j ws ->
       forall k, k >= i -> forall v, ws{k:=v} = ws) /\
  (forall i j (bs:list (branch cps)), cpsbranches_wf i j bs ->
       forall k, k >= i -> forall v,bs{k:=v} = bs) /\
  (forall i j (cs:list cps), fn_list_wf i j cs ->
       forall k, k >= i -> forall v,cs{k:=v} = cs).
Proof.
 apply my_wf_ind ; intros ; simpl ; auto ; 
  repeat 
  match goal with
    | [ H : forall k, k >= ?j -> _, H1 : ?k >= ?j |- _ ] =>
                rewrite (H _ H1) ; auto
    | _ => idtac
  end.
 - fold usubst_branches. rewrite H0 ; auto.
 - repeat if_split.
 - rewrite (H (1+k)) ; auto ; lia.
 - fold usubst_vals ; rewrite H ; auto.
 - fold usubst_fn_list. rewrite H ; auto.
 - apply f_equal2; try reflexivity.
   + apply f_equal2; try reflexivity.
     * rewrite H; auto. admit.
 - rewrite H. auto. reflexivity.
   *
rewrite H ; auto. lia.
  rewrite H ; auto ; lia.
Qed.
Definition usubst_closed_val := proj1 (proj2 usubst_closed).

(** We can eliminate substitution for a continuation variable in a CPS'd term. *)
Lemma cps_cvt_ksubst :
  forall i e,
    exp_wf i e ->
    forall k v, 
      (cps_cvt e)[k := v] = cps_cvt e.
Proof.
  intros. rewrite (ksubst_closed_val _ _ _ (cps_kvar_closed _ _ H)) ; auto.
  lia.
Qed.
Hint Rewrite cps_cvt_ksubst.

(** Eliminating user shifts when out of range. *)
Lemma ushift_closed' :
  (forall i j e, cps_wf i j e -> forall k, ushift_cps k i e = e) /\
  (forall i j v, val_wf i j v -> forall k, ushift_val k i v = v) /\
  (forall i j vs, vals_wf i j vs -> forall k, ushift_vals k i vs = vs) /\
  (forall i j bs, cpsbranches_wf i j bs -> forall k, ushift_branches k i bs = bs) /\
  (forall i j cs, fn_list_wf i j cs -> forall k, ushift_fn_list k i cs = cs).
Proof.
  apply my_wf_ind ; simpl ; intros ;
  fold ushift_branches ; fold ushift_vals ; fold ushift_fn_list ; try congruence.
  if_split. rewrite H ; rewrite H0 ; auto.
Qed.

(** Eliminating continuation shifts when out of range. *)
Lemma kshift_closed' :
  (forall i j e, cps_wf i j e -> forall k, kshift_cps k j e = e) /\
  (forall i j v, val_wf i j v -> forall k, kshift_val k j v = v) /\
  (forall i j vs, vals_wf i j vs -> forall k, kshift_vals k j vs = vs) /\
  (forall i j bs, cpsbranches_wf i j bs -> forall k, kshift_branches k j bs = bs) /\
  (forall i j cs, fn_list_wf i j cs -> forall k, kshift_fn_list k j cs = cs).
Proof.
  apply my_wf_ind ; simpl ; intros ;
  fold kshift_branches; fold kshift_vals ; fold kshift_fn_list ; try congruence.
  if_split. rewrite H ; rewrite H0 ; auto.
Qed.

Definition kshift_closed_cps := proj1 kshift_closed'.
Definition kshift_closed_val' := proj1 (proj2 kshift_closed').
Definition kshift_closed_vals := proj1 (proj2 (proj2 kshift_closed')).
Definition kshift_closed_branches := proj1 (proj2 (proj2 (proj2 kshift_closed'))).
Definition kshift_closed_fn_list := proj2 (proj2 (proj2 (proj2 kshift_closed'))).

(** Eliminating user shifts on closed values. *)
Lemma ushift_closed_val :
  forall v, val_wf 0 0 v -> forall k l, ushift_val k l v = v.
Proof.
  intros.
  assert (val_wf l 0 v). generalize (val_weaken _ _ _ H l 0). simpl.
  replace (l + 0) with l ; try lia. auto.
  eapply (proj1 (proj2 ushift_closed')) ; eauto.
Qed.

(** Eliminating continuation shifts on closed values. *)
Lemma kshift_closed_val :
  forall v, val_wf 0 0 v -> forall k l, kshift_val k l v = v.
Proof.
  intros.
  assert (val_wf 0 l v). generalize (val_weaken _ _ _ H 0 l). simpl.
  replace (l + 0) with l ; auto ; lia.
  eapply kshift_closed_val' ; eauto.
Qed.  

(** A preservation theorem for substitution of a closed value for a
    user variable. *)
Lemma usubst_preserves_wf' :
  (forall i' j e, cps_wf i' j e ->
                  forall i, i' = 1+i -> 
                            forall v, val_wf 0 0 v -> forall k, k <= i -> cps_wf i j (e{k := v})) /\
  (forall i' j w, val_wf i' j w ->
                  forall i, i' = 1+i -> 
                            forall v, val_wf 0 0 v -> forall k, k <= i -> val_wf i j (w{k := v})) /\
  (forall i' j ws, vals_wf i' j ws ->
                  forall i, i' = 1+i -> 
                            forall v, val_wf 0 0 v -> forall k, k <= i -> vals_wf i j (ws{k := v})) /\
  (forall i' j bs, cpsbranches_wf i' j bs ->
                   forall i, i' = 1+i ->
                             forall v, val_wf 0 0 v -> forall k, k <= i -> cpsbranches_wf i j (bs{k:=v})) /\
  (forall i' j cs, fn_list_wf i' j cs ->
                   forall i, i' = 1+i ->
                             forall v, val_wf 0 0 v -> forall k, k <= i -> fn_list_wf i j (cs{k:=v})).
Proof.
  apply my_wf_ind ; simpl ; intros ; subst ; repeat
  match goal with
    | [ H : forall i, 1+?j = 1+i -> _ |- _ ] => specialize (H _ eq_refl)
    | _ => auto
  end.
  repeat if_split ; try (constructor ; auto ; lia). rewrite ushift_closed_val ; auto.
  specialize (H _ H1). constructor. apply H. lia.
  constructor ; auto. specialize (H (n + i0)). replace (n + (1 + i0)) with (1 + (n + i0)) in H ;
    [idtac | lia]. specialize (H eq_refl _ H2). apply (H (n+k)). lia.
  constructor. apply (H (2 + i0)) ; auto ; try lia.
  apply H0 ; auto.
Qed.

Definition usubst_preserves_wf_cps := proj1 usubst_preserves_wf'.
Definition usubst_preserves_wf_val := proj1 (proj2 usubst_preserves_wf').

(** A preservation theorem for substitution of a closed value for a
    continuation variable. *)
Lemma ksubst_preserves_wf' :
  (forall i j' e, cps_wf i j' e ->
                  forall j, j' = 1+j -> 
                            forall v, val_wf 0 0 v -> forall k, k <= j -> cps_wf i j (e[k := v])) /\
  (forall i j' w, val_wf i j' w ->
                  forall j, j' = 1+j -> 
                            forall v, val_wf 0 0 v -> forall k, k <= j -> val_wf i j (w[k := v])) /\
  (forall i j' ws, vals_wf i j' ws ->
                  forall j, j' = 1+j -> 
                            forall v, val_wf 0 0 v -> forall k, k <= j -> vals_wf i j (ws[k := v])) /\
  (forall i j' bs, cpsbranches_wf i j' bs ->
                   forall j, j' = 1+j ->
                             forall v, val_wf 0 0 v -> forall k, k <= j -> cpsbranches_wf i j (bs[k:=v])) /\
  (forall i j' cs, fn_list_wf i j' cs ->
                   forall j, j' = 1+j ->
                             forall v, val_wf 0 0 v -> forall k, k <= j -> fn_list_wf i j (cs[k:=v])).
Proof.
  apply my_wf_ind ; simpl ; intros ; subst ; repeat
  match goal with
    | [ H : forall i, 1+?j = 1+i -> _ |- _ ] => specialize (H _ eq_refl)
    | _ => auto
  end.
  repeat if_split ; try (constructor ; auto ; lia). rewrite kshift_closed_val ; auto.
  constructor. apply H ; auto ; lia.
  constructor ; apply H ; auto ; lia.
  constructor ; [apply H ; auto ; lia | apply H0 ; auto].
Qed.

Definition ksubst_preserves_wf_cps := proj1 ksubst_preserves_wf'.
Definition ksubst_preserves_wf_branches := proj1 (proj2 (proj2 (proj2 ksubst_preserves_wf'))).

(** Substitution preservation specialized to a 0 index on an CPS expression. *)
Lemma usubst_preserves_wf :
  forall i j e, cps_wf (1+i) j e -> forall v, val_wf 0 0 v -> cps_wf i j (e{0:=v}).
Proof.
  intros. eapply usubst_preserves_wf_cps ; eauto. lia.
Qed.

(** Substitution preservation specialized to a 0 index on an CPS expression. *)
Lemma ksubst_preserves_wf :
  forall i j e, cps_wf i (1+j) e -> forall v, val_wf 0 0 v -> cps_wf i j (e[0:=v]).
Proof.
  intros. eapply ksubst_preserves_wf_cps ; eauto. lia.
Qed.

Lemma find_cps_branch_wf :
  forall i j bs, cpsbranches_wf i j bs ->
                 forall d n c, find_branch d n bs = Some c ->
                               cps_wf (n+i) j c.
Proof.
  induction bs ; simpl ; intros ; try discriminate.
  inversion H ; subst ; clear H. simpl in H0.
  destruct (N.eq_dec d d0) ; subst.
  destruct (N.eq_dec n0 n) ; subst ; try discriminate.
  injection H0 ; intros ; subst ; auto.
  eapply IHbs ; eauto.
Qed.

Lemma usubst_list_preserves_wf :
  forall vs, vals_wf 0 0 vs ->
             forall c, cps_wf (N.of_nat (length vs)) 0 c ->
                       cps_wf 0 0 (usubst_list c vs).
Proof.
  induction vs ; simpl ; intros ; auto.
  inversion H ; subst ; clear H.
  apply (IHvs H6 (usubst_cps a 0 c)).
  eapply usubst_preserves_wf ; eauto.
  replace (1 + N.of_nat (length vs)) with (N.of_nat (S (length vs))) ;
    auto ; lia.
Qed.

Lemma nth_opt_cps_wf :
  forall i j cs, fn_list_wf i j cs -> forall n c, nthopt n cs = Some c -> cps_wf (2+i) (1+j) c.
Proof.
  induction cs ; simpl ; intros. destruct n ; try discriminate.
  inversion H ; subst ; clear H. destruct n ; simpl in *.
  injection H0 ; intros ; subst ; auto.
  apply (IHcs H6 _ _ H0).
Qed.

(** Evaluation of CPS terms preserves closedness. *)
Lemma cps_eval_preserves_wf :
  forall e v, eval_c e v -> cps_wf 0 0 e -> val_wf 0 0 v.
Proof.
  induction 1 ; intros. inversion H ; subst ; auto.
  inversion H0 ; clear H0 ; subst. inversion H5 ; clear H5 ; subst.
  apply IHeval_c. apply ksubst_preserves_wf ; auto.
  inversion H0 ; clear H0 ; subst. inversion H6 ; clear H6 ; subst.
  apply IHeval_c.
  apply usubst_preserves_wf ; auto.
  apply ksubst_preserves_wf ; auto.
  inversion H1 ; subst ; clear H1.
  apply IHeval_c.
  generalize (find_cps_branch_wf _ _ _ H7 _ _ _ H).
  rewrite N.add_0_r. inversion H6 ; subst ; clear H6 ; intros.
  apply usubst_list_preserves_wf ; auto.
  inversion H1 ; subst. clear H1. inversion H6 ; clear H6 ; subst.
  specialize (nth_opt_cps_wf _ _ _ H4 _ _ H). intros.
  apply IHeval_c ; clear IHeval_c. constructor ; auto.
  unfold substitute in *. simpl in *. intros. constructor.
  apply (usubst_preserves_wf_cps 2 1 c H1 1 eq_refl).
  constructor ; auto. lia.
Qed.

(** Getting rid of redundant shifts.  (Duplicate?) *)
Lemma wf_kshift_zero :
  (forall i j e, cps_wf i j e -> forall k l, j <= l -> (kshift_cps k l e) = e) /\
  (forall i j v, val_wf i j v -> forall k l, j <= l -> (kshift_val k l v) = v) /\
  (forall i j vs, vals_wf i j vs -> forall k l, j <= l -> (kshift_vals k l vs) = vs) /\
  (forall i j bs, cpsbranches_wf i j bs -> forall k l, j <= l -> (kshift_branches k l bs) = bs)/\
  (forall i j cs, fn_list_wf i j cs -> forall k l, j <= l -> (kshift_fn_list k l cs) = cs).
Proof.
  apply my_wf_ind ; intros ; simpl ; subst ; auto ;
  try (rewrite H ; auto ; try lia ; rewrite H0 ; auto ; rewrite H1 ; auto).
  if_split.
Qed.

Definition wf_kshift_zero_val := proj1 (proj2 wf_kshift_zero).

Lemma is_valueb_shift' :
  (forall e i j, is_valueb (shift i j e) = is_valueb e) /\ 
  (forall es i j, are_valuesb (shifts i j es) = are_valuesb es) /\
  (forall (bs:list (branch exp)), True).
Proof.
  apply my_exp_ind ; simpl ; intros ; auto. rewrite H. rewrite H0. auto.
Qed.

Definition is_valueb_shift := proj1 is_valueb_shift'.
Definition are_valuesb_shift := proj1 (proj2 is_valueb_shift').

Lemma is_value_shift' :
  (forall e i j, is_value (shift i j e) <-> is_value e) /\ 
  (forall es i j, are_values (shifts i j es) <-> are_values es) /\
  (forall (bs:list (branch exp)), True).
Proof.
  apply my_exp_ind ; simpl ; intros ; split ; intro ; auto ;
  try (inversion H1 ; fail). inversion H0 ; subst. constructor.
  rewrite <- H ; eauto. inversion H0 ; subst. constructor.
  rewrite H ; eauto. inversion H0. inversion H0.
  inversion H1. subst. constructor. rewrite <- H ; eauto.
  rewrite <- H0 ; eauto. inversion H1 ; subst ; constructor. rewrite H ; eauto.
  rewrite H0 ; eauto.
Qed.

Definition is_value_shift := proj1 is_value_shift'.
Definition are_values_shift := proj1 (proj2 is_value_shift').

Lemma length_shift :
  forall es i j, length (shifts i j es) = length es.
Proof.
  intros ; unfold shifts, shifts'. apply map_length.
Qed.

Lemma ushift_list_to_indices :
  forall es i j, ushift_vals i j (list_to_indices es) = list_to_indices (shifts i j es).
Proof.
  induction es ; simpl ; intros ; auto. rewrite length_shift. congruence.
Qed.

(** User variable shifts commute with CPS conversion. *)
Lemma ushift_cps_cvt' :
  (forall e, (forall i j,ushift_val i j (cps_cvt e) = cps_cvt (shift i j e)) /\
                 (is_value e -> forall i j, (ushift_val i j (cps_cvt_val e) =
                                             cps_cvt_val (shift i j e))))
  /\
  (forall es, (forall i j c,
                 ushift_cps i j (cps_cvts es c) = cps_cvts (shifts i j es) (ushift_cps i j c)) /\
              (are_values es -> forall i j, (ushift_vals i j (cps_cvt_vals es) =
                                             cps_cvt_vals (shifts i j es))) /\
              (forall i j,
                 ushift_fn_list i j (cps_cvt_fn_list es) = cps_cvt_fn_list (shifts i (2 + j) es)))
  /\
  (forall bs i j,
     ushift_branches i j (cps_cvt_branches bs) = cps_cvt_branches (shift_branches i j bs)).
Proof.
  apply my_exp_ind ; simpl ; intros ; auto.
  split ; intros.
  rewrite (proj1 H). auto.
  rewrite (proj1 H). auto.
  split ; intros.
  rewrite (proj1 H) ; rewrite (proj1 H0) ; auto.
  inversion H1.
  fold are_valuesb. fold cps_cvt_val. fold cps_cvt_vals.
  split ; intros.
  generalize (proj1 (are_valuesb_corr es)). destruct H. intros.
  rewrite (are_valuesb_shift). destruct (are_valuesb es) ; simpl ; auto.
  rewrite (proj1 H0) ; auto. rewrite H ; auto. simpl. rewrite length_shift.
  rewrite ushift_list_to_indices. auto. inversion H0 ; subst.
  rewrite (proj1 (proj2 H) H2). auto.
  intros. split ; [ intros | intro H1 ; inversion H].
  rewrite (proj1 H). fold ushift_branches. fold shift_branches.
  rewrite H0. auto.
  inversion H1.
  split ; intros.
  rewrite (proj1 H) ; rewrite (proj1 H0) ; auto.
  inversion H1.
  split ; intros.
  fold ushift_fn_list cps_cvt_fn_list shifts.
  rewrite (proj2 (proj2 H)). auto.
  rewrite (proj2 (proj2 H)). auto.
  split ; intros.
  rewrite (proj1 H) ; auto. inversion H0.
  split ; intros.
  rewrite (proj1 H) ; rewrite (proj1 H0) ; auto.
  split ; intros.
  inversion H1 ; subst. clear H1. rewrite (proj2 H H4).
  rewrite (proj1 (proj2 H0) H5). auto. 
  rewrite (proj1 H). rewrite (proj2 (proj2 H0)). auto.
  rewrite (proj1 H) ; auto. rewrite H0 ; auto.
Qed.

Lemma ushift_cps_cvt e i j : ushift_val i j (cps_cvt e) = cps_cvt (shift i j e).
  apply (proj1 (proj1 ushift_cps_cvt' e) i j).
Qed.

Lemma ushift_cps_cvt_val e i j :
  is_value e -> ushift_val i j (cps_cvt_val e) = cps_cvt_val (shift i j e).
Proof.
  intro H. apply (proj2 (proj1 ushift_cps_cvt' e) H i j).
Qed.

Lemma ushift_cps_cvts es i j c :
  ushift_cps i j (cps_cvts es c) = cps_cvts (shifts i j es) (ushift_cps i j c).
Proof.
  apply (proj1 (proj1 (proj2 ushift_cps_cvt') es) i j c).
Qed.

Lemma ushift_cps_cvt_vals es i j :
  are_values es -> ushift_vals i j (cps_cvt_vals es) = cps_cvt_vals (shifts i j es).
Proof.
  intro H. apply (proj1 (proj2 (proj1 (proj2 ushift_cps_cvt') es)) H i j).
Qed.

Lemma ushift_cps_cvt_fn_list es i j :
  ushift_fn_list i j (cps_cvt_fn_list es) = cps_cvt_fn_list (shifts i (2 + j) es).
Proof.
  apply (proj2 (proj2 ((proj1 (proj2 ushift_cps_cvt') es)))).
Qed.
Lemma ushift_cps_cvt_branches bs i j :
  ushift_branches i j (cps_cvt_branches bs) = cps_cvt_branches (shift_branches i j bs).
Proof.
  apply (proj2 (proj2 ushift_cps_cvt')).
Qed.

Lemma is_valueb_subst' :
  forall v, is_value v ->
            (forall e i, is_valueb (subst v i e) = is_valueb e) /\
            (forall es i, are_valuesb (substs v i es) = are_valuesb es) /\
            (forall bs : list (branch exp), True).
Proof.
  intros v H.
  apply my_exp_ind ; simpl ; intros ; auto. repeat if_split.
  rewrite (is_valueb_shift). rewrite (is_valueb_corr v) ; auto.
  rewrite H0. rewrite H1. auto.
Qed.

Lemma is_valueb_subst v e i :
  is_value v -> is_valueb (subst v i e) = is_valueb e.
  intro H. apply (proj1 (is_valueb_subst' v H) e i).
Qed.

Lemma are_valuesb_subst v es i :
  is_value v -> are_valuesb (substs v i es) = are_valuesb es.
  intro H. apply (proj1 (proj2 (is_valueb_subst' v H)) es i).
Qed.
  
Lemma length_substs :
  forall es v j, length (substs v j es) = length es.
Proof.
  unfold substs, substs'. intros. rewrite map_length. auto.
Qed.

Lemma list_to_indices_substs :
  forall es v j, list_to_indices (substs v j es) = list_to_indices es.
Proof.
  induction es ; simpl ; intros ; auto. rewrite length_substs. congruence.
Qed.

Lemma usubst_list_to_indices :
  forall es v j, usubst_vals v j (list_to_indices es) = list_to_indices es.
Proof.
  induction es ; simpl ; intros ; congruence.
Qed.

Lemma wf_list_to_indices :
  forall es, vals_wf 0 (1 + (N.of_nat (length es))) (list_to_indices es).
Proof.
  induction es ; simpl ; repeat constructor ; try lia ; auto.
  generalize (vals_weaken _ _ _ IHes 0 1).
  replace (1 + (1 + N.of_nat (length es))) with (1 + N.of_nat (S (length es))) ;
    auto ; try lia.
Qed.

(** CPS conversion commutes with substitution for user variables. *)
Lemma cps_cvt_comm_usubst':
  forall v, is_value v -> exp_wf 0 v ->
  (forall i e, exp_wf i e ->
    (forall j, j < i ->       
      (usubst_val (cps_cvt_val v) j (cps_cvt e) = cps_cvt (subst v j e))) /\
    (forall j, j < i -> 
      (is_valueb e = true ->        
       (usubst_val (cps_cvt_val v) j (cps_cvt_val e) =
        cps_cvt_val (subst v j e))))) /\
  (forall i es, exps_wf i es ->
     (forall j k c,
        j < i -> cps_wf 0 k c -> 
        usubst_cps (cps_cvt_val v) j (cps_cvts es c) =
        cps_cvts (substs v j es) (usubst_cps (cps_cvt_val v) j c)) /\
     (are_valuesb es = true -> 
      forall j, j < i ->
                usubst_vals (cps_cvt_val v) j (cps_cvt_vals es) =
                cps_cvt_vals (substs v j es)) /\
     (forall j i', i = 2 + i' ->  j < i' ->
                   usubst_fn_list (cps_cvt_val v) j (cps_cvt_fn_list es) =
                   cps_cvt_fn_list (substs v (2+j) es))) /\
  (forall i bs, branches_wf i bs ->
     forall j, j < i -> 
               usubst_branches (cps_cvt_val v) j (cps_cvt_branches bs) =
               cps_cvt_branches (subst_branches v j bs)).
Proof.
  intros v H1 H2.
  apply my_exp_wf_ind ; simpl ; intros ; auto ; try split ; intros ; 
  repeat match goal with [ H : _ /\ _ |- _ ] => destruct H | _ => idtac end ;
  try discriminate.
  repeat if_split.
  rewrite (ushift_cps_cvt_val v) ; auto. rewrite cps_val ; auto.
  apply is_value_shift ; auto.
  repeat if_split. apply ushift_cps_cvt_val ; auto.
  assert (H4: 1+j < 1+i) ; [lia | rewrite (H _ H4); auto].
  assert (H5: 1+j < 1+i) ; [lia | rewrite (H _ H5); auto].
  rewrite H ; auto ; rewrite H0 ; auto. 
  rewrite (are_valuesb_subst) ; auto. fold are_valuesb.
  remember (are_valuesb es) as b. destruct b. simpl.
  fold cps_cvt_val cps_cvt_vals substs.
  rewrite H3 ; auto.
  rewrite list_to_indices_substs ; rewrite length_substs. simpl.
  rewrite (H _ (1+ (N.of_nat (length es)))) ; eauto. simpl. 
  rewrite usubst_list_to_indices ; auto.
  repeat constructor ; try lia. apply wf_list_to_indices.
  rewrite (H4 H3) ; auto.
  rewrite H ; auto. fold cps_cvt_branches usubst_branches subst_branches.
  rewrite H0 ; auto.
  rewrite H0 ; auto. rewrite H ; auto. lia.
  fold usubst_fn_list cps_cvt_fn_list substs. rewrite (H4 j i); auto. 
  fold usubst_fn_list cps_cvt_fn_list substs'. rewrite (H5 j i) ; auto. 
  rewrite H ; auto.
  erewrite H0 ; eauto. rewrite H ; auto.
  split.
  remember (is_valueb e) as b1.
  remember (are_valuesb es) as b2.
  destruct b1 ; destruct b2 ; intros ; try discriminate. 
  rewrite H5 ; auto. rewrite H3 ; auto. 
  intros. subst. rewrite (H4 _ _ eq_refl); auto. rewrite H ; auto. lia.
  rewrite H ; auto ; try lia. rewrite H0 ; auto.
Qed.

Lemma cps_cvt_comm_subst :
  forall v i e j, is_value v -> exp_wf 0 v -> exp_wf i e -> j < i ->
       usubst_val (cps_cvt_val v) j (cps_cvt e) = cps_cvt (subst v j e).
Proof.
  intros. apply (proj1 (proj1 (cps_cvt_comm_usubst' v H H0) i e H1) j H2).
Qed.

Lemma cps_cvt_val_comm_subst :
  forall v i e j, is_value v -> exp_wf 0 v -> exp_wf i e -> j < i ->
    is_valueb e = true -> 
    usubst_val (cps_cvt_val v) j (cps_cvt_val e) = cps_cvt_val (subst v j e).
Proof.
  intros. apply (proj2 (proj1 (cps_cvt_comm_usubst' v H H0) i e H1) j H2 H3).
Qed.

Lemma cps_cvts_comm_subst :
  forall v i es j k c, is_value v -> exp_wf 0 v -> exps_wf i es -> j < i ->
    cps_wf 0 k c ->
    usubst_cps (cps_cvt_val v) j (cps_cvts es c) =
    cps_cvts (substs v j es) (usubst_cps (cps_cvt_val v) j c).
Proof.
  intros. apply (proj1 (proj1 (proj2 (cps_cvt_comm_usubst' v H H0)) i es H1) j k c H2 H3).
Qed.

Lemma cps_cvt_vals_comm_subst :
  forall v i es j, is_value v -> exp_wf 0 v -> exps_wf i es ->
      are_valuesb es = true -> j < i -> 
      usubst_vals (cps_cvt_val v) j (cps_cvt_vals es) =
      cps_cvt_vals (substs v j es).
Proof.
  intros.
  apply (proj1 (proj2 (proj1 (proj2 (cps_cvt_comm_usubst' v H H0)) i es H1)) H2 j H3).
Qed.

Lemma cps_cvt_branches_comm_subst :
  forall v i bs j, is_value v -> exp_wf 0 v -> branches_wf i bs -> j < i -> 
                   usubst_branches (cps_cvt_val v) j (cps_cvt_branches bs) =
                   cps_cvt_branches (subst_branches v j bs).
Proof.
  intros. apply (proj2 (proj2 (cps_cvt_comm_usubst' v H H0)) i bs H1 j H2).
Qed.

Lemma cps_cvt_fn_list_comm_subst :
  forall v i es j, is_value v -> exp_wf 0 v -> exps_wf (2 + i) es -> j < i ->
                   usubst_fn_list (cps_cvt_val v) j (cps_cvt_fn_list es) =
                   cps_cvt_fn_list (substs v (2+j) es).
Proof.
  intros. 
  apply (proj2 (proj2 (proj1 (proj2 (cps_cvt_comm_usubst' v H H0)) _ es H1)) j i eq_refl H2).
Qed.

Lemma cps_cvt_comm_usub_list :
  forall vs, are_values vs -> exps_wf 0 vs ->
             forall e k, exp_wf (N.of_nat (length vs)) e -> val_wf 0 0 k -> 
                         usubst_list (Ret_c (cps_cvt e) k) (cps_cvt_vals vs) =
                         (Ret_c (cps_cvt (subst_list e vs)) k).
Proof.
  induction vs ; simpl ; intros. auto. inversion H. inversion H0. subst ; clear H H0.
  erewrite cps_cvt_comm_subst ; eauto ; try lia.
  erewrite usubst_closed_val ; eauto ; try lia.
  apply IHvs ; eauto. apply subst_preserves_exp_wf ; auto.
  replace (1 + N.of_nat (length vs)) with (N.of_nat (S (length vs))) ; auto ; lia.
Qed.

Lemma evals_length :
  forall es vs, evals es vs -> length es = length vs.
Proof.
  induction es ; intros vs H ; inversion H ; intros ; subst ; auto.
  simpl. rewrite (IHes vs0) ; auto.
Qed.

Lemma evals_list_to_indices :
  forall es vs, evals es vs -> list_to_indices es = list_to_indices vs.
Proof.
  induction es. intros. inversion H ; subst. auto. intros.
  inversion H ; intros ; subst. simpl. erewrite evals_length ; eauto.
  erewrite IHes ; eauto.
Qed.    

Lemma eval_is_valueb_eq' : 
  (forall e v,
     eval e v ->
     true = is_valueb e -> e = v) /\
  (forall es vs, 
        evals es vs -> 
        true = are_valuesb es -> es = vs).
Proof.
  apply my_eval_ind ; simpl ; intros ; auto ; try discriminate.
  rewrite H ; auto.
  destruct (is_valueb e) ; destruct (are_valuesb es) ; try discriminate.
  rewrite (H eq_refl) ; rewrite (H0 eq_refl) ; auto.
Qed.

Definition eval_is_valueb_eq := proj1 eval_is_valueb_eq'.
Definition evals_are_valuesb_eq := proj2 eval_is_valueb_eq'.

Lemma ksubst_gt_indices :
  forall k es i, i >= N.of_nat (length es) ->
                 ksubst_vals k i (list_to_indices es) = list_to_indices es.
Proof.
  induction es ; simpl ; intros ; auto. if_split. rewrite IHes ; auto. lia.
Qed.

Lemma ksubst_cps_cvts' : 
  forall d k, val_wf 0 0 k -> 
    forall es2 es1, exps_wf 0 es2 -> 
      (cps_cvts es2 (Ret_c (KVar_c (N.of_nat (length (es1 ++ es2))))
                           (Con_c d (list_to_indices (es1 ++ es2)))))[N.of_nat(length es1) := k] =
      cps_cvts es2 (Ret_c k (Con_c d (list_to_indices (es1 ++ es2)))).
Proof.
  induction es2 ; simpl ; intros.
  repeat if_split ; try rewrite <- app_nil_end in * ; try lia.
  erewrite kshift_closed_val ; eauto.
  rewrite ksubst_gt_indices ; auto ; lia.
  inversion H0 ; clear H0 ; subst.
  erewrite ksubst_closed_val. Focus 2.
  eapply cps_kvar_closed. eauto. Focus 2. lia. repeat apply f_equal.
  specialize (IHes2 (es1 ++ [a]) H5).
  repeat rewrite app_length in *. simpl in *.
  repeat rewrite <- app_assoc in IHes2. simpl in *.
  replace (N.of_nat (length es1 + 1)) with (1 + N.of_nat (length es1)) in IHes2 ; try lia. 
  replace (N.of_nat (length es1 + 1 + length es2)) with (N.of_nat (length es1 + S (length es2)))
  in IHes2; try lia. auto.
Qed.

Lemma ksubst_cps_cvts :
  forall d k es,
    val_wf 0 0 k ->
    exps_wf 0 es ->
      (cps_cvts es (Ret_c (KVar_c (N.of_nat (length es)))
                           (Con_c d (list_to_indices es))))[0 := k] =
      cps_cvts es (Ret_c k (Con_c d (list_to_indices es))).
Proof.
  intros. generalize (ksubst_cps_cvts' d k H es nil H0). simpl. auto.
Qed.

Lemma ksubst_vals_append :
  forall v k (vs1 vs2:list val_c),
    (vs1 ++ vs2)[k:=v] = (vs1[k:=v]) ++ (vs2[k:=v]).
  induction vs1 ; simpl ; intros ; auto. rewrite IHvs1. auto.
Qed.

Lemma ksubst_cps_cvts2' :
  forall es2 es1,
    exps_wf 0 es2 ->
    forall v k,
      (cps_cvts es2 k) [N.of_nat(length es1) := (cps_cvt_val v)] = 
      (cps_cvts es2 (k [N.of_nat(length (es1 ++ es2)) := (cps_cvt_val v)])).
Proof.
  induction es2 ; simpl ; intros ; auto.
  rewrite <- app_nil_end ; auto.
  inversion H ; clear H ; subst.
  erewrite cps_cvt_ksubst ; eauto. repeat apply f_equal.
  specialize (IHes2 (es1 ++ [a]) H4).
  repeat rewrite app_length in *. simpl in *.
  replace (N.of_nat (length es1 + 1)) with (1 + N.of_nat (length es1)) in IHes2 ; try lia.
  rewrite IHes2.
  replace (N.of_nat (length es1 + 1 + length es2)) with (N.of_nat (length es1 + S (length es2))) ;
    auto ; try lia.
Qed.

Lemma ksubst_cps_cvts2 :
  forall es v k, exps_wf 0 es ->
                 (cps_cvts es k) [0 := cps_cvt_val v] =
                 cps_cvts es (k [N.of_nat (length es) := cps_cvt_val v]).
Proof.
  intros.
  apply (ksubst_cps_cvts2' es nil H v k).
Qed.                 

Fixpoint cps_cvt_vals' (es:list exp) (k:cps) : cps :=
  match es with
    | nil => k
    | e :: es => cps_cvt_vals' es (k[N.of_nat(length es):=cps_cvt_val e])
  end.

Lemma vals_wf_append :
  forall i j vs1 vs2,
    vals_wf i j (vs1 ++ vs2) <-> (vals_wf i j vs1 /\ vals_wf i j vs2).
Proof.
  induction vs1 ; simpl ; intros ; split ; intro. split. constructor. auto.
  destruct H ; auto. inversion H ; subst ; clear H. split ; auto. 
  constructor ; auto. specialize (IHvs1 vs2). destruct IHvs1. tauto.
  specialize (IHvs1 vs2). destruct IHvs1. tauto.
  destruct H. inversion H. subst. clear H. constructor ; auto.
  specialize (IHvs1 vs2). destruct IHvs1. auto.
Qed.

Lemma eval_cps_cvt_vals' :
  forall d vs,
    exps_wf 0 vs -> 
    are_values vs ->
    forall k ws,
      val_wf 0 0 k ->
      vals_wf 0 0 ws ->
      forall v', 
        (eval_c (cps_cvt_vals' vs (Ret_c k (Con_c d (ws ++ (list_to_indices vs))))) v' <->
         eval_c (Ret_c k (Con_c d (ws ++ (cps_cvt_vals vs)))) v').
Proof.
  induction vs ; simpl ; intros. tauto.
  inversion H ; inversion H0 ; subst ; clear H H0. rename a into v.
  erewrite (ksubst_closed_val 0 0) ; auto ; try lia.
  fold ksubst_vals. rewrite ksubst_vals_append.
  erewrite ksubst_closed_vals ; eauto ; try lia.
  simpl. repeat if_split.
  erewrite kshift_closed_val ; [idtac | eapply cps_val_kvar_closed ; eauto].
  rewrite ksubst_gt_indices ; try lia.
  specialize (app_assoc ws [cps_cvt_val v] (list_to_indices vs)).
  intros. simpl in H. rewrite H.
  specialize (IHvs H7 H11 k (ws ++ [cps_cvt_val v]) H1).
  rewrite IHvs. rewrite <- app_assoc ; simpl ; tauto.
  rewrite vals_wf_append ; split ; auto. 
Qed.

Lemma find_branch_cps_cvt :
  forall d n e bs,
    find_branch d n bs = Some e ->
    forall v1 v2,
      find_branch d n (ksubst_branches v1 0 (ksubst_branches v2 1 (cps_cvt_branches bs))) =
      Some (ksubst_cps v1 0 (ksubst_cps v2 1 (Ret_c (cps_cvt e) (KVar_c 1)))).
Proof.
  induction bs ; simpl ; intros. discriminate. unfold br.
  destruct a. destruct p. simpl in *. repeat if_split. congruence. discriminate.
Qed.

Lemma cps_cvt_list_nth :
  forall n es e, nthopt n es = Some e ->
    nthopt n (cps_cvt_fn_list es) = Some (Ret_c (cps_cvt e) (KVar_c 0)).
Proof.
  induction n ; destruct es ; simpl ; intros ; try discriminate. injection H.
  intro ; subst ; auto. apply (IHn _ _ H).
Qed.

(** The key correctness lemma for CPS conversion.  In essence, CPS converting
    an expression and feeding it closed continuation [k], is the same as 
    evaluating the expression to a value, then CPS converting the value,
    and then feeding k to the value. *)
Lemma cps_cvt_corr :
  (forall e v,
     eval e v ->
     exp_wf 0 e -> 
     forall k, val_wf 0 0 k ->
               forall v', 
                 eval_c (Ret_c (cps_cvt e) k) v' <->
                 eval_c (Ret_c (cps_cvt v) k) v') /\
  (forall es vs,
     evals es vs ->
     exps_wf 0 es ->
       forall d k ws,
         val_wf 0 0 k -> 
         vals_wf 0 0 ws -> 
         forall v', 
           (eval_c (cps_cvts es (Ret_c k (Con_c d (ws ++ (list_to_indices es))))) v' <->
            eval_c (cps_cvt_vals' vs (Ret_c k (Con_c d (ws ++ (list_to_indices vs))))) v')).
Proof.
  Transparent N.add.
  Transparent N.sub.
  apply my_eval_ind ; intros ; simpl ; try tauto.
  (* application case *)
  inversion H2 ; clear H2 ; subst.
  specialize (H H7). specialize (H0 H8).
  generalize (eval_preserves_wf _ _ e H7) (eval_preserves_wf _ _ e0 H8).
  intros. inversion H2. subst.
  generalize (subst_preserves_exp_wf 0 e1' H9 _ H4). intro.
  generalize (eval_preserves_wf _ _ e3 H5). intro.
  rewrite <- H1 ; auto ; clear H1.
  rewrite eval_ret. simpl.
  rewrite (cps_cvt_ksubst _ _ H7).
  rewrite (cps_cvt_ksubst _ _ H8).
  rewrite (kshift_closed_val k H3).
  rewrite H ; simpl ; clear H. Focus 2. repeat constructor ; eauto.
  rewrite eval_ret. simpl.
  rewrite eval_ret. simpl.
  rewrite (cps_cvt_ksubst (1+0)) ; auto.
  rewrite (kshift_closed_val' 1 1 (cps_cvt e1')) ; auto. Focus 2.
  eapply (val_weaken 1 0 (cps_cvt e1') _ 0 1). 
  rewrite (kshift_closed_val' 0 1 (cps_cvt e2)) ; auto. 
  rewrite (ksubst_closed_val 0 0 (cps_cvt e2)) ; auto ; try lia.
  rewrite H0 ; simpl ; clear H0.
  Focus 2. repeat constructor.
  eapply (val_weaken 1 0 (cps_cvt e1') _ 0 2). simpl.
  generalize (cps_kvar_closed _ _ H9). simpl. intro.
  rewrite (wf_kshift_zero_val 0 0 k H3) ; try lia.
  rewrite (ksubst_closed_val _ _ _ H3) ; auto ; try lia.
  generalize (eval_yields_value _ _ e0). intro. 
  rewrite (cps_val _ H).
  rewrite eval_ret. simpl.
  repeat rewrite val_kshift_0.
  generalize (cps_val_kvar_closed 0 _ H4 H). intro.
  rewrite (ksubst_closed_val _ _ (cps_cvt_val v2) H0 0) ; auto ; try lia.
  rewrite eval_ret. simpl.
  repeat rewrite val_kshift_0.
  repeat rewrite (ksubst_closed_val _ _ _ H3) ; auto ; try lia.
  rewrite eval_call. simpl.
  rewrite val_kshift_0. 
  generalize (cps_kvar_closed _ _ H9). intro.
  generalize (val_weaken _ _ _ H1 0 1). simpl. intro.
  repeat rewrite (ksubst_closed_val _ _ _ H1) ; auto ; try lia.
  rewrite (usubst_closed_val _ _ _ H3) ; auto ; try lia.
  rewrite (cps_cvt_comm_subst v2 1) ; auto ; try lia.
  tauto.
  (* D(e1,....,en) case *)
  inversion H0 ; clear H0 ; subst. fold are_valuesb.
  remember (are_valuesb es) as b.
  generalize (evals_are_valuesb_eq _ _ e). intro.
  destruct b.
  (* D(v1,...,vn) case -- already a value *)
  rewrite Heqb in H0. specialize (H0 eq_refl). subst.
  rewrite <- Heqb. tauto.
  (* D(e1,...,en) case -- not already a value *)
  generalize (proj2 (are_valuesb_corr vs) (evals_yields_values _ _ e)).
  intro. rewrite H2.
  repeat rewrite eval_ret.
  simpl. rewrite val_kshift_0.
  generalize (ksubst_closed_vals 0 0). unfold ksubstitute. simpl.
  intros. rewrite H3 ; try lia.
  Focus 2.
  apply cps_vals_kvar_closed.
  apply (evals_preserves_wf _ _ e) ; auto.
  eapply evals_yields_values ; eauto.
  rewrite ksubst_cps_cvts ; auto.
  specialize (H H4 d k nil H1 (nil_c_wf 0 0) v'). simpl in H.
  rewrite H.
  assert (are_values vs). apply (proj1 (are_valuesb_corr _)) ; auto.
  assert (exps_wf 0 vs). eapply (evals_preserves_wf) ; eauto.
  rewrite (eval_cps_cvt_vals' d vs H6 H5 k nil H1) ; auto. simpl ; tauto.
  (* Let case *)
  inversion H1 ; clear H1 ; subst.
  repeat rewrite eval_ret ; simpl.
  rewrite (ksubst_closed_val 0 0) ; eauto ; try lia.
  rewrite H ; eauto.
  Focus 2. repeat constructor. rewrite (ksubst_closed_val 1 0) ; eauto ; try lia.
  simpl in *. eapply (val_weaken 1 0 (cps_cvt e2) _ 0 2).
  rewrite kshift_closed_val ; eauto.
  rewrite (cps_val v1) ; [idtac | eapply eval_yields_value ; eauto].
  rewrite eval_ret. simpl. rewrite (ksubst_closed_val 0 0 (cps_cvt_val v1)) ; try lia.
  Focus 2. apply cps_val_kvar_closed ; eauto. eapply eval_preserves_wf ; eauto.
  repeat rewrite val_kshift_0.
  rewrite kshift_closed_val ; eauto. 
  rewrite eval_ret. simpl.
  rewrite (ksubst_closed_val 1 0 (cps_cvt e2)) ; try lia.
  Focus 2. apply (cps_kvar_closed 1) ; auto.
  rewrite val_kshift_0.
  rewrite (ksubst_closed_val 1 0 (cps_cvt e2)) ; try lia.
  Focus 2. apply (cps_kvar_closed 1) ; auto.
  rewrite (ksubst_closed_val 0 0 k) ; eauto ; try lia.
  rewrite eval_call. simpl. rewrite (ksubst_closed_val 1 0 (cps_cvt e2)) ; try lia.
  Focus 2. apply (cps_kvar_closed 1) ; auto.
  rewrite val_kshift_0. rewrite (usubst_closed_val 0 0 k) ; auto ; try lia.
  rewrite (cps_cvt_comm_subst v1 1) ; eauto ; try lia.
  Focus 2. eapply eval_preserves_wf ; eauto.
  unfold substitute in H0. simpl in H0. apply H0 ; auto.
  apply subst_preserves_exp_wf ; eauto. eapply eval_preserves_wf ; eauto.
  (* Match case *)
  inversion H1 ; subst.
  assert (is_value (Con_e d vs)). eapply eval_yields_value ; eauto. inversion H3 ; subst.
  assert (exp_wf 0 (Con_e d vs)). eapply eval_preserves_wf ; eauto. inversion H4 ; subst.
  rewrite eval_ret. simpl. rewrite (ksubst_closed_val 0 0 (cps_cvt e)) ; eauto ; try lia.
  assert(cpsbranches_wf 0 1 (ksubst_branches' ksubst_cps k 1 (cps_cvt_branches' cps_cvt bs))).
  fold ksubst_branches.
  eapply ksubst_preserves_wf_branches ; eauto ; try lia.
  apply cps_branches_closed ; auto.
  rewrite H ; eauto. Focus 2. repeat constructor. eauto.
  rewrite cps_val ; eauto.
  rewrite eval_ret. simpl. fold kshift_branches ksubst_branches ksubst_vals cps_cvt_branches.
  rewrite (kshift_closed_branches 0) ; eauto.
  rewrite (ksubst_closed_vals 0 0) ; eauto ; try lia.
  rewrite eval_ret. simpl. fold ksubst_branches kshift_vals cps_cvt_vals.
  rewrite vals_kshift_0. fold ksubst_branches in H8.
  generalize (find_branch_cps_cvt _ _ _ _ e1 (Con_c d (cps_cvt_vals vs)) k).
  assert (length vs = length (cps_cvt_vals vs)). unfold cps_cvt_vals. rewrite map_length. auto.
  rewrite H9. intro.
  rewrite eval_match ; eauto.
  simpl.
  generalize (find_branch_preserves_wf _ _ H7 _ _ _ e1). rewrite N.add_0_r. intro.
  assert (val_wf (N.of_nat (length vs)) 0 (cps_cvt e')).
  apply (cps_kvar_closed) ; auto.
  repeat (rewrite (ksubst_closed_val (N.of_nat (length vs)) 0 (cps_cvt e')) ; eauto ; try lia).
  rewrite kshift_closed_val ; eauto.
  rewrite (ksubst_closed_val 0 0 k) ; eauto ; try lia.
  rewrite cps_cvt_comm_usub_list ; auto. 
  apply H0 ; auto.
  apply subst_list_preserves_exp_wf ; auto. rewrite N.add_0_r ; auto.
  (* Proj case *)
  inversion H0 ; subst ; clear H0.
  repeat rewrite eval_ret.
  simpl. rewrite (kshift_closed_val k) ; eauto. 
  rewrite (ksubst_closed_val 0 0) ; eauto ; try lia.
  rewrite H ; auto. Focus 2. repeat constructor. eapply (val_weaken 0 0 k H1 0 1).
  rewrite val_kshift_0. simpl.
  rewrite eval_ret. simpl. fold ksubst_fn_list. fold cps_cvt_fn_list.
  assert (exps_wf 2 es).
  generalize (eval_preserves_wf _ _ e0 H4). intro. inversion H0 ; subst. auto.
  assert (fn_list_wf 0 0 (cps_cvt_fn_list es)).
  apply (cps_fn_list_closed 0 es) ; auto.
  rewrite (ksubst_closed_fn_list 0 0) ; auto ; try lia.
  rewrite (kshift_closed_val' 0 1 k) ; [idtac | eapply (val_weaken 0 0 k H1 0 1)].
  rewrite eval_ret. simpl. fold kshift_fn_list.
  rewrite (kshift_closed_fn_list _ _ _ H2).
  rewrite (ksubst_closed_val 0 0 k) ; eauto ; try lia.
  generalize (cps_cvt_list_nth _ _ _ e1) ; intro.
  rewrite eval_proj ; eauto.
  replace (Fix_c (cps_cvt_fn_list es)) with (cps_cvt_val (Fix_e es)) ; auto.
  replace (Lam_c (Ret_c (cps_cvt e') (KVar_c 0))) with (cps_cvt_val (Lam_e e')) ; auto.
  rewrite (cps_cvt_val_comm_subst _ 1) ; auto ; try lia. Focus 2.
  constructor. apply (nthopt_preserves_wf _ _ H0 _ _ e1).
  rewrite (ksubst_closed_val 1 1) ; try lia. simpl. tauto.
  rewrite <- (cps_cvt_comm_subst _ 2) ; eauto ; try lia ; simpl.
  Focus 2. apply (nthopt_preserves_wf _ _ H0 _ _ e1). fold cps_cvt_fn_list.
  apply (fun H1 H2 H3 => usubst_preserves_wf_val 2 1 (cps_cvt e') H1 1 H2 (Fix_c (cps_cvt_fn_list es)) H3 1) ; auto ; try lia.
  generalize (nthopt_preserves_wf _ _ H0 _ _ e1). intros.
  generalize (cps_kvar_closed _ _ H5). intro.
  apply (val_weaken _ _ _ H6 0 1).
  (* Cons case *)
  inversion H1 ; subst ; clear H1.
  rewrite H ; auto.
  Focus 2.
  constructor.
  apply (proj1 (proj1 (proj2 cps_kvar_closed') 0 es H8) 1).
  repeat constructor.
  generalize (val_weaken _ _ _ H2 0 (1 + N.of_nat(length es))).
  replace (1 + N.of_nat(length es) + 0) with (1 + N.of_nat(length es)) ; try lia. auto.
  rewrite vals_wf_append. split.
  generalize (vals_weaken _ _ _ H3 0 (1 + N.of_nat(length es))).
  replace (1 + N.of_nat(length es) + 0) with (1 + N.of_nat(length es)) ; try lia. auto.
  repeat constructor. lia. apply wf_list_to_indices.
  rewrite cps_val. Focus 2. eapply eval_yields_value ; eauto.
  rewrite eval_ret. simpl.
  rewrite eval_ret. simpl.
  rewrite (ksubst_closed_val 0 0) ; try lia.
  Focus 2. eapply cps_val_kvar_closed ; eauto. eapply (eval_preserves_wf) ; eauto.
  rewrite cps_kshift_0.
  rewrite ksubst_cps_cvts2 ; auto.
  simpl. rewrite (ksubst_closed_val 0 0) ; eauto ; try lia.
  fold ksubst_vals cps_cvt_vals. 
  rewrite ksubst_vals_append.
  erewrite ksubst_closed_vals ; eauto ; try lia. simpl.
  repeat if_split.
  rewrite kshift_closed_val ; eauto.
  Focus 2. eapply cps_val_kvar_closed ; eauto. eapply eval_preserves_wf ; eauto.
  rewrite ksubst_gt_indices ; try lia.
  specialize (H0 H8 d k (ws ++ [cps_cvt_val v]) H2).
  assert (vals_wf 0 0 (ws ++ [cps_cvt_val v])).
  rewrite vals_wf_append. split ; auto. constructor.
  eapply cps_val_kvar_closed ; eauto. eapply (eval_preserves_wf) ; eauto. constructor.
  specialize (H0 H1 v').
  rewrite <- app_assoc in H0. simpl in H0. rewrite H0.
  rewrite (ksubst_closed_val 0 0) ; try lia ; auto.
  rewrite ksubst_vals_append.
  rewrite (ksubst_closed_vals 0 0) ; try lia ; auto. simpl.
  repeat if_split. rewrite kshift_closed_val.
  Focus 2. eapply cps_val_kvar_closed ; eauto. eapply eval_preserves_wf ; eauto.
  rewrite ksubst_gt_indices ; try lia.
  rewrite <- app_assoc. tauto.
  Grab Existential Variables.
  apply (cps_kvar_closed) ; eauto.
  apply (cps_kvar_closed) ; eauto.
  apply (cps_kvar_closed) ; eauto.
Qed.

Lemma cps_cvt_prog_corr :
  forall e v, exp_wf 0 e -> eval e v -> eval_c (cps_cvt_prog e) (cps_cvt_val v).
Proof.
  intros. unfold cps_cvt_prog.
  rewrite (proj1 cps_cvt_corr e v H0 H) ; [idtac | repeat constructor ; auto ; lia].
  rewrite (cps_val _ (eval_yields_value _ _ H0)).
  rewrite eval_ret. simpl. rewrite eval_ret. simpl.
  rewrite (ksubst_closed_val 0 0) ; try lia. Focus 2.
  eapply cps_val_kvar_closed ; eauto. eapply eval_preserves_wf ; eauto.
  rewrite val_kshift_0. constructor.
Qed.

Lemma kshift_twice :
  (forall c i j m n, i <= j -> j <= i + m -> kshift_cps n j (kshift_cps m i c) = kshift_cps (m+n) i c) /\
  (forall v i j m n, i <= j -> j <= i + m -> kshift_val n j (kshift_val m i v) = kshift_val (m+n) i v) /\
  (forall vs i j m n, i <= j -> j <= i + m -> kshift_vals n j (kshift_vals m i vs) = kshift_vals (m+n) i vs) /\
  (forall bs i j m n, i <= j -> j <= i + m -> kshift_branches n j (kshift_branches m i bs) = kshift_branches (m+n) i bs) /\
  (forall fs i j m n, i <= j -> j <= i + m -> kshift_fn_list n j (kshift_fn_list m i fs) = kshift_fn_list (m+n) i fs).
Proof.
  Opaque N.add.
  apply my_cps_ind ; simpl ; intros ; auto ;
  try (rewrite H ; auto ; rewrite H0 ; auto ; rewrite H1 ; auto ; fail).
  repeat if_split ; auto. replace (n + (m + n0)) with (n + m + n0) ; try lia ; auto.
  rewrite (H (1+i) (1+j)) ; auto ; try lia.
  rewrite (H (1+i) (1+j)) ; auto ; try lia.
  rewrite (H (1+i) (1+j)) ; auto ; try lia.
  rewrite H0 ; auto.
Qed.

Lemma ushift_twice :
  (forall c i j m n, i <= j -> j <= i + m -> ushift_cps n j (ushift_cps m i c) = ushift_cps (m+n) i c) /\
  (forall v i j m n, i <= j -> j <= i + m -> ushift_val n j (ushift_val m i v) = ushift_val (m+n) i v) /\
  (forall vs i j m n, i <= j -> j <= i + m -> ushift_vals n j (ushift_vals m i vs) = ushift_vals (m+n) i vs) /\
  (forall bs i j m n, i <= j -> j <= i + m -> ushift_branches n j (ushift_branches m i bs) = ushift_branches (m+n) i bs) /\
  (forall fs i j m n, i <= j -> j <= i + m -> ushift_fn_list n j (ushift_fn_list m i fs) = ushift_fn_list (m+n) i fs).
Proof.
  apply my_cps_ind ; simpl ; intros ; auto ;
  try (rewrite H ; auto ; rewrite H0 ; auto ; rewrite H1 ; auto ; fail).
  repeat if_split ; auto. replace (n + (m + n0)) with (n + m + n0) ; try lia ; auto.
  rewrite (H (1+i) (1+j)) ; auto ; try lia.
  rewrite (H (n+i) (n+j)) ; auto ; try lia. rewrite H0 ; auto ; try lia.
  rewrite (H (2+i) (2+j)) ; auto ; try lia.
  rewrite H0 ; auto.
Qed.

Lemma kshift_ushift_comm :
  (forall c i j k l, kshift_cps i j (ushift_cps k l c) = ushift_cps k l (kshift_cps i j c)) /\
  (forall v i j k l, kshift_val i j (ushift_val k l v) = ushift_val k l (kshift_val i j v)) /\
  (forall vs i j k l, kshift_vals i j (ushift_vals k l vs) = ushift_vals k l (kshift_vals i j vs)) /\
  (forall bs i j k l, kshift_branches i j (ushift_branches k l bs) = ushift_branches k l (kshift_branches i j bs)) /\
  (forall fs i j k l, kshift_fn_list i j (ushift_fn_list k l fs) = ushift_fn_list k l (kshift_fn_list i j fs)).
Proof.
  apply my_cps_ind ; simpl ; intros ; auto ;
  try (rewrite H ; auto ; rewrite H0 ; auto ; rewrite H1 ; auto ; fail) ; if_split.
Qed.

Lemma kshift_ksubst :
  (forall c i k j v, k <= j -> kshift_cps i k (c[j:=v]) = (kshift_cps i k c)[j+i:=v]) /\
  (forall w i k j v, k <= j -> kshift_val i k (w[j:=v]) = (kshift_val i k w)[j+i:=v]) /\
  (forall ws i k j v, k <= j -> kshift_vals i k (ws[j:=v]) = (kshift_vals i k ws)[j+i:=v]) /\
  (forall bs i k j v, k <= j -> kshift_branches i k (bs[j:=v]) = (kshift_branches i k bs)[j+i:=v]) /\
  (forall fs i k j v, k <= j -> kshift_fn_list i k (fs[j:=v]) = (kshift_fn_list i k fs)[j+i:=v]).
Proof.
  apply my_cps_ind ; simpl ; intros ; auto ;
  try (rewrite H ; auto ; rewrite H0 ; auto; rewrite H1 ; auto ; fail).
  repeat if_split ; auto. destruct (lt_dec j k) ; auto. rewrite (proj1 (proj2 kshift_twice)) ;
    auto ; try lia. rewrite (proj1 (proj2 kshift_twice)) ; auto ; try lia.
  destruct (lt_dec n k) ; try lia. apply f_equal ; lia.
  rewrite (H i (1 + k) (1 +j)). replace (1 + j + i) with (1 + (j + i)) ; try lia. auto. lia.
  rewrite (H i (1 + k) (1 + j)). replace (1 + j + i) with (1 + (j + i)) ; try lia. auto. lia.
  rewrite (H i (1 + k) (1 + j)) ; try lia. rewrite H0 ; try lia.
  replace (1 + j + i) with (1 + (j + i)) ; auto ; try lia.
Qed.

Lemma ushift_usubst :
  (forall c i k j v, k <= j -> ushift_cps i k (c{j:=v}) = (ushift_cps i k c){j+i:=v}) /\
  (forall w i k j v, k <= j -> ushift_val i k (w{j:=v}) = (ushift_val i k w){j+i:=v}) /\
  (forall ws i k j v, k <= j -> ushift_vals i k (ws{j:=v}) = (ushift_vals i k ws){j+i:=v}) /\
  (forall bs i k j v, k <= j -> ushift_branches i k (bs{j:=v}) = (ushift_branches i k bs){j+i:=v}) /\
  (forall fs i k j v, k <= j -> ushift_fn_list i k (fs{j:=v}) = (ushift_fn_list i k fs){j+i:=v}).
Proof.
  apply my_cps_ind ; simpl ; intros ; auto ;
  try (rewrite H ; auto ; rewrite H0 ; auto; rewrite H1 ; auto ; fail).
  repeat if_split ; auto. destruct (lt_dec j k) ; auto. try lia.
  rewrite (proj1 (proj2 ushift_twice)) ;
    auto ; try lia. destruct (lt_dec n k) ; try lia. apply f_equal ; lia.
  rewrite (H i (1 + k) (1 +j)). replace (1 + j + i) with (1 + (j + i)) ; try lia. auto. lia.
  rewrite (H i (n + k) (n + j)). replace (n + j + i) with (n + (j + i)) ; try lia.
  rewrite H0 ; auto. lia.
  rewrite (H i (2 + k) (2 + j)) ; try lia. rewrite H0 ; try lia.
  replace (2 + j + i) with (2 + (j + i)) ; auto ; try lia.
Qed.

(*
Lemma kshift_usubst :
  (forall c i k j v, k <= j -> kshift_cps i k (c{j:=v}) = (kshift_cps i k c){j:=kshift_val i k v}) /\
  (forall w i k j v, k <= j -> kshift_val i k (w{j:=v}) = (kshift_val i k w){j:=kshift_val i k v}) /\
  (forall ws i k j v, k <= j -> kshift_vals i k (ws{j:=v}) = (kshift_vals i k ws){j:=kshift_val i k v}) /\
  (forall bs i k j v, k <= j -> kshift_branches i k (bs{j:=v}) = (kshift_branches i k bs){j:=kshift_val i k v}) /\
  (forall fs i k j v, k <= j -> kshift_fn_list i k (fs{j:=v}) = (kshift_fn_list i k fs){j:=kshift_val i k v}).
Proof.
  apply my_cps_ind ; simpl ; intros ; auto ;
  try (rewrite H ; auto ; rewrite H0 ; auto ; rewrite H1 ; auto ; fail).
  repeat if_split. rewrite (proj1 (proj2 kshift_ushift_comm)). auto.
*)
  

Lemma kshift_away_subst :
  (forall c k i j v, k <= i -> i < k + (j + 1) ->
        (kshift_cps (1+j) k c)[i:=v] = kshift_cps j k c) /\
  (forall w k i j v, k <= i -> i < k + (j + 1) ->
        (kshift_val (1+j) k w)[i:=v] = kshift_val j k w) /\
  (forall ws k i j v, k <= i -> i < k + (j + 1) ->
        (kshift_vals (1+j) k ws)[i:=v] = kshift_vals j k ws) /\
  (forall bs k i j v, k <= i -> i < k + (j + 1) ->
        (kshift_branches (1+j) k bs)[i:=v] = kshift_branches j k bs) /\
  (forall fs k i j v, k <= i -> i < k + (j + 1) ->
        (kshift_fn_list (1+j) k fs)[i:=v] = kshift_fn_list j k fs).
Proof.
  apply my_cps_ind ; simpl ; intros ; auto ;
  try (rewrite H ; auto ; rewrite H0 ; auto ; rewrite H1 ; auto ; fail).
  repeat if_split. apply f_equal. lia.
  rewrite (H (1+k) (1+i)) ; try lia ; auto.
  rewrite (H (1+k) (1+i)) ; try lia ; auto.
  rewrite (H (1+k) (1+i)) ; try lia. rewrite H0 ; auto.
Qed.

Lemma ushift_away_subst :
  (forall c k i j v, k <= i -> i < k + (j + 1) ->
                     (ushift_cps (1+j) k c){i:=v} = ushift_cps j k c) /\
  (forall w k i j v, k <= i -> i < k + (j + 1) ->
                     (ushift_val (1+j) k w){i:=v} = ushift_val j k w) /\
  (forall ws k i j v, k <= i -> i < k + (j + 1) ->
                     (ushift_vals (1+j) k ws){i:=v} = ushift_vals j k ws) /\
  (forall bs k i j v, k <= i -> i < k + (j + 1) ->
                     (ushift_branches (1+j) k bs){i:=v} =
                     ushift_branches j k bs) /\
  (forall fs k i j v, k <= i -> i < k + (j + 1) ->
                     (ushift_fn_list (1+j) k fs){i:=v} =
                     ushift_fn_list j k fs).
Proof.
  apply my_cps_ind ; simpl ; intros ; auto ;
  try (rewrite H ; auto ; rewrite H0 ; auto ; rewrite H1 ; auto ; fail).
  repeat if_split. apply f_equal. lia.
  rewrite (H (1+k) (1+i)) ; try lia ; auto.
  rewrite (H (n+k) (n+i)) ; try lia. rewrite H0 ; auto.
  rewrite (H (2+k) (2+i)) ; try lia. rewrite H0 ; auto.
Qed.

Lemma ksubst_comm :
  (forall (c:cps) v1 v2 i j, i <= j -> c[i:=v1][j:=v2] = c[1+j:=v2][i:=v1[j-i:=v2]]) /\
  (forall (w:val_c) v1 v2 i j, i <= j -> w[i:=v1][j:=v2] = w[1+j:=v2][i:=v1[j-i:=v2]]) /\
  (forall (ws:list val_c) v1 v2 i j, i <= j -> ws[i:=v1][j:=v2] = ws[1+j:=v2][i:=v1[j-i:=v2]]) /\
  (forall (bs:list (branch cps)) v1 v2 i j,
     i <= j -> bs[i:=v1][j:=v2] = bs[1+j:=v2][i:=v1[j-i:=v2]]) /\
  (forall (fs:list cps) v1 v2 i j, i <= j -> fs[i:=v1][j:=v2] = fs[1+j:=v2][i:=v1[j-i:=v2]]).
Proof.
  apply my_cps_ind ; simpl ; intros ; auto ;
  try (rewrite H ; auto ; rewrite H0 ; auto ; rewrite H1 ; auto ; fail).
  repeat if_split. generalize (proj1 (proj2 kshift_ksubst) v1 i 0 (j - i) v2).
  unfold ksubstitute ; simpl. intros. rewrite H0 ; try lia.
  replace (j - i + i) with j ; try lia ; auto.
  generalize (proj1 (proj2 kshift_away_subst) v2 0 i (n-1)). unfold ksubstitute ; simpl.
  intros. rewrite H0 ; try lia ; auto.
  rewrite (H _ _ (1+i) (1+j)). replace (1 + j - (1 + i)) with (j - i) ; try lia ; auto. lia.
  rewrite (H _ _ (1+i) (1+j)). replace (1 + j - (1 + i)) with (j - i) ; try lia ; auto. lia.
  rewrite (H _ _ (1+i) (1+j)). replace (1 + j - (1 + i)) with (j - i) ; try lia ; auto.
  rewrite H0 ; try lia. auto. lia.
Qed.

Lemma usubst_comm :
  (forall (c:cps) v1 v2 i j, i <= j ->
     c{i:=v1}{j:=v2} = c{1+j:=v2}{i:=v1{j-i:=v2}}) /\
  (forall (w:val_c) v1 v2 i j, i <= j -> 
     w{i:=v1}{j:=v2} = w{1+j:=v2}{i:=v1{j-i:=v2}}) /\
  (forall (ws:list val_c) v1 v2 i j, i <= j -> 
     ws{i:=v1}{j:=v2} = ws{1+j:=v2}{i:=v1{j-i:=v2}}) /\
  (forall (bs:list (branch cps)) v1 v2 i j, i <= j -> 
     bs{i:=v1}{j:=v2} = bs{1+j:=v2}{i:=v1{j-i:=v2}}) /\
  (forall (fs:list cps) v1 v2 i j, i <= j ->
     fs{i:=v1}{j:=v2} = fs{1+j:=v2}{i:=v1{j-i:=v2}}).
Proof.
  apply my_cps_ind ; simpl ; intros ; auto ;
  try (rewrite H ; auto ; rewrite H0 ; auto ; rewrite H1 ; auto ; fail).
  repeat if_split. generalize (proj1 (proj2 ushift_usubst) v1 i 0 (j - i) v2).
  unfold substitute ; simpl. intros. rewrite H0 ; try lia.
  replace (j - i + i) with j ; try lia ; auto.
  generalize (proj1 (proj2 ushift_away_subst) v2 0 i (n-1)). unfold substitute ; simpl.
  intros. rewrite H0 ; try lia ; auto.
  rewrite (H _ _ (1+i) (1+j)) ; try lia.
  replace (1 + j - (1 + i)) with (j - i) ; try lia ; auto.
  rewrite (H _ _ (n+i) (n+j)) ; try lia.
  replace (n + j - (n + i)) with (j - i) ; try lia ; auto. 
  rewrite H0 ; try lia. replace (1 + (n + j)) with (n + (1 + j)) ; try lia ; auto.
  rewrite (H _ _ (2+i) (2+j)) ; try lia. rewrite H0 ; try lia.
  replace (2 + j - (2 + i)) with (j - i) ; try lia.
  replace (1 + (2 + j)) with (2 + (1 + j)) ; try lia ; auto.
Qed.

(*
Lemma usubst_kshift_comm :
  (forall c v i j k, (ushift_cps i k c)[j:=ushift_val i k v] = ushift_cps i k (c[j:=v])) /\
  (forall w v i j k, (ushift_val i k w)[j:=ushift_val i k v] = ushift_val i k (w[j:=v])) /\
  (forall ws v i j k, (ushift_vals i k ws)[j:=ushift_val i k v] = ushift_vals i k (ws[j:=v])) /\
  (forall bs v i j k, (ushift_branches i k bs)[j:=ushift_val i k v] = ushift_branches i k (bs[j:=v])) /\
  (forall fs v i j k, (ushift_fn_list i k fs)[j:=ushift_val i k v] = ushift_fn_list i k (fs[j:=v])).
Proof.
  apply my_cps_ind ; simpl ; intros ; auto ;
  try (rewrite H ; auto ; rewrite H0 ; auto ; rewrite H1 ; auto ; fail).
  repeat if_split. apply (proj1 (proj2 kshift_ushift)).
  rewrite <- (H v i (1 + j) (1 +k)).
  Admitted.
  
Lemma uksubst_comm :
  (forall (c:cps) v1 v2 i j, i <= j -> c{i:=v1}[j:=v2] = c[j:=v2]{i:=v1[j:=v2]}) /\
  (forall (w:val_c) v1 v2 i j, i <= j -> w{i:=v1}[j:=v2] = w[j:=v2]{i:=v1[j:=v2]}) /\
  (forall (ws:list val_c) v1 v2 i j, i <= j -> ws{i:=v1}[j:=v2] = ws[j:=v2]{i:=v1[j:=v2]}) /\
  (forall (bs:list (branch cps)) v1 v2 i j, i <= j -> bs{i:=v1}[j:=v2] = bs[j:=v2]{i:=v1[j:=v2]}) /\
  (forall (fs:list cps) v1 v2 i j, i <= j -> fs{i:=v1}[j:=v2] = fs[j:=v2]{i:=v1[j:=v2]}).
Proof.
  apply my_cps_ind ; simpl ; intros ; auto ;
  try (rewrite H ; auto ; rewrite H0 ; auto ; rewrite H1 ; auto ; fail).
  repeat if_split.
*)
  
(** optimised cps reduction **)
Inductive cps_red : cps -> cps -> Prop :=
| reduce_ret_red :
    forall c c' v v', val_red v v' -> cps_red c c' ->
                      cps_red (Ret_c (Cont_c c) v) (c'[0:=v'])
(*                                                             
| reduce_call_red :
    forall c c' v1 v1' v2 v2',
      val_red v1 v1' -> val_red v2 v2' -> cps_red c c' ->
      cps_red (Call_c (Lam_c c) v1 v2) (c'[0:=v1']{0:=v2'})
| reduce_match_red :
    forall d vs vs' bs c c',
      find_branch d (N.of_nat (length vs)) bs = Some c ->
      vals_red vs vs' -> 
      cps_red c c' -> 
      cps_red (Match_c (Con_c d vs) bs) (usubst_list c' vs')
| reduce_proj_red :
    forall cs n c c' v v',
      nthopt (N.to_nat n) cs = Some c ->
      val_red v v' -> 
      cps_red c c' -> 
      cps_red (Proj_c (Fix_c cs) n v) (Ret_c v' ((Lam_c c'){0:=Fix_c cs}))
*)
| halt_red :
    forall v w, val_red v w -> cps_red (Halt_c v) (Halt_c w)
| ret_red :
    forall v1 v2 w1 w2, val_red v1 w1 -> val_red v2 w2 ->
                        cps_red (Ret_c v1 v2) (Ret_c w1 w2)
| call_red :
    forall v1 v2 v3 w1 w2 w3,
      val_red v1 w1 -> val_red v2 w2 -> val_red v3 w3 ->
      cps_red (Call_c v1 v2 v3) (Call_c w1 w2 w3)
| match_red :
    forall v1 bs1 v2 bs2,
      val_red v1 v2 -> branches_red bs1 bs2 ->
      cps_red (Match_c v1 bs1) (Match_c v2 bs2)
| proj_red :
    forall v1 v2 n1 w1 w2 n2,
      n1 = n2 -> val_red v1 w1 -> val_red v2 w2 ->
      cps_red (Proj_c v1 n1 v2) (Proj_c w1 n2 w2)
with val_red : val_c -> val_c -> Prop :=
| var_red : forall n1 n2, n1 = n2 -> val_red (Var_c n1) (Var_c n2)
| kvar_red : forall n1 n2, n1 = n2 -> val_red (KVar_c n1) (KVar_c n2)
| lam_red : forall c1 c2, cps_red c1 c2 -> val_red (Lam_c c1) (Lam_c c2)
| cont_red : forall c1 c2, cps_red c1 c2 -> val_red (Cont_c c1) (Cont_c c2)
| con_red : forall d1 vs1 d2 vs2,
             d1 = d2 -> vals_red vs1 vs2 ->
             val_red (Con_c d1 vs1) (Con_c d2 vs2)
| fix_red : forall cs1 cs2, fn_list_red cs1 cs2 ->
                            val_red (Fix_c cs1) (Fix_c cs2)
with vals_red : list val_c -> list val_c -> Prop :=
| vals_nil_red : vals_red nil nil
| vals_cons_red : forall v1 v1s v2 v2s,
                   val_red v1 v2 -> vals_red v1s v2s ->
                   vals_red (v1::v1s) (v2::v2s)
with branches_red : list (branch cps) -> list (branch cps) -> Prop :=
     | br_nil_red : branches_red nil nil
     | br_cons_red : forall d1 n1 c1 bs1 d2 n2 c2 bs2,
                      d1 = d2 -> n1 = n2 -> cps_red c1 c2 ->
                      branches_red bs1 bs2 -> 
                      branches_red ((d1,n1,c1)::bs1) ((d2,n2,c2)::bs2)
with fn_list_red : list cps -> list cps -> Prop :=
| fn_nil_red : fn_list_red nil nil
| fn_cons_red : forall c1 c2 cs1 cs2,
                 cps_red c1 c2 -> fn_list_red cs1 cs2 ->
                 fn_list_red (c1::cs1) (c2::cs2).
Hint Constructors fn_list_red vals_red branches_red val_red cps_red.
Scheme cps_red_ind2 := Induction for cps_red Sort Prop
with val_red_ind2 := Induction for val_red Sort Prop
with vals_red_ind2 := Induction for vals_red Sort Prop
with branches_red_ind2 := Induction for branches_red Sort Prop
with fn_list_red_ind2 := Induction for fn_list_red Sort Prop.
Combined Scheme my_cps_red_ind from cps_red_ind2, val_red_ind2,
                vals_red_ind2, branches_red_ind2, fn_list_red_ind2.

Lemma cps_red_refl' :
  (forall c, cps_red c c) /\
  (forall v, val_red v v) /\
  (forall vs, vals_red vs vs) /\
  (forall bs, branches_red bs bs) /\
  (forall fs, fn_list_red fs fs).
Proof.
  apply my_cps_ind ; intros ; eauto.
Qed.
Definition cps_red_refl := proj1 cps_red_refl'.
Definition val_red_refl := proj1 (proj2 cps_red_refl').
Definition vals_red_refl := proj1 (proj2 (proj2 cps_red_refl')).
Definition branches_red_refl := proj1 (proj2 (proj2 (proj2 cps_red_refl'))).
Definition fn_list_red_refl := proj2 (proj2 (proj2 (proj2 cps_red_refl'))).
Hint Resolve val_red_refl cps_red_refl vals_red_refl
     branches_red_refl fn_list_red_refl.

(** unoptimised cps reduction **)
Inductive cps_ured : cps -> cps -> Prop :=
| reduce_ret_ured :
    forall c c' v v', val_ured v v' -> cps_ured c c' ->
                      cps_ured (Ret_c (Cont_c c) v) (c'[0::=v'])
| halt_ured :
    forall v w, val_ured v w -> cps_ured (Halt_c v) (Halt_c w)
| ret_ured :
    forall v1 v2 w1 w2, val_ured v1 w1 -> val_ured v2 w2 ->
                        cps_ured (Ret_c v1 v2) (Ret_c w1 w2)
| call_ured :
    forall v1 v2 v3 w1 w2 w3,
      val_ured v1 w1 -> val_ured v2 w2 -> val_ured v3 w3 ->
      cps_ured (Call_c v1 v2 v3) (Call_c w1 w2 w3)
| match_ured :
    forall v1 bs1 v2 bs2,
      val_ured v1 v2 -> branches_ured bs1 bs2 ->
      cps_ured (Match_c v1 bs1) (Match_c v2 bs2)
| proj_ured :
    forall v1 v2 n1 w1 w2 n2,
      n1 = n2 -> val_ured v1 w1 -> val_ured v2 w2 ->
      cps_ured (Proj_c v1 n1 v2) (Proj_c w1 n2 w2)
with val_ured : val_c -> val_c -> Prop :=
| var_ured : forall n1 n2, n1 = n2 -> val_ured (Var_c n1) (Var_c n2)
| kvar_ured : forall n1 n2, n1 = n2 -> val_ured (KVar_c n1) (KVar_c n2)
| lam_ured : forall c1 c2, cps_ured c1 c2 -> val_ured (Lam_c c1) (Lam_c c2)
| cont_ured : forall c1 c2, cps_ured c1 c2 -> val_ured (Cont_c c1) (Cont_c c2)
| con_ured : forall d1 vs1 d2 vs2,
             d1 = d2 -> vals_ured vs1 vs2 ->
             val_ured (Con_c d1 vs1) (Con_c d2 vs2)
| fix_ured : forall cs1 cs2, fn_list_ured cs1 cs2 ->
                            val_ured (Fix_c cs1) (Fix_c cs2)
with vals_ured : list val_c -> list val_c -> Prop :=
| vals_nil_ured : vals_ured nil nil
| vals_cons_ured : forall v1 v1s v2 v2s,
                   val_ured v1 v2 -> vals_ured v1s v2s ->
                   vals_ured (v1::v1s) (v2::v2s)
with branches_ured : list (branch cps) -> list (branch cps) -> Prop :=
     | br_nil_ured : branches_ured nil nil
     | br_cons_ured : forall d1 n1 c1 bs1 d2 n2 c2 bs2,
                      d1 = d2 -> n1 = n2 -> cps_ured c1 c2 ->
                      branches_ured bs1 bs2 -> 
                      branches_ured ((d1,n1,c1)::bs1) ((d2,n2,c2)::bs2)
with fn_list_ured : list cps -> list cps -> Prop :=
| fn_nil_ured : fn_list_ured nil nil
| fn_cons_ured : forall c1 c2 cs1 cs2,
                 cps_ured c1 c2 -> fn_list_ured cs1 cs2 ->
                 fn_list_ured (c1::cs1) (c2::cs2).
Hint Constructors fn_list_ured vals_ured branches_ured val_ured cps_ured.
Scheme cps_ured_ind2 := Induction for cps_ured Sort Prop
with val_ured_ind2 := Induction for val_ured Sort Prop
with vals_ured_ind2 := Induction for vals_ured Sort Prop
with branches_ured_ind2 := Induction for branches_ured Sort Prop
with fn_list_ured_ind2 := Induction for fn_list_ured Sort Prop.
Combined Scheme my_cps_ured_ind from cps_ured_ind2, val_ured_ind2,
                vals_ured_ind2, branches_ured_ind2, fn_list_ured_ind2.

Lemma cps_ured_refl' :
  (forall c, cps_ured c c) /\
  (forall v, val_ured v v) /\
  (forall vs, vals_ured vs vs) /\
  (forall bs, branches_ured bs bs) /\
  (forall fs, fn_list_ured fs fs).
Proof.
  apply my_cps_ind ; intros ; eauto.
Qed.
Definition cps_ured_refl := proj1 cps_ured_refl'.
Definition val_ured_refl := proj1 (proj2 cps_ured_refl').
Definition vals_ured_refl := proj1 (proj2 (proj2 cps_ured_refl')).
Definition branches_ured_refl := proj1 (proj2 (proj2 (proj2 cps_ured_refl'))).
Definition fn_list_ured_refl := proj2 (proj2 (proj2 (proj2 cps_ured_refl'))).
Hint Resolve val_ured_refl cps_ured_refl vals_ured_refl
     branches_ured_refl fn_list_ured_refl.

(** optimised and unoptimised reduction relations are equivalent **)
Lemma redc_uredc:
  (forall c d:cps, cps_red c d -> cps_ured c d) /\
  (forall v u:val_c, val_red v u -> val_ured v u) /\
  (forall vs us, vals_red vs us -> vals_ured vs us) /\
  (forall bs cs, branches_red bs cs -> branches_ured bs cs) /\
  (forall bs cs, fn_list_red bs cs -> fn_list_ured bs cs).
Proof.
  apply my_cps_red_ind; simpl; intros; intuition.
  - rewrite ksubst_ksbst_cps_0. constructor; assumption.
Qed.

Lemma kshft_pres_ured :
  (forall c1 c2, cps_ured c1 c2 ->
   forall j, cps_ured (kshft_cps j c1) (kshft_cps j c2)) /\
  (forall v1 v2, val_ured v1 v2 ->
   forall j, val_ured (kshft_val j v1) (kshft_val j v2)) /\
  (forall vs1 vs2, vals_ured vs1 vs2 ->
   forall j, vals_ured (kshft_vals j vs1) (kshft_vals j vs2)) /\
  (forall bs1 bs2, branches_ured bs1 bs2 ->
   forall j, branches_ured (kshft_branches j bs1) 
                            (kshft_branches j bs2)) /\
  (forall fs1 fs2, fn_list_ured fs1 fs2 ->
   forall j, fn_list_ured (kshft_fn_list j fs1) (kshft_fn_list j fs2)).
Proof.
  apply my_cps_ured_ind; simpl; intros; subst; try constructor; intuition.
  - change (cps_ured (Ret_c (Cont_c (kshft_cps (1 + j) c)) (kshft_val j v))
     (kshft_cps j (c'[0::=v']))).
    rewrite cps_kshft_ksbst. rewrite (N_i_plus_1 j).
    apply (reduce_ret_ured _ _ _ _ (H j) (H0 (1+j))). lia.
Qed.
Definition cps_kshft_pres_ured := proj1 kshft_pres_ured.
Definition val_kshft_pres_ured := proj1 (proj2 kshft_pres_ured).

(**
Lemma ushft_pres_ured :
  (forall c1 c2, cps_ured c1 c2 ->
   forall j, cps_ured (ushft_cps j c1) (ushft_cps j c2)) /\
  (forall v1 v2, val_ured v1 v2 ->
   forall j, val_ured (ushft_val j v1) (ushft_val j v2)) /\
  (forall vs1 vs2, vals_ured vs1 vs2 ->
   forall j, vals_ured (ushft_vals j vs1) (ushft_vals j vs2)) /\
  (forall bs1 bs2, branches_ured bs1 bs2 ->
   forall j, branches_ured (ushft_branches j bs1) (ushft_branches j bs2)) /\
  (forall fs1 fs2, fn_list_ured fs1 fs2 ->
   forall j, fn_list_ured (ushft_fn_list j fs1) (ushft_fn_list j fs2)).
Proof.
  apply my_cps_ured_ind; simpl; intros; subst; try constructor; intuition.
  - change (cps_ured (Ret_c (Cont_c (ushft_cps j c)) (ushft_val j v))
                     (ushft_cps j (c'[0::=v']))).

    apply reduce_ret_ured. constructor.

Lemma ushift_pres_ured :
  (forall c1 c2, cps_ured c1 c2 ->
   forall j n, cps_ured (ushift_cps j n c1) (ushift_cps j n c2)) /\
  (forall v1 v2, val_ured v1 v2 ->
   forall j n, val_ured (ushift_val j n v1) (ushift_val j n v2)) /\
  (forall vs1 vs2, vals_ured vs1 vs2 ->
   forall j n, vals_ured (ushift_vals j n vs1) (ushift_vals j n vs2)) /\
  (forall bs1 bs2, branches_ured bs1 bs2 ->
   forall j n, branches_ured (ushift_branches j n bs1) 
                            (ushift_branches j n bs2)) /\
  (forall fs1 fs2, fn_list_ured fs1 fs2 ->
   forall j n, fn_list_ured (ushift_fn_list j n fs1) (ushift_fn_list j n fs2)).
Proof.
  apply my_cps_ured_ind; simpl; intros; subst; try constructor; intuition.
  - change (cps_ured (Ret_c (Cont_c (ushift_cps j n c)) (ushift_val j n v))
                     (ushift_cps j n (c'[0::=v']))).
    apply reduce_ret_ured. constructor.

  - change (cps_ured (Ret_c (Cont_c (ushift_cps (1 + j) c)) (ushift_val j v))
     (ushift_cps j (c'[0::=v']))).
    rewrite cps_ushift_ksbst. rewrite (N_i_plus_1 j).
    apply (reduce_ret_ured _ _ _ _ (H j) (H0 (1+j))). lia.
Qed.
Definition cps_ushift_pres_ured := proj1 ushift_pres_ured.
Definition val_ushift_pres_ured := proj1 (proj2 ushift_pres_ured).
**)

Lemma pre_uL1:  (** continuation variables **)
  (forall c, forall v1 v2, val_ured v1 v2 ->
     forall n, cps_ured (c[n ::= v1]) (c[n::= v2])) /\
  (forall u, forall v1 v2, val_ured v1 v2 ->
     forall n, val_ured (u[n ::= v1]) (u[n::= v2])) /\
  (forall u, forall v1 v2, val_ured v1 v2 ->
     forall n, vals_ured (u[n ::= v1]) (u[n::= v2])) /\
  (forall u, forall v1 v2, val_ured v1 v2 ->
     forall n, branches_ured (u[n ::= v1]) (u[n::= v2])) /\
  (forall u, forall v1 v2, val_ured v1 v2 ->
     forall n, fn_list_ured (u[n ::= v1]) (u[n::= v2])).
Proof.
  apply my_cps_ind; simpl; intros; intuition.
  - if_split. destruct (N.eq_dec n n0).
    + assumption.
    + apply val_ured_refl.
  - constructor. apply H. apply kshft_pres_ured. assumption.
  - constructor. apply H. apply kshft_pres_ured. assumption.
  - constructor.
    + apply H. apply kshft_pres_ured. assumption.
    + apply H0. assumption.
Qed.
Definition cps_pre_uL1 := proj1 pre_uL1.
Definition val_pre_uL1 := proj1 (proj2 pre_uL1).

Lemma uL1:  (** continuation variables **)
  (forall c1 c2, cps_ured c1 c2 -> forall v1 v2, val_ured v1 v2 ->
     forall n, cps_ured (c1[n ::= v1]) (c2[n::= v2])) /\
  (forall u1 u2, val_ured u1 u2 -> forall v1 v2, val_ured v1 v2 ->
     forall n, val_ured (u1[n ::= v1]) (u2[n::= v2])) /\
  (forall u1 u2, vals_ured u1 u2 -> forall v1 v2, val_ured v1 v2 ->
     forall n, vals_ured (u1[n ::= v1]) (u2[n::= v2])) /\
  (forall u1 u2, branches_ured u1 u2 -> forall v1 v2, val_ured v1 v2 ->
     forall n, branches_ured (u1[n ::= v1]) (u2[n::= v2])) /\
  (forall u1 u2, fn_list_ured u1 u2 -> forall v1 v2, val_ured v1 v2 ->
     forall n, fn_list_ured (u1[n ::= v1]) (u2[n::= v2])).
Proof.
  apply my_cps_ured_ind; simpl; intros; intuition.
  - rewrite <- ksbst_ksbst_cps; try lia.
    change (cps_ured
     (Ret_c (Cont_c (c[1+n::=kshft_val 0 v1])) (v[n::= v1]))
     ((c' [n + 1 ::= kshft_val 0 v2]) [0 ::= v' [n ::= v2]])).
    apply (reduce_ret_ured (c[1+n::=kshft_val 0 v1])
                           (c' [n + 1 ::= kshft_val 0 v2])).
    + apply H. assumption.
    + rewrite (N_i_plus_1). apply H0.
      apply val_kshft_pres_ured. assumption.
  - repeat if_split.
  - constructor. apply H. apply val_kshft_pres_ured. assumption.
  - constructor. apply H. apply val_kshft_pres_ured. assumption.
  - constructor.
    + apply H. apply val_kshft_pres_ured. assumption.
    + apply H0. assumption.
Qed.
Definition cps_uL1 := proj1 uL1.
Definition val_uL1 := proj1 (proj2 uL1).

Lemma pre_UL1:  (** user variables **)
  (forall c, forall v1 v2, val_ured v1 v2 ->
     forall n, cps_ured (c{n ::= v1}) (c{n::= v2})) /\
  (forall u, forall v1 v2, val_ured v1 v2 ->
     forall n, val_ured (u{n ::= v1}) (u{n::= v2})) /\
  (forall u, forall v1 v2, val_ured v1 v2 ->
     forall n, vals_ured (u{n ::= v1}) (u{n::= v2})) /\
  (forall u, forall v1 v2, val_ured v1 v2 ->
     forall n, branches_ured (u{n ::= v1}) (u{n::= v2})) /\
  (forall u, forall v1 v2, val_ured v1 v2 ->
     forall n, fn_list_ured (u{n ::= v1}) (u{n::= v2})).
Proof.
  apply my_cps_ind; simpl; intros; intuition.
  - if_split. destruct (N.eq_dec n n0).
    + assumption.
    + apply val_ured_refl.
Qed.

Lemma uL1:  (** user variables **)
  (forall c1 c2, cps_ured c1 c2 -> forall v1 v2, val_ured v1 v2 ->
     forall n, cps_ured (c1{n ::= v1}) (c2{n::= v2})) /\
  (forall u1 u2, val_ured u1 u2 -> forall v1 v2, val_ured v1 v2 ->
     forall n, val_ured (u1{n ::= v1}) (u2{n::= v2})) /\
  (forall u1 u2, vals_ured u1 u2 -> forall v1 v2, val_ured v1 v2 ->
     forall n, vals_ured (u1{n ::= v1}) (u2{n::= v2})) /\
  (forall u1 u2, branches_ured u1 u2 -> forall v1 v2, val_ured v1 v2 ->
     forall n, branches_ured (u1{n ::= v1}) (u2{n::= v2})) /\
  (forall u1 u2, fn_list_ured u1 u2 -> forall v1 v2, val_ured v1 v2 ->
     forall n, fn_list_ured (u1{n ::= v1}) (u2{n::= v2})).
Proof.
  apply my_cps_ured_ind; simpl; intros; intuition.
  - rewrite <- ksbst_ksbst_cps; try lia.
    change (cps_ured
     (Ret_c (Cont_c (c{1+n::=kshft_val 0 v1})) (v{n::= v1}))
     ((c' {n + 1 ::= kshft_val 0 v2}) {0 ::= v' {n ::= v2}})).
    apply (reduce_ret_ured (c{1+n::=kshft_val 0 v1})
                           (c' {n + 1 ::= kshft_val 0 v2})).
    + apply H. assumption.
    + rewrite (N_i_plus_1). apply H0.
      apply val_kshft_pres_ured. assumption.
  - repeat if_split.
  - constructor. apply H. apply val_kshft_pres_ured. assumption.
  - constructor. apply H. apply val_kshft_pres_ured. assumption.
  - constructor.
    + apply H. apply val_kshft_pres_ured. assumption.
    + apply H0. assumption.
Qed.
Definition cps_uL1 := proj1 uL1.
Definition val_uL1 := proj1 (proj2 uL1).

Lemma cps_ured_sound :
  forall c v, ueval_c c v -> forall c', cps_ured c c' ->
    exists v', ueval_c c' v' /\ val_ured v v'.
Proof.
  induction 1 ; intros; assert (j:= val_ured_refl).
  * inversion H ; subst ; eauto.
  * inversion H0 ; subst ; clear H0.
    apply IHueval_c. apply cps_uL1 ; auto.
    inversion H3 ; clear H3 ; subst. Check (cps_uL1 _ _ H1 _ _ H5 _).
    specialize (IHueval_c (c2 [0 ::= w2]) (cps_uL1 _ _ H1 _ _ H5 _)).
    destruct IHueval_c as [w [H2 H3]]. eauto.
  * inversion H0 ; subst. clear H0. inversion H4 ; subst. clear H4.
    specialize (IHueval_c (c2[0::= w2]{0:=w3})).
    Check (cps_uL1 _ _ H1).
    destruct (IHueval_c _ (cps_uL1 _ _ H1 _ _ _ _)) as [w [H6 H7]] ; eauto.
Check (cps_uL1 _ _ H1 _ _ H6).
    apply (cps_uL1 _ _ H1 _ _ H6). cps_uL1 ; eauto.
    inversion H3 ; subst ; clear H3.
    destruct (IHeval_c _ (cps_red_ksubst _ _ H1 _ _ 0 H5)) as [w [H6 H7]] ; eauto
Lemma cps_red_usound :
  forall c v, ueval_c c v -> forall c', cps_ured c c' ->
    exists v', ueval_c c' v' /\ val_ured v v'.
Proof.
  induction 1 ; intros.
  * exists v. intuition. inversion H ; subst ; eauto.
  * inversion H0 ; subst ; clear H0.
    apply IHeval_c. apply cps_red_ksubst ; auto.
    inversion H3 ; clear H3 ; subst.
    specialize (IHeval_c (c2 [0 := w2]) (cps_red_ksubst _ _ H1 _ _ 0 H5)).
    destruct IHeval_c as [w [H2 H3]]. eauto.
  * inversion H0 ; clear H0 ; subst. inversion H4 ; clear H4 ; subst.
    specialize (IHeval_c (c2[0:= w2]{0:=w3})).



Goal
  forall c v, ueval_c c v -> forall v', val_ured v v' -> 
      exists c', cps_ured c c'.
Proof.
  induction 1; intros u h.
  - exists (Halt_c u). constructor. assumption.
  - 


Lemma cps_red_usound :
  forall c v, ueval_c c v -> forall c', cps_ured c c' ->
    exists v', ueval_c c' v' /\ val_ured v v'.
Proof.
  induction 1 ; intros.
  - inversion H; subst; clear H. exists w. intuition. constructor.
  - inversion H0; subst; clear H0.
    + apply IHueval_c. apply cps_uL1; assumption.
    + inversion H3; subst; clear H3.
      destruct (IHueval_c (c [0 ::= v]) (cps_ured_refl _)) as [x [j1 j2]].
      exists x. intuition.
      constructor. admit.
  - inversion H0; subst; clear H0. inversion H4. subst.
    inversion H4. subst. clear H4.
    exists v'. split. apply (proj2 (ueval_call _ _ _ _)). admit. admit.
  - inversion H1. subst. inversion H1. subst. clear H1. admit.
  -  inversion H1. subst. 


apply IHueval_c. 



ksbst_pres_ueval
ueval_single valued.


    + inversion H; subst; clear H.

apply IHueval_c. apply uL1; assumption.
    + assert (j:= cps_ured (c [0 ::= v]) (c'0 [0 ::= v'0])).


Require Import Relations.

Definition cps_red_star := clos_refl_trans cps cps_red.
Definition val_red_star := clos_refl_trans val_c val_red.
Definition vals_red_star := clos_refl_trans (list val_c) vals_red.
Definition branches_red_star := clos_refl_trans _ branches_red.
Definition fn_list_red_star := clos_refl_trans _ fn_list_red.


Lemma length_ksubst_vals :
  forall v i vs, length (ksubst_vals v i vs) = length vs.
Proof.
  induction vs ; simpl ; intros ; auto.
Qed.

Lemma find_ksubst_branch :
  forall d n bs c v i, 
    find_branch d n bs = Some c ->
    find_branch d n (ksubst_branches v i bs) = Some (ksubst_cps v i c).
Proof.
  induction bs ; simpl ; intros ; try discriminate. unfold ksubst_branch ; unfold br in *.
  destruct a ; destruct p.
  destruct (N.eq_dec d d0) ; destruct (N.eq_dec n0 n) ; try discriminate ; subst.
  congruence. apply IHbs ; auto. apply IHbs ; auto.
Qed.

(*
Lemma ksubst_usubst_comm' :
  (forall (c:cps) v1 v2 i j, (c{i:=v1})[j:=v2] = (c[j:=v2]){i:=v1[j:=v2]}) /\
  (forall (w:val_c) v1 v2 i j, w{i:=v1}[j:=v2] = w[j:=v2]{i:=v1[j:=v2]}) /\
  (forall (ws:list val_c) v1 v2 i j, ws{i:=v1}[j:=v2] = ws[j:=v2]{i:=v1[j:=v2]}) /\
  (forall (bs:list (branch cps)) v1 v2 i j, bs{i:=v1}[j:=v2] = bs[j:=v2]{i:=v1[j:=v2]}) /\
  (forall (fs:list cps) v1 v2 i j, fs{i:=v1}[j:=v2] = fs[j:=v2]{i:=v1[j:=v2]}).
Proof.
  apply my_cps_ind ; simpl ; intros ; auto ;
  try (rewrite H ; auto ; rewrite H0 ; auto ; rewrite H1 ; auto ; fail).
  repeat if_split.
Admitted.

Lemma ksubst_usubst_list_comm :
  forall vs i v c,
    (usubst_list c vs)[i:=v] = usubst_list (c[i:=v]) (vs[i:=v]).
Proof.
  induction vs ; simpl in * ; intros ; auto.
  rewrite IHvs. rewrite (proj1 ksubst_usubst_comm'). auto.
Qed.
*)

Lemma nth_ksubst_fn_list :
  forall n cs c v i,
    nthopt n cs = Some c ->
    nthopt n (ksubst_fn_list v i cs) = Some (ksubst_cps v (1+i) c).
Proof.
  induction n ; destruct cs ; simpl ; intros ; try discriminate. congruence.
  apply IHn ; auto.
Qed.

(*
Lemma ksubst_kshift2 :
  (forall c i j k l v, ksubst_cps (kshift_val i j v) k (kshift_cps i (l+j) c) =
                     kshift_cps i j (ksubst_cps v k c)) /\
  (forall w i j k l v, ksubst_val (kshift_val i j v) k (kshift_val i (l+j) w) =
                     kshift_val i j (ksubst_val v k w)) /\
  (forall ws i j k l v, ksubst_vals (kshift_val i j v) k (kshift_vals i (l+j) ws) =
                                 kshift_vals i j (ksubst_vals v k ws)) /\
  (forall bs i j k l v, ksubst_branches (kshift_val i j v) k (kshift_branches i (l+j) bs) =
                        kshift_branches i j (ksubst_branches v k bs)) /\
  (forall fs i j k l v, ksubst_fn_list (kshift_val i j v) k (kshift_fn_list i (l+j) fs) =
                      kshift_fn_list i j (ksubst_fn_list v k fs)).
Proof.
  apply my_cps_ind ; simpl ; intros ; auto.
  rewrite H ; auto.
  rewrite H ; rewrite H0 ; auto.
  rewrite H ; rewrite H0 ; rewrite H1 ; auto.
  rewrite H ; rewrite H0 ; auto.
  rewrite H ; rewrite H0 ; auto.
  Focus 2.
  specialize (H i j (1+k) (1+l) v).
  replace (1 + (l + j)) with (1 + l + j) ; try lia. rewrite H.
  try (auto ; rewrite H ; auto ; rewrite H0 ; auto ; rewrite H1 ; auto ; fail).
  repeat if_split.

  (shift i l c)[k := (shift i j v)
  Admitted.
*)


Lemma cps_red_ksubst' :
  (forall c1 c2, cps_red c1 c2 ->
   forall v1 v2 i, val_red v1 v2 -> cps_red (c1[i:=v1]) (c2[i:=v2])) /\
  (forall w1 w2, val_red w1 w2 ->
   forall v1 v2 i, val_red v1 v2 -> val_red (w1[i:=v1]) (w2[i:=v2])) /\
  (forall ws1 ws2, vals_red ws1 ws2 ->
   forall v1 v2 i, val_red v1 v2 -> vals_red (ws1[i:=v1]) (ws2[i:=v2])) /\
  (forall bs1 bs2, branches_red bs1 bs2 ->
   forall v1 v2 i, val_red v1 v2 -> branches_red (bs1[i:=v1]) (bs2[i:=v2])) /\
  (forall fs1 fs2, fn_list_red fs1 fs2 ->
   forall v1 v2 i, val_red v1 v2 -> fn_list_red (fs1[i:=v1]) (fs2[i:=v2])).
Proof.
  Opaque N.add.
  apply my_cps_red_ind ; simpl in * ; intros ; eauto.
  - rewrite (proj1 ksubst_comm) ; try lia.
    replace (i - 0) with i ; try lia. eauto.
  - subst. repeat if_split. apply cps_red_kshift ; auto.
Qed.
Definition cps_red_ksubst := proj1 cps_red_ksubst'.


(*** 
Lemma cps_red_ushift :
  (forall c1 c2, cps_red c1 c2 ->
                 forall i j, cps_red (ushift_cps i j c1) (ushift_cps i j c2)) /\
  (forall v1 v2, val_red v1 v2 ->
                 forall i j, val_red (ushift_val i j v1) (ushift_val i j v2)) /\
  (forall vs1 vs2, vals_red vs1 vs2 ->
                   forall i j, vals_red (ushift_vals i j vs1) (ushift_vals i j vs2)) /\
  (forall bs1 bs2, branches_red bs1 bs2 ->
                   forall i j, branches_red (ushift_branches i j bs1) (ushift_branches i j bs2)) /\
  (forall fs1 fs2, fn_list_red fs1 fs2 ->
                   forall i j, fn_list_red (ushift_fn_list i j fs1) (ushift_fn_list i j fs2)).
Proof.
  apply my_cps_red_ind ; intros ; subst ; simpl ; try (constructor ; eauto ; fail).
  replace (ushift_cps i j (usubst_cps v' 0 c')) with (usubst_cps (ushift_val i j v') 0 (ushift_cps i (1+j) c')).
  constructor ; eauto.
Admitted.

Lemma cps_red_usubst' :
  (forall c1 c2, cps_red c1 c2 ->
                 forall v1 v2 i, val_red v1 v2 -> cps_red (c1{i:=v1}) (c2{i:=v2})) /\
  (forall w1 w2, val_red w1 w2 ->
                 forall v1 v2 i, val_red v1 v2 -> val_red (w1{i:=v1}) (w2{i:=v2})) /\
  (forall ws1 ws2, vals_red ws1 ws2 ->
                 forall v1 v2 i, val_red v1 v2 -> vals_red (ws1{i:=v1}) (ws2{i:=v2})) /\
  (forall bs1 bs2, branches_red bs1 bs2 ->
                 forall v1 v2 i, val_red v1 v2 -> branches_red (bs1{i:=v1}) (bs2{i:=v2})) /\
  (forall fs1 fs2, fn_list_red fs1 fs2 ->
                   forall v1 v2 i, val_red v1 v2 -> fn_list_red (fs1{i:=v1}) (fs2{i:=v2})).
Proof.
  apply my_cps_red_ind ; simpl ; intros ; subst ; eauto.
  Focus 2.
  repeat if_split.
  
Definition cps_red_usubst := proj1 cps_red_usubst'.


Lemma cps_red_usubst_list :
  forall v1s v2s, vals_red v1s v2s ->
                forall c1 c2, cps_red c1 c2 -> cps_red (usubst_list c1 v1s) (usubst_list c2 v2s).
Proof.
  induction 1 ; simpl ; auto ; intros.
  apply IHvals_red. apply cps_red_usubst ; auto.
Qed.
*)

Lemma find_branch_pres_red :
  forall bs1 bs2, branches_red bs1 bs2 ->
    forall d n c1, find_branch d n bs1 = Some c1 ->
      exists c2, (find_branch d n bs2 = Some c2 /\ cps_red c1 c2).
Proof.
  induction 1 ; simpl ; intros. discriminate.
  subst. destruct (N.eq_dec d d2). subst.
  destruct (N.eq_dec n2 n) ; try discriminate.
  injection H3 ; intros ; subst. eauto.
  apply IHbranches_red. auto.
Qed.

Lemma fn_list_pres_red :
  forall n fs1 fs2, fn_list_red fs1 fs2 ->
    forall c1, nthopt n fs1 = Some c1 ->
      exists c2, (nthopt n fs2 = Some c2 /\ cps_red c1 c2).
Proof.
  induction n ; simpl in *; intros.
  inversion H ; subst ; try discriminate ; clear H.
  injection H0 ; intros ; subst. eauto.
  inversion H ; subst ; try discriminate ; clear H.
  apply (IHn _ _ H2 _ H0).
Qed.

Lemma fn_list_red_same_len :
  forall fs1 fs2, fn_list_red fs1 fs2 -> length fs1 = length fs2.
Proof.
  induction 1 ; simpl ; intros ; subst ; auto.
Qed.  
  
Lemma vals_red_same_len :
  forall vs1 vs2, vals_red vs1 vs2 -> length vs1 = length vs2.
Proof.
  induction 1 ; simpl ; intros ; auto.
Qed.



Lemma cps_red_sound :
  forall c v, eval_c c v -> forall c', cps_red c c' ->
    exists v', eval_c c' v' /\ val_red v v'.
Proof.
  Hint Constructors eval_c.
  induction 1 ; intros; assert (j:= val_red_refl)
  * inversion H ; subst ; eauto.
  * inversion H0 ; subst ; clear H0.
    apply IHeval_c. apply cps_red_ksubst ; auto.
    inversion H3 ; clear H3 ; subst.
    specialize (IHeval_c (c2 [0 := w2]) (cps_red_ksubst _ _ H1 _ _ 0 H5)).
    destruct IHeval_c as [w [H2 H3]]. eauto.
  * inversion H0 ; clear H0 ; subst. inversion H4 ; clear H4 ; subst.
    specialize (IHeval_c (c2[0:= w2]{0:=w3})).


    apply cps_red_ksubst ; eauto.
    inversion H3 ; subst ; clear H3.
    destruct (IHeval_c _ (cps_red_ksubst _ _ H1 _ _ 0 H5)) as [w [H6 H7]] ; eauto.
  * inversion H0 ; subst ; clear H0.
    apply IHeval_c. apply cps_red_usubst ; eauto. apply cps_red_ksubst ; eauto.
    inversion H4 ; subst ; clear H4.
    specialize (cps_red_ksubst _ _ H1 _ _ 0 H6) ; intro.
    specialize (cps_red_usubst _ _ H0 _ _ 0 H7) ; intro.
    specialize (IHeval_c _ H2). destruct IHeval_c as [w [H8 H9]] ; eauto.
  * inversion H1 ; clear H1 ; subst.
    rewrite H in H5. injection H5 ; intros ; subst ; clear H5.
    apply IHeval_c. eapply cps_red_usubst_list ; eauto.
    inversion H4 ; subst ; clear H4.
    destruct (find_branch_pres_red _ _ H6 _ _ _ H) as [c' [H8 H9]].
    specialize (cps_red_usubst_list _ _ H7 _ _ H9). intro.
    specialize (IHeval_c _ H1). destruct IHeval_c as [v [H10 H11]].
    exists v. rewrite (vals_red_same_len _ _ H7) in H8. eauto.
  * inversion H1 ; subst ; clear H1. rewrite H in H5.
    injection H5 ; intros ; subst ; clear H5. apply IHeval_c.
    apply ret_red ; auto. simpl. apply lam_red.
    apply (cps_red_usubst _ _ H8 (Fix_c cs) _ 1 (val_red_refl _)). 
    inversion H7 ; subst ; clear H7.
    destruct (fn_list_pres_red _ _ _ H2 _ H) as [c' [H9 H10]].
    assert (cps_red (Ret_c k ((Lam_c c) {0 := Fix_c cs}))
                    (Ret_c w2 ((Lam_c c'){0 := Fix_c cs2}))).
    constructor. auto. simpl. constructor ; auto.
    eapply (cps_red_usubst) ; eauto.
    specialize (IHeval_c _ H1). destruct IHeval_c as [v [H11 H12]].
    exists v ; eauto.
Qed.

(* Todo:

1. replace nat with positive or BinNat's [Done]
2. Adam-ize
   * introduce lemmas, hints to make proofs go through easier
3. Add constructors  C(e1,...,en) [Done]
4. Add pattern matching [Done]
5. Add mutually recursive functions [Done]
6. Add let to the source [Done]
7. Relate to optimized translation -- 
   requires setting up a Beta-value relation.

*)*)
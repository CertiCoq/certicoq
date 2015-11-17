(** Naive conversion to continuation-passing style for a core language including
    mutually recursive functions, data constructors, and pattern matching.
*)
Require Import Arith BinNat String List Omega Program Psatz.
Open Scope N_scope.
Opaque N.add.
Opaque N.sub.
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

(* data constructors *)
Definition dcon := N.

(** Source expressions, represented using deBruijn notation *)
Definition branch(A:Type):Type := (dcon * N * A)%type.
Inductive exp : Type :=
| Var_e : N -> exp
| Lam_e : exp -> exp
| App_e : exp -> exp -> exp
| Con_e : dcon -> (list exp) -> exp
| Match_e : exp -> (list (branch exp)) -> exp
| Let_e : exp -> exp -> exp
| Fix_e : (list exp) -> N -> exp.  (* implicitly lambdas *)

(* A few notes on the source:  

   [Let_e e1 e2] corresponds to (let x0 := e1 in e2)

   [Fix_e [e1;e2;...;en] i] produces a projection of an n-tuple of
   functions.  Each expression is treated as binding the n functions.

   So this is similar to saying something like:

    let rec f1 = e1
        and f2 = e2
        ...
        and fn = en
    in fi

   For [Match_e] each [branch] binds [n] variables, corresponding to the
   arguments to the data constructor.  
*)


(** Induction scheme for expressions. *)
Section EXP_SCHEME.
  Variable Pexp : exp -> Prop.
  Variable Pexps : list exp -> Prop.
  Variable Pbranches : list (dcon * N * exp) -> Prop.

  Variable var_e : forall n, Pexp (Var_e n).
  Variable lam_e : forall {e}, Pexp e -> Pexp (Lam_e e).
  Variable app_e : forall {e1 e2}, Pexp e1 -> Pexp e2 -> Pexp (App_e e1 e2).
  Variable con_e : forall d {es}, Pexps es -> Pexp (Con_e d es).
  Variable match_e : forall {e bs}, Pexp e -> Pbranches bs -> Pexp (Match_e e bs).
  Variable let_e : forall {e1 e2}, Pexp e1 -> Pexp e2 -> Pexp (Let_e e1 e2).
  Variable fix_e : forall {es} i, Pexps es -> Pexp (Fix_e es i).
  Variable nil_es : Pexps nil.
  Variable cons_es : forall {e es}, Pexp e -> Pexps es -> Pexps (e::es).
  Variable nil_bs : Pbranches nil.
  Variable cons_bs : forall d n {e bs}, Pexp e -> Pbranches bs -> Pbranches ((d,n,e)::bs).

  Section MY_EXP_IND.
     Variable my_exp_ind : forall e, Pexp e.

     Fixpoint my_exps_ind' (es:list exp) : Pexps es :=
       match es return Pexps es with
         | nil => nil_es
         | e::es' => cons_es _ _ (my_exp_ind e) (my_exps_ind' es')
       end.

     Fixpoint my_branches_ind' (bs: list (dcon * N * exp)) : Pbranches bs :=
         match bs return Pbranches bs with
           | nil => nil_bs
           | (d,n,e)::bs' => cons_bs d n _ _ (my_exp_ind e) (my_branches_ind' bs')
         end.
  End MY_EXP_IND.

  Fixpoint my_exp_ind' (e:exp) : Pexp e :=
    match e return Pexp e with
      | Var_e n => var_e n
      | Lam_e e => lam_e _ (my_exp_ind' e)
      | App_e e1 e2 => app_e _ _ (my_exp_ind' e1) (my_exp_ind' e2)
      | Con_e d es => con_e d _ (my_exps_ind' my_exp_ind' es)
      | Match_e e bs => match_e _ _ (my_exp_ind' e) (my_branches_ind' my_exp_ind' bs)
      | Let_e e1 e2 => let_e _ _ (my_exp_ind' e1) (my_exp_ind' e2)
      | Fix_e es i => fix_e _ i (my_exps_ind' my_exp_ind' es)
    end.

  Definition my_exp_ind :
    (forall e, Pexp e) /\ (forall es, Pexps es) /\ (forall bs, Pbranches bs) := 
    (conj my_exp_ind' (conj (my_exps_ind' my_exp_ind') (my_branches_ind' my_exp_ind'))).
End EXP_SCHEME.

(** [exp_wf i e] ensures there is no free variable above [i]. *)
Inductive exp_wf : N -> exp -> Prop :=
| var_e_wf : forall i j, j < i -> exp_wf i (Var_e j)
| lam_e_wf : forall i e, exp_wf (1 + i) e -> exp_wf i (Lam_e e)
| app_e_wf : forall i e1 e2, exp_wf i e1 -> exp_wf i e2 -> exp_wf i (App_e e1 e2)
| con_e_wf : forall i d es, exps_wf i es -> exp_wf i (Con_e d es)
| match_e_wf : forall i e bs, exp_wf i e -> branches_wf i bs -> exp_wf i (Match_e e bs)
| let_e_wf : forall i e1 e2, exp_wf i e1 -> exp_wf (1 + i) e2 -> exp_wf i (Let_e e1 e2)
| fix_e_wf : forall i es k, exps_wf (2 + i) es -> exp_wf i (Fix_e es k)
with exps_wf : N -> list exp -> Prop :=
| nil_wf : forall i, exps_wf i nil
| cons_wf : forall i e es, exp_wf i e -> exps_wf i es -> exps_wf i (e::es)
with branches_wf : N -> list (dcon * N * exp) -> Prop :=
| nilb_wf : forall i, branches_wf i nil
| consb_wf : forall i d n e bs, exp_wf (n + i) e -> branches_wf i bs -> branches_wf i ((d,n,e)::bs).
Hint Constructors exp_wf exps_wf branches_wf.
Scheme exp_wf_ind2 := Induction for exp_wf Sort Prop
with exps_wf_ind2 := Induction for exps_wf Sort Prop
with branches_wf_ind2 := Induction for branches_wf Sort Prop.
Combined Scheme my_exp_wf_ind from exp_wf_ind2, exps_wf_ind2, branches_wf_ind2.

(** Weakening with respect to [exp_wf]. *)
Lemma weaken_wf' :
  (forall i e, exp_wf i e -> forall j, i < j -> exp_wf j e) /\
  (forall i es, exps_wf i es -> forall j, i < j -> exps_wf j es) /\
  (forall i bs, branches_wf i bs -> forall j, i < j -> branches_wf j bs).
Proof.  
  apply my_exp_wf_ind ; intros ; econstructor ; auto ; try lia ; 
  match goal with
    | [ H : forall _, _ -> exp_wf _ ?e |- exp_wf _ ?e] => apply H ; lia
    | _ => idtac                                                                      
  end. apply (H (2 + j)). lia.
Qed.
  
Lemma weaken_wf : forall i e, exp_wf i e -> forall j, i < j -> exp_wf j e.
  apply (proj1 weaken_wf').
Qed.

(** We can always weaken a closed expression. *)
Lemma weaken_closed : forall e i, exp_wf 0 e -> exp_wf i e.
  intros. destruct i ; auto ; eapply weaken_wf ; eauto ; lia.
Qed.

Lemma weaken_closeds: forall es i, exps_wf 0 es -> exps_wf i es.
  intros ; destruct i ; auto ; eapply (proj1 (proj2 weaken_wf')) ; eauto ; lia.
Qed.

Lemma weaken_branches: forall bs i, branches_wf 0 bs -> branches_wf i bs.
  intros ; destruct i ; auto ; eapply (proj2 (proj2 weaken_wf')) ; eauto ; lia.
Qed.

Hint Resolve weaken_closed weaken_closeds weaken_branches.

Definition br{A B:Type}(f:dcon -> N -> A -> B) (b:branch A) : B := 
  match b with
    | (d,n,e) => f d n e
  end.

(** Shift all variables [i] equal or above [k] by [n]. *)
Section SHIFT.
  Variable shift : N -> N -> exp -> exp.
  Definition shifts' n k es := List.map (shift n k) es.
  Definition shift_branch' (i k:N) (b:dcon*N*exp) := br (fun d n e => (d,n,shift i (n+k) e)) b.
  Definition shift_branches' n k bs := List.map (shift_branch' n k) bs.
End SHIFT.

Fixpoint shift n k e := 
  match e with
    | Var_e i => Var_e (if lt_dec i k then i else i + n)
    | App_e e1 e2 => App_e (shift n k e1) (shift n k e2)
    | Lam_e e' => Lam_e (shift n (1 + k) e')
    | Con_e d es => Con_e d (shifts' shift n k es)
    | Let_e e1 e2 => Let_e (shift n k e1) (shift n (1 + k) e2)
    | Match_e e bs => Match_e (shift n k e) (shift_branches' shift n k bs)
    | Fix_e es i => Fix_e (shifts' shift n (2 + k) es) i
  end.
Definition shifts := shifts' shift.
Definition shift_branch := shift_branch' shift.
Definition shift_branches := shift_branches' shift.

(** Substitute [v] for variable [k] in [e]. *)
Section SUBST.
  Variable subst : exp -> N -> exp -> exp.
  Definition substs' v k es := List.map (subst v k) es.
  Definition subst_branch' v k b := br (fun d n e => (d,n,subst v (n+k) e)) b.
  Definition subst_branches' v k bs := List.map (subst_branch' v k) bs.
End SUBST.
  
Fixpoint subst (v:exp) k (e:exp) : exp :=
  match e with
    | Var_e i => if lt_dec i k then Var_e i
                 else if eq_dec i k then shift k 0 v
                      else Var_e (i - 1)
    | App_e e1 e2 => App_e (subst v k e1) (subst v k e2)
    | Lam_e e' => Lam_e (subst v (1 + k) e')
    | Con_e d es => Con_e d (substs' subst v k es)
    | Let_e e1 e2 => Let_e (subst v k e1) (subst v (1 + k) e2)
    | Match_e e bs => Match_e (subst v k e) (subst_branches' subst v k bs)
    | Fix_e es i => Fix_e (substs' subst v (2 + k) es) i
  end.
Definition substs := substs' subst.
Definition subst_branch := subst_branch' subst.
Definition subst_branches := subst_branches' subst.

Class Substitute (v:Type) (t:Type) := { substitute : v -> N -> t -> t }.

(** Notation for substitution. *)
Notation "M { j := N }" := (substitute N j M) (at level 10, right associativity).

Instance ExpSubstitute : Substitute exp exp :=
  { substitute := subst}.
Instance ExpsSubstitute : Substitute exp (list exp) :=
  { substitute := substs}.
Instance BranchSubstitute : Substitute exp (dcon * N * exp) :=
  { substitute := subst_branch}.
Instance BranchesSubstitute : Substitute exp (list (dcon * N * exp)) := 
  { substitute := subst_branches}.

(** A tactic for simplifying numeric tests. *)
Ltac if_split := 
  match goal with
    | [ |- context[if ?e then _ else _] ] => destruct e ; simpl ; try lia ; auto ; try subst
  end.

(* These lemmas come from "A Head-to-Head Comparison of deBruijn Indices and Names"
   by Stefan Berghofer and Christian Urban. It's notable that they and others remark
   that coming up with these on your own is quite difficult... 

   I don't actually need these yet, so they are not quite up to date with the rest
   of the development.
*)
(*
Lemma shift_twice:
  forall N i j m n, i <= j -> j <= i + m -> shift n j (shift m i N) = shift (m + n) i N.
Proof.
  assert ((forall N i j m n, i <= j -> j <= i + m -> shift n j (shift m i N) = shift (m + n) i N) /\
          (forall Ns i j m n, i <= j -> j <= i + m -> shifts n j (shifts m i Ns) = shifts (m + n) i Ns)).
  apply my_exp_ind ; intros ; simpl ; auto ;
  try (rewrite H ; auto ; try lia ; rewrite H0 ; auto ; try lia ; auto).
  repeat if_split. apply f_equal. lia.
  tauto.
Qed.

Lemma shift_subst :
  forall N i k j L, k <= j -> shift i k (N{j := L}) = (shift i k N){j+i := L}.
Proof.
  assert ((forall N i k j L, k <= j -> shift i k (N{j := L}) = (shift i k N){j+i := L}) /\
          (forall Ns i k j L, k <= j -> shifts i k (Ns{j := L}) = (shifts i k Ns){j+i := L})).
  apply my_exp_ind ; intros ; simpl ; auto ;
  try (rewrite H ; auto ; rewrite H0 ; auto).
  repeat if_split. destruct (lt_dec j k) ; try lia. rewrite shift_twice ; auto ; lia.
  destruct (lt_dec n k) ; try lia ; auto. apply f_equal. lia.
  apply f_equal. rewrite H ; try lia. simpl.
  replace (1 + j + i) with (1 + (j + i)) ; auto ; lia. 
  tauto.
Qed.

Lemma shift_away_subst :
  forall (L:exp) k i j (P:exp), k <= i -> i < k + (j + 1) ->
                    (shift (1 + j) k L){i := P} = shift j k L.
Proof.
  assert ((forall (L:exp) k i j (P:exp), k <= i -> i < k + (j + 1) ->
                                         (shift (1 + j) k L){i := P} = shift j k L) /\
          (forall (Ls:exps) k i j (P:exp), k <= i -> i < k + (j + 1) ->
                                         (shifts (1 + j) k Ls){i := P} = shifts j k Ls)).
  apply my_exp_ind ; simpl ; intros ; auto ;
  try (rewrite H ; auto ; try lia ; rewrite H0 ; auto).
  repeat if_split. replace (n + (1 + j) - 1) with (n + j) ; auto ; lia.
  tauto.
Qed.

(** According to Berghofer and Urban, this is a critical property of substitution,
    though we don't use it here. *)
Lemma substitution :
  forall (M N L:exp) i j, i <= j ->
    M{i := N}{j := L} = M{1+j := L}{i := N{ j-i := L}}.
Proof.
  assert ((forall (M:exp) N L i j, i <= j -> M{i := N}{j := L} = M{1+j := L}{i := N{ j-i := L}}) /\
          (forall (Ms:exps) N L i j, i <= j -> Ms{i := N}{j := L} = Ms{1+j := L}{i := N{ j-i := L}})).
  apply my_exp_ind ; intros ; simpl in * ; auto ;
  try (rewrite H ; auto ; rewrite H0 ; auto).
  repeat if_split.
  assert (0 <= j - i). lia.
  generalize (shift_subst N i 0 (j - i) L H0). intros.
  unfold substitute in H1. simpl in H1.
  rewrite H1. replace (j - i + i) with j ; auto. lia.
  destruct (eq_dec n 0). lia.
  generalize  (shift_away_subst L 0 i (n - 1)). intro.
  unfold substitute in H0. simpl in H0.
  specialize (H0 (subst L (n - 1 - i) N)). rewrite H0 ; auto. lia. lia.
  apply f_equal.
  rewrite H. replace (1 + j - (1 + i)) with (j - i). auto. lia. lia.
  tauto.
Qed.
*)

(** Some properties that I use below to show evaluation preserves well-formedness. *)

(** Shifting an [i] expression by [k] when above [i] has no effect. *)
Lemma shift_closed' :
  (forall i e, exp_wf i e -> forall k, shift k i e = e) /\
  (forall i es, exps_wf i es -> forall k, shifts k i es = es) /\
  (forall i bs, branches_wf i bs -> forall k, shift_branches k i bs = bs).
Proof.
  apply my_exp_wf_ind ; simpl ; intros ; auto ; 
  fold shifts in * ; fold shift_branches in * ; try congruence. if_split.
Qed.

(** Corrollary:  shifting a closed expression has no effect. *)
Lemma shift_closed_exp : forall k i e, exp_wf i e -> shift k i e = e.
  intros. apply (proj1 shift_closed') ; auto.
Qed.
Lemma shift_closed_exps : forall k i es, exps_wf i es -> shifts k i es = es.
  intros. apply (proj1 (proj2 shift_closed')) ; auto.
Qed.
Lemma shift_closed_branches : forall k i bs, branches_wf i bs -> shift_branches k i bs = bs.
  intros. apply (proj2 (proj2 shift_closed')) ; auto.
Qed.
Hint Rewrite shift_closed_exp shift_closed_exps shift_closed_branches.

Fixpoint subst_list (e:exp) (vs:list exp) : exp :=
  match vs with
    | nil => e
    | v::vs => subst_list (e{0:=v}) vs
  end.

(** Find a branch in a match expression corresponding to a given constructor
    and arity. *)
Fixpoint find_branch{A} (d:dcon) (m:N) (bs:list (branch A)) : option A :=
  match bs with
    | nil => None
    | b::bs => br (fun d' n e =>
                     if eq_dec d d' then if eq_dec n m then Some e else None
                     else find_branch d m bs) b
  end.

(** Find the nth component in a list -- should replace with a library function. *)
Fixpoint nthopt{A} (n:nat) (xs:list A) : option A :=
  match n, xs with 
    | 0%nat, h::_ => Some h
    | S n, _::t => nthopt n t
    | _, _ => None
  end.

(** Big-step evaluation for [exp]. *)
Inductive eval : exp -> exp -> Prop :=
| eval_Lam_e : forall e, eval (Lam_e e) (Lam_e e)
| eval_App_e : forall e1 e1' e2 v2 v,
                 eval e1 (Lam_e e1') ->
                 eval e2 v2 ->
                 eval (e1'{0 := v2}) v -> 
                 eval (App_e e1 e2) v
| eval_Con_e : forall d es vs, evals es vs -> eval (Con_e d es) (Con_e d vs)
| eval_Let_e : forall e1 v1 e2 v2,
                 eval e1 v1 ->
                 eval (e2{0:=v1}) v2 ->
                 eval (Let_e e1 e2) v2
| eval_Match_e : forall e bs d vs e' v,
                   eval e (Con_e d vs) ->
                   find_branch d (N.of_nat (List.length vs)) bs = Some e' ->
                   eval (subst_list e' vs) v ->
                   eval (Match_e e bs) v
| eval_Fix_e : forall es i, eval (Fix_e es i) (Fix_e es i)
| eval_Proj_e : forall e es n e' e2 v2,
                  eval e (Fix_e es n) ->
                  nthopt (N.to_nat n) es = Some e' ->
                  eval (App_e e e2) (e'{0 := Fix_e es})
with evals : list exp -> list exp -> Prop :=
     | evals_nil : evals nil nil
     | evals_cons : forall e es v vs, eval e v -> evals es vs ->
                                        evals (e::es) (v::vs).

Scheme eval_ind2 := Induction for eval Sort Prop
with evals_ind2 := Induction for evals Sort Prop.
Combined Scheme my_eval_ind from eval_ind2, evals_ind2.

(** If [e] is an [i+1] expression, and [v] is a closed expression, then 
    for any [k <= i], substituting [v] for [k] in e yields an [i] expression.

    I wish I could generalize this to non-closed expressions, but haven't
    been able to.  But perhaps the whole point is that I need to shift [v]
    or something.
 *)
Lemma subst_preserves_wf' :
  (forall i' e, exp_wf i' e ->
                forall i, i' = 1 + i -> forall v, exp_wf 0 v ->
                                                  forall k, k <= i -> exp_wf i (e{k:=v})) /\
  (forall i' es, exps_wf i' es ->
                 forall i, i' = 1 + i -> forall v, exp_wf 0 v ->
                                                   forall k, k <= i -> exps_wf i (es{k:=v})) /\
  (forall i' bs, branches_wf i' bs ->
                 forall i, i' = 1 + i -> forall v, exp_wf 0 v ->
                                                   forall k, k <= i -> branches_wf i (bs{k:=v})).
Proof.
  apply my_exp_wf_ind ; simpl ; intros ; subst ; eauto.
  repeat if_split ; try (constructor ; auto ; lia).
  rewrite shift_closed_exp ; auto.
  constructor. apply H ; try lia ; auto.
  constructor ; auto. apply H0 ; try lia ; auto.
  constructor ; auto. apply H ; try lia ; auto.
  constructor ; auto. apply H ; try lia ; auto.
Qed.

(** Corrollary:  if [e] is an [i+1] expression, and [v] is closed, then 
   substituting [v] for [0] in [e] yields an [i] expression. *)
Lemma subst_preserves_exp_wf :
  forall i e, exp_wf (1 + i) e -> forall v, exp_wf 0 v -> exp_wf i (e {0 := v}).
Proof.
  intros ; eapply (proj1 subst_preserves_wf') ; eauto ; lia.
Qed.

Lemma subst_list_preserves_exp_wf :
  forall vs, exps_wf 0 vs -> forall i e, exp_wf (N.of_nat (List.length vs) + i) e ->
                                         exp_wf i (subst_list e vs).
Proof.
  induction vs ; simpl ; intros ; subst ; auto. inversion H ; clear H ; subst.
  replace (N.pos (Pos.of_succ_nat (Datatypes.length vs)) + i) with
  (1 + (N.of_nat (Datatypes.length vs) + i)) in H0 ; [idtac | lia].
  apply IHvs ; auto. apply subst_preserves_exp_wf ; auto.
Qed.
  
Lemma subst_preserves_exps_wf :
  forall i es, exps_wf (1 + i) es -> forall v, exp_wf 0 v -> exps_wf i (es {0 := v}).
Proof.
  intros ; eapply (proj1 (proj2 subst_preserves_wf')) ; eauto ; lia.
Qed.

Lemma subst_preserves_branches_wf :
  forall i bs, branches_wf (1 + i) bs -> forall v, exp_wf 0 v -> branches_wf i (bs {0 := v}).
Proof.
  intros ; eapply (proj2 (proj2 subst_preserves_wf')) ; eauto ; lia.
Qed.

Hint Resolve subst_preserves_exp_wf subst_preserves_exps_wf subst_preserves_branches_wf.

Lemma nthopt_preserves_wf :
  forall i es, exps_wf i es -> forall n e, nthopt n es = Some e -> exp_wf i e.
Proof.
  induction es ; simpl ; intros. destruct n ; discriminate.
  inversion H ; subst. destruct n ; simpl in *. injection H0 ; intros ; subst ; auto.
  apply (IHes H5 n e) ; auto.
Qed.
  
Lemma find_branch_preserves_wf :
  forall i bs, branches_wf i bs -> forall d m e, find_branch d m bs = Some e -> exp_wf (m+i) e.
Proof.
  induction 1 ; simpl ; intros a b c ; repeat if_split ; intro H1 ; try discriminate.
  injection H1 ; intros ; subst ; auto. eapply IHbranches_wf ; eauto.
Qed.
Hint Resolve find_branch_preserves_wf.

(** Evaluation preserves closed expressions.  I wish I could generalize this
   to evaluation preserves [i] expressions. *)
Lemma eval_preserves_wf :
  (forall e v, eval e v -> exp_wf 0 e -> exp_wf 0 v) /\
  (forall es vs, evals es vs -> exps_wf 0 es -> exps_wf 0 vs).
Proof.
  apply my_eval_ind ; simpl ; intros ; auto. inversion H2 ; clear H2 ; subst.
  specialize (H H6) ; clear H6. specialize (H0 H7) ; clear H7.
  inversion H ; clear H ; subst. apply H1 ; auto. 
  inversion H0 ; auto. inversion H1 ; auto.
  inversion H1 ; clear H1 ; subst. apply H0 ; auto.
  apply subst_list_preserves_exp_wf. specialize (H H5). inversion H ; subst.
  auto. eapply find_branch_preserves_wf ; eauto.
  inversion H0 ; subst.
  specialize (H H3). inversion H ; subst.
  apply (fun H' => subst_preserves_exp_wf 0 (Lam_e e') H' (Fix_e es) H).
  constructor. apply (nthopt_preserves_wf _ _ H4 _ _ e1). 
  inversion H1 ; subst. constructor ; auto.
Qed.

(** Characterize values *)
Inductive is_value : exp -> Prop :=
| var_is_value : forall i, is_value (Var_e i)
| lam_is_value : forall e, is_value (Lam_e e)
| con_is_value : forall d es, are_values es -> is_value (Con_e d es)
| fix_is_value : forall es, is_value (Fix_e es)
with are_values : list exp -> Prop :=
| nil_are_values : are_values nil
| cons_are_values : forall e es, is_value e -> are_values es ->
                                 are_values (e::es).
Scheme is_value_ind2 := Induction for is_value Sort Prop
with are_values_ind2 := Induction for are_values Sort Prop.
Combined Scheme my_is_value_ind from is_value_ind2, are_values_ind2.
Hint Constructors is_value are_values.

(** Show that evaluation always yields a value. *)
Lemma eval_yields_value' :
  (forall e v, eval e v -> is_value v) /\
  (forall es vs, evals es vs -> are_values vs).
Proof.
  apply my_eval_ind ; simpl ; intros ; auto ; try constructor ; auto.
Qed.

Lemma eval_yields_value e v : eval e v -> is_value v.
  apply (proj1 eval_yields_value' e v).
Qed.
Hint Resolve eval_yields_value.

Lemma evals_yields_values es vs : evals es vs -> are_values vs.
  apply (proj2 eval_yields_value' es vs).
Qed.
Hint Resolve evals_yields_values.

(**********************)
(** * CPS expressions *)
(**********************)

(** We distinguish values from computations in the syntax.  In addition, we have
    two separate deBruijn name spaces -- one for user-level variables that come
    from the source expression (and remain the same after being translated) and 
    one for continuation variables which are introduced as part of the CPS translation. 

    So for instance, [Var_c] refers to a user-level variable, whereas [KVar_c]
    refers to a continuation variable.  The construct [Cont_c] is a one-argument
    lambda that abstracts a [KVar_c].  The construct [Lam_c] is a two-argument
    lambda that abstracts a [KVar_c] and a [Var_c].  So for instance, the 
    expression:  [Lam_c (Ret_c (KVar_c 0) (Var_c 0))] is closed and corresponds
    to [fun k x => k x].  
*)
Inductive cps : Type :=
| Halt_c : val_c -> cps
| Ret_c : val_c (* cont *) -> val_c (* result *) -> cps
| Call_c : val_c (* fn *) -> val_c (* cont *) -> val_c (* arg *) -> cps
| Match_c : val_c -> list (branch cps) -> cps
| Proj_c : val_c -> N -> val_c -> cps
with val_c : Type :=
| Var_c : N -> val_c
| KVar_c : N -> val_c
| Lam_c : cps (* abstract cont first, then arg *) -> val_c
| Cont_c : cps (* abstracts arg *) -> val_c
| Con_c : dcon -> list val_c -> val_c
  (* each of the Fix expressions abstracts (a) a user-level variable corresponding 
     to the fixpoint record, (b) a user-level variable corresponding to the function
     argument, and (c) a continuation variable. *)                                  
| Fix_c : list cps -> val_c.

(* Induction scheme for CPS terms.  Horribly complicated! *)
Section CPS_SCHEME.
  Variable Pcps : cps -> Prop.
  Variable Pval : val_c -> Prop.
  Variable Pbranches : list (branch cps) -> Prop.
  Variable Pvals : list val_c -> Prop.
  Variable Pfn_list : list cps -> Prop.

  Variable halt_c : forall {v}, Pval v -> Pcps (Halt_c v).
  Variable ret_c : forall {v1 v2}, Pval v1 -> Pval v2 -> Pcps (Ret_c v1 v2).
  Variable call_c : forall {v1 v2 v3}, Pval v1 -> Pval v2 -> Pval v3 -> Pcps (Call_c v1 v2 v3).
  Variable match_c : forall {v bs}, Pval v -> Pbranches bs -> Pcps (Match_c v bs).
  Variable proj_c : forall {v1 v2} n, Pval v1 -> Pval v2 -> Pcps (Proj_c v1 n v2).
  Variable var_c : forall n, Pval (Var_c n).
  Variable kvar_c : forall n, Pval (KVar_c n).
  Variable lam_c : forall {c}, Pcps c -> Pval (Lam_c c).
  Variable cont_c : forall {c}, Pcps c -> Pval (Cont_c c).
  Variable con_c : forall d {vs}, Pvals vs -> Pval (Con_c d vs).
  Variable fix_c : forall cs, Pfn_list cs -> Pval (Fix_c cs).
  Variable nil_vs : Pvals nil.
  Variable cons_vs : forall {v vs}, Pval v -> Pvals vs -> Pvals (v::vs).
  Variable nil_b : Pbranches nil.
  Variable cons_b : forall d n {c bs}, Pcps c -> Pbranches bs -> Pbranches ((d,n,c)::bs).
  Variable nil_fn : Pfn_list nil.
  Variable cons_fn : forall {c cs}, Pcps c -> Pfn_list cs -> Pfn_list (c::cs).

  Section MY_CPS_IND.
    Variable my_cps_ind : forall c, Pcps c.
    Fixpoint my_cps_branches_ind' (bs: list (branch cps)) : Pbranches bs :=
      match bs return Pbranches bs with
        | nil => nil_b
        | (d,n,c)::bs' => cons_b d n _ _ (my_cps_ind c) (my_cps_branches_ind' bs')
      end.
    Variable my_val_ind : forall v, Pval v.
    Fixpoint my_vals_ind' (vs:list val_c) : Pvals vs :=
      match vs return Pvals vs with
        | nil => nil_vs
        | v::vs' => cons_vs _ _ (my_val_ind v) (my_vals_ind' vs')
      end.
    Fixpoint my_fn_list_ind' (cs: list cps) : Pfn_list cs :=
      match cs return Pfn_list cs with
        | nil => nil_fn
        | c::cs' => cons_fn _ _ (my_cps_ind c) (my_fn_list_ind' cs')
      end.
  End MY_CPS_IND.
  
  Fixpoint my_cps_ind'(c:cps) : Pcps c :=
    match c return Pcps c with
      | Halt_c v => halt_c _ (my_val_ind' v)
      | Ret_c v1 v2 => ret_c _ _ (my_val_ind' v1) (my_val_ind' v2)
      | Call_c v1 v2 v3 => call_c _ _ _ (my_val_ind' v1) (my_val_ind' v2) (my_val_ind' v3)
      | Match_c v bs =>
        match_c _ _ (my_val_ind' v) (my_cps_branches_ind' my_cps_ind' bs)
      | Proj_c v1 i v2 => proj_c _ _ i (my_val_ind' v1) (my_val_ind' v2)
    end
  with my_val_ind'(v:val_c) : Pval v := 
    match v return Pval v with 
      | Var_c n => var_c n
      | KVar_c n => kvar_c n
      | Lam_c c => lam_c _ (my_cps_ind' c)
      | Cont_c c => cont_c _ (my_cps_ind' c)
      | Con_c d vs => con_c d _ (my_vals_ind' my_val_ind' vs)
      | Fix_c cs => fix_c _ (my_fn_list_ind' my_cps_ind' cs)
    end.
  Definition my_cps_branches_ind := my_cps_branches_ind' my_cps_ind'.
  Definition my_vals_ind := my_vals_ind' my_val_ind'.
  Definition my_fn_list_ind := my_fn_list_ind' my_cps_ind'.

  Lemma my_cps_ind :
    (forall c, Pcps c) /\ (forall v, Pval v) /\ (forall vs, Pvals vs)
    /\ (forall bs, Pbranches bs) /\ (forall cs, Pfn_list cs).
  Proof.
    split. apply my_cps_ind'. split. apply my_val_ind'.
    split. apply my_vals_ind. split. apply my_cps_branches_ind. apply my_fn_list_ind.
  Qed.
End CPS_SCHEME.

(** [cps_wf i j c] (resp. [val_wf i j v]) holds when [c] (resp. [v]) has no 
    user variable greater than or equal to [i], and no continuation variable 
    greater than or equal to [j]. *)
Inductive cps_wf : N (* user *) -> N -> (* cont *) cps -> Prop :=
| halt_wf : forall i j v, val_wf i j v -> cps_wf i j (Halt_c v)
| ret_wf : forall i j v1 v2, val_wf i j v1 -> val_wf i j v2 -> cps_wf i j (Ret_c v1 v2)
| call_wf : forall i j v1 v2 v3,
              val_wf i j v1 -> val_wf i j v2 -> val_wf i j v3 -> cps_wf i j (Call_c v1 v2 v3)
| match_wf : forall i j v bs, val_wf i j v -> cpsbranches_wf i j bs -> cps_wf i j (Match_c v bs)
| proj_wf : forall i j v1 n v2, val_wf i j v1 -> val_wf i j v2 -> cps_wf i j (Proj_c v1 n v2)
with val_wf : N -> N -> val_c -> Prop :=
| var_wf : forall i j k, k < i -> val_wf i j (Var_c k)
| kvar_wf : forall i j k, k < j -> val_wf i j (KVar_c k)
| lam_wf : forall i j c, cps_wf (1 + i) (1 + j) c -> val_wf i j (Lam_c c)
| cont_wf : forall i j c, cps_wf i (1 + j) c -> val_wf i j (Cont_c c)
| con_wf : forall i j d vs, vals_wf i j vs -> val_wf i j (Con_c d vs)
| fix_wf : forall i j cs, fn_list_wf i j cs -> val_wf i j (Fix_c cs)
with vals_wf : N -> N -> list val_c -> Prop :=
| nil_c_wf : forall i j, vals_wf i j nil
| cons_c_wf : forall i j v vs, val_wf i j v -> vals_wf i j vs -> vals_wf i j (v::vs)
with cpsbranches_wf : N -> N -> list (branch cps) -> Prop :=
| nil_b_wf : forall i j, cpsbranches_wf i j nil
| cons_b_wf : forall i j d n c bs, cps_wf (n+i) j c ->
                                   cpsbranches_wf i j bs -> cpsbranches_wf i j ((d,n,c)::bs)
with fn_list_wf : N -> N -> list cps -> Prop :=
| nil_fn_wf : forall i j, fn_list_wf i j nil
| cons_fn_wf : forall i j c cs, cps_wf (2 + i) (1 + j) c ->
                                 fn_list_wf i j cs -> fn_list_wf i j (c::cs).
Hint Constructors cps_wf val_wf vals_wf cpsbranches_wf fn_list_wf.

Scheme cps_wf_ind2 := Induction for cps_wf Sort Prop
with val_wf_ind2 := Induction for val_wf Sort Prop
with vals_wf_ind2 := Induction for vals_wf Sort Prop
with cpsbranches_wf_ind2 := Induction for cpsbranches_wf Sort Prop
with fn_list_ind2 := Induction for fn_list_wf Sort Prop.                                                           
Combined Scheme my_wf_ind from cps_wf_ind2, val_wf_ind2, vals_wf_ind2, cpsbranches_wf_ind2, fn_list_ind2.

(** Weakening holds on well-formedness of CPS terms. *)
Lemma cps_weaken' :
  (forall i j e, cps_wf i j e -> forall k l, cps_wf (k + i) (l + j) e) /\
  (forall i j v, val_wf i j v -> forall k l, val_wf (k + i) (l + j) v) /\
  (forall i j vs, vals_wf i j vs -> forall k l, vals_wf (k + i) (l + j) vs) /\ 
  (forall i j bs, cpsbranches_wf i j bs -> forall k l, cpsbranches_wf (k + i) (l + j) bs) /\
  (forall i j cs, fn_list_wf i j cs -> forall k l, fn_list_wf (k + i) (l + j) cs).
Proof.
  apply my_wf_ind ; simpl ; intros ; eauto ; constructor ; try lia ; auto.
  specialize (H k l).
  replace (1 + (k + i)) with (k + (1 + i)) ; [auto | lia].  
  replace (1 + (l + j)) with (l + (1 + j)) ; [auto | lia].
  specialize (H k l). replace (1 + (l + j)) with (l + (1 + j)) ; [auto|lia].
  specialize (H k l).
  replace (n + (k + i)) with (k + (n + i)) ; [auto | lia].
  specialize (H k l).
  replace (2 + (k + i)) with (k + (2 + i)) ; [auto|lia].
  replace (1 + (l + j)) with (l + (1 + j)) ; [auto|lia].
Qed.

Definition cps_weaken := proj1 cps_weaken'.
Definition val_weaken := proj1 (proj2 cps_weaken').
Definition vals_weaken := proj1 (proj2 (proj2 cps_weaken')).
Definition cpsbranches_weaken := proj1 (proj2 (proj2 (proj2 cps_weaken'))).
Definition fn_list_weaken := proj2 (proj2 (proj2 (proj2 cps_weaken'))).

Lemma cps_closed_weaken : forall i j c, cps_wf 0 0 c -> cps_wf i j c.
  intros. generalize (cps_weaken _ _ _ H i j) ; repeat rewrite N.add_0_r ; auto.
Qed.
Lemma val_closed_weaken : forall i j v, val_wf 0 0 v -> val_wf i j v.
  intros. generalize (val_weaken _ _ _ H i j) ; repeat rewrite N.add_0_r ; auto.
Qed.
Lemma vals_closed_weaken : forall i j vs, vals_wf 0 0 vs -> vals_wf i j vs.
  intros. generalize (vals_weaken _ _ _ H i j) ; repeat rewrite N.add_0_r ; auto.
Qed.
Lemma cpsbranches_closed_weaken : forall i j bs, cpsbranches_wf 0 0 bs -> cpsbranches_wf i j bs.
  intros. generalize (cpsbranches_weaken _ _ _ H i j) ; repeat rewrite N.add_0_r ; auto.
Qed.
Lemma fn_list_closed_weaken : forall i j cs, fn_list_wf 0 0 cs -> fn_list_wf i j cs.
  intros. generalize (fn_list_weaken _ _ _ H i j). repeat rewrite N.add_0_r ; auto.
Qed.
Hint Resolve cps_closed_weaken val_closed_weaken vals_closed_weaken cpsbranches_closed_weaken fn_list_closed_weaken.

(** Shifting for user-level variables, analogous to shifting for source
   expressions. Notice this has no effect on [KVar_c] and that the lower
   bound does not change when going under a [Cont_c]. *)
Section USHIFT.
  Variable ushift_val : N -> N -> val_c -> val_c.
  Definition ushift_vals' n k (vs:list val_c) : list val_c := List.map (ushift_val n k) vs.
  Variable ushift_cps : N -> N -> cps -> cps.
  Definition ushift_branch n k (b:branch cps) : branch cps :=
    br (fun d m c => (d,m,ushift_cps n (m+k) c)) b.
  Definition ushift_branches' (n k:N) (bs:list (branch cps)) : list (branch cps) :=
    List.map (ushift_branch n k) bs.
  Definition ushift_fn_list' n k (cs:list cps) : list cps :=
    List.map (ushift_cps n (2 + k)) cs.
End USHIFT.

Fixpoint ushift_cps (n:N) (k:N) (e:cps) : cps :=
  match e with
    | Halt_c v => Halt_c (ushift_val n k v)
    | Ret_c v1 v2 => Ret_c (ushift_val n k v1) (ushift_val n k v2)
    | Call_c v1 v2 v3 => Call_c (ushift_val n k v1) (ushift_val n k v2) (ushift_val n k v3)
    | Match_c v bs => Match_c (ushift_val n k v) (ushift_branches' ushift_cps n k bs)
    | Proj_c v1 i v2 => Proj_c (ushift_val n k v1) i (ushift_val n k v2)
  end
with ushift_val (n:N) (k:N) (v:val_c) : val_c :=
  match v with
    | Var_c i => Var_c (if lt_dec i k then i else i+n)
    | KVar_c i => KVar_c i
    | Lam_c e' => Lam_c (ushift_cps n (1 + k) e')
    | Cont_c e' => Cont_c (ushift_cps n k e')
    | Con_c d vs => Con_c d (ushift_vals' ushift_val n k vs)
    | Fix_c cs => Fix_c (ushift_fn_list' ushift_cps n k cs)
  end.
Definition ushift_vals := ushift_vals' ushift_val.
Definition ushift_branches := ushift_branches' ushift_cps.
Definition ushift_fn_list := ushift_fn_list' ushift_cps.

(** Shifting for continuation variables.  Notice this has no effect
    on [Var_c] and that the lower bound is adjusted for both [Lam_c]
    and [Cont_c] since each bind a continuation variable. *)
Section KSHIFT.
  Variable kshift_val : N -> N -> val_c -> val_c.
  Definition kshift_vals' n k (vs:list val_c) : list val_c := List.map (kshift_val n k) vs.
  Variable kshift_cps : N -> N -> cps -> cps.
  Definition kshift_branch n k (b:branch cps) : branch cps :=
    br (fun d m c => (d,m,kshift_cps n k c)) b.
  Definition kshift_branches' (n k:N) (bs:list (branch cps)) : list (branch cps) :=
    List.map (kshift_branch n k) bs.
  Definition kshift_fn_list' n k (cs:list cps) : list cps :=
    List.map (kshift_cps n (1 + k)) cs.
End KSHIFT.

Fixpoint kshift_cps (n:N) (k:N) (e:cps) : cps :=
  match e with
    | Halt_c v => Halt_c (kshift_val n k v)
    | Ret_c v1 v2 => Ret_c (kshift_val n k v1) (kshift_val n k v2)
    | Call_c v1 v2 v3 => Call_c (kshift_val n k v1) (kshift_val n k v2) (kshift_val n k v3)
    | Match_c v bs => Match_c (kshift_val n k v) (kshift_branches' kshift_cps n k bs)
    | Proj_c v1 i v2 => Proj_c (kshift_val n k v1) i (kshift_val n k v2)
  end
with kshift_val (n:N) (k:N) (v:val_c) : val_c :=
  match v with
    | Var_c i => Var_c i
    | KVar_c i => KVar_c (if lt_dec i k then i else i+n)
    | Lam_c e' => Lam_c (kshift_cps n (1 + k) e')
    | Cont_c e' => Cont_c (kshift_cps n (1 + k) e')
    | Con_c d vs => Con_c d (kshift_vals' kshift_val n k vs)
    | Fix_c cs => Fix_c (kshift_fn_list' kshift_cps n k cs)
  end.
Definition kshift_vals := kshift_vals' kshift_val.
Definition kshift_branches := kshift_branches' kshift_cps.
Definition kshift_fn_list := kshift_fn_list' kshift_cps.

(** Substitution of a value for a user-level variable.  Notice this has
    has no effect on [KVar_c] and that the index does not change going
    under a [Cont_c]. *)
Section USUBST.
  Variable usubst_val : val_c -> N -> val_c -> val_c.
  Definition usubst_vals' v k vs := List.map (usubst_val v k) vs.
  Variable usubst_cps : val_c -> N -> cps -> cps.
  Definition usubst_branch v k b := br (fun d n c => (d,n,usubst_cps v (n + k) c)) b.
  Definition usubst_branches' v k bs := List.map (usubst_branch v k) bs.
  Definition usubst_fn_list' v k cs := List.map (usubst_cps v (2 + k)) cs.
End USUBST.
  
Fixpoint usubst_cps (v:val_c) (k:N) (e:cps) : cps :=
  match e with
    | Halt_c v' => Halt_c (usubst_val v k v')
    | Ret_c v1 v2 => Ret_c (usubst_val v k v1) (usubst_val v k v2)
    | Call_c v1 v2 v3 => Call_c (usubst_val v k v1) (usubst_val v k v2) (usubst_val v k v3)
    | Match_c v' bs => Match_c (usubst_val v k v') (usubst_branches' usubst_cps v k bs)
    | Proj_c v1 i v2 => Proj_c (usubst_val v k v1) i (usubst_val v k v2)
  end
with usubst_val (v:val_c) (k:N) (v':val_c) : val_c :=
  match v' with
    | Var_c i => if lt_dec i k then Var_c i
                 else if eq_dec i k then ushift_val k 0 v
                      else Var_c (i - 1)
    | KVar_c i => KVar_c i
    | Lam_c e => Lam_c (usubst_cps v (1 + k) e)
    | Cont_c e => Cont_c (usubst_cps v k e)
    | Con_c d vs => Con_c d (usubst_vals' usubst_val v k vs)
    | Fix_c cs => Fix_c (usubst_fn_list' usubst_cps v k cs)
  end.
Definition usubst_vals := usubst_vals' usubst_val.
Definition usubst_branches := usubst_branches' usubst_cps.
Definition usubst_fn_list := usubst_fn_list' usubst_cps.

(** Re-use the notation for substitution. *)
Instance UCPSSubstitute : Substitute val_c cps := { substitute := usubst_cps }.
Instance UValSubstitute : Substitute val_c val_c := { substitute := usubst_val }.
Instance UValsSubstitute : Substitute val_c (list val_c) := { substitute := usubst_vals }.
Instance UBranchSubstitute : Substitute val_c (list (branch cps)) := {substitute := usubst_branches}.
Instance UFNListSubstitute : Substitute val_c (list cps) := {substitute := usubst_fn_list}.

Fixpoint usubst_list (c:cps) (vs:list val_c) : cps :=
  match vs with
    | nil => c
    | v::vs => usubst_list (c{0:=v}) vs
  end.
(** Substitution of a value for a continuation variable.  Notice this
    has no effect on [Var_c] and that the index changes when going under
    either a [Cont_c] or a [Lam_c]. *)
Section KSUBST.
  Variable ksubst_val : val_c -> N -> val_c -> val_c.
  Definition ksubst_vals' v k vs := List.map (ksubst_val v k) vs.
  Variable ksubst_cps : val_c -> N -> cps -> cps.
  Definition ksubst_branch v k b := br (fun d n c => (d,n,ksubst_cps v k c)) b.
  Definition ksubst_branches' v k bs := List.map (ksubst_branch v k) bs.
  Definition ksubst_fn_list' v k cs := List.map (ksubst_cps v (1 + k)) cs.
End KSUBST.

Fixpoint ksubst_cps (v:val_c) (k:N) (e:cps) : cps :=
  match e with     
    | Halt_c v' => Halt_c (ksubst_val v k v')
    | Ret_c v1 v2 => Ret_c (ksubst_val v k v1) (ksubst_val v k v2)
    | Call_c v1 v2 v3 => Call_c (ksubst_val v k v1) (ksubst_val v k v2) (ksubst_val v k v3)
    | Match_c v' bs => Match_c (ksubst_val v k v') (ksubst_branches' ksubst_cps v k bs)
    | Proj_c v1 i v2 => Proj_c (ksubst_val v k v1) i (ksubst_val v k v2)
  end
with ksubst_val (v:val_c) (k:N) (v':val_c) : val_c :=
  match v' with
    | Var_c i => Var_c i 
    | KVar_c i => if lt_dec i k then KVar_c i
                  else if eq_dec i k then kshift_val k 0 v
                       else KVar_c (i - 1)
    | Lam_c e => Lam_c (ksubst_cps v (1 + k) e)
    | Cont_c e => Cont_c (ksubst_cps v (1 + k) e)
    | Con_c d vs => Con_c d (ksubst_vals' ksubst_val v k vs)
    | Fix_c cs => Fix_c (ksubst_fn_list' ksubst_cps v k cs)
  end.
Definition ksubst_vals := ksubst_vals' ksubst_val.
Definition ksubst_branches := ksubst_branches' ksubst_cps.
Definition ksubst_fn_list := ksubst_fn_list' ksubst_cps.

(** Use square brackets for continuation substitution. *)
Class KSubstitute (v:Type) (t:Type) := { ksubstitute : v -> N -> t -> t }.
Notation "M [ j := N ]" := (ksubstitute N j M) (at level 10, right associativity).

Instance KCPSSubstitute : KSubstitute val_c cps := { ksubstitute := ksubst_cps }.
Instance KValSubstitute : KSubstitute val_c val_c := { ksubstitute := ksubst_val }.
Instance KValsSubstitute : KSubstitute val_c (list val_c) := { ksubstitute := ksubst_vals }.
Instance KBranchesSubstitute : KSubstitute val_c (list (branch cps)) := {ksubstitute := ksubst_branches}.
Instance KFNListSubstitute : KSubstitute val_c (list cps) := {ksubstitute := ksubst_fn_list}.

(** Big-step evaluation for CPS expressions.  Notice that only computations
    are evaluated -- values are inert so to speak. *)
Inductive eval_c : cps -> val_c -> Prop :=
| eval_Halt_c : forall v, eval_c (Halt_c v) v
| eval_Ret_c : forall c v v',
                 eval_c (c [0 := v]) v' -> 
                 eval_c (Ret_c (Cont_c c) v) v'
| eval_Call_c : forall c v1 v2 v',
                  eval_c (c [0:=v1]{0:=v2}) v' -> 
                  eval_c (Call_c (Lam_c c) v1 v2) v'
| eval_Match_c : forall d vs bs c v',
                   find_branch d (N.of_nat (List.length vs)) bs = Some c ->
                   eval_c (usubst_list c vs) v' -> 
                   eval_c (Match_c (Con_c d vs) bs) v'
| eval_Proj_c : forall cs i c k v',
                  nthopt (N.to_nat i) cs = Some c -> 
                  eval_c (Ret_c k ((Lam_c c){0:=Fix_c cs})) v' ->
                  eval_c (Proj_c (Fix_c cs) i k) v'
.

(** Useful for rewriting. *)
Lemma eval_ret :
  forall c v v', eval_c (Ret_c (Cont_c c) v) v' <-> eval_c (c[0 := v]) v'.
Proof.
  intros. split ; intro. inversion H. subst ; auto. constructor ; auto.
Qed.

(** Useful for rewriting. *)
Lemma eval_call :
  forall c v1 v2 v',
    eval_c (Call_c (Lam_c c) v1 v2) v' <-> eval_c (c[0:=v1]{0:=v2}) v'.
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
    (eval_c (Proj_c (Fix_c cs) i k) v' <-> eval_c (Ret_c k ((Lam_c c){0:=Fix_c cs})) v').
Proof.
  intros ; split ; intro. inversion H0 ; subst. rewrite H in H5. injection H5 ; intros ; subst.
  auto. econstructor ; eauto.
Qed.

(** A fuel-based interpreter. *)
Inductive ans :=
  Value : val_c -> ans | RetTypeError : val_c -> ans | CallTypeError : val_c -> ans
  | MatchMissingCaseError : ans | MatchTypeError : val_c -> ans | ProjError 
  | Fuel : cps -> ans.

Fixpoint eval_c_n (n:nat) (c:cps) : ans := 
  match n with
    | 0%nat => Fuel c
    | S n => match c with
               | Halt_c v => Value v
               | Ret_c (Cont_c c) v => eval_c_n n (c[0 := v])
               | Ret_c v _ => RetTypeError v
               | Call_c (Lam_c c) v1 v2 => eval_c_n n (c[0 := v1]{0 := v2})
               | Match_c (Con_c d vs) bs =>
                 match find_branch d (N.of_nat (List.length vs)) bs with
                   | Some c => eval_c_n n (usubst_list c vs)
                   | None => MatchMissingCaseError
                 end
               | Proj_c (Fix_c cs) i k =>
                 match nthopt (N.to_nat i) cs with
                   | None => ProjError
                   | Some c => eval_c_n n (Ret_c k ((Lam_c c){0:=Fix_c cs}))
                 end
               | Match_c v _ => MatchTypeError v
               | Call_c v _ _ => CallTypeError v
               | Proj_c _ _ _ => ProjError
             end
  end.

(** Sanity check that the two evaluation approaches are consistent. *)
Lemma eval_c_iff_eval_c_n :
  forall c v, eval_c c v <-> (exists n, eval_c_n n c = Value v).
Proof.
  Ltac dex := match goal with
                | [ H : exists _, _ |- _ ] => destruct H
              end.
  intros. split. induction 1 ; simpl ; repeat dex. exists 1%nat. auto.
  exists (S x) ; auto. exists (S x) ; auto. exists (S x). simpl.
  rewrite H. auto. exists (S x) ; simpl. rewrite H. auto.
  intro. destruct H as [n H1]. generalize c v H1. clear c v H1.
  induction n ; simpl ; intros. discriminate.
  destruct c. injection H1. intros ; subst. constructor.
  destruct v0 ; try discriminate. constructor. auto.
  destruct v0 ; try discriminate. constructor. auto.
  destruct v0 ; try discriminate.
  remember (find_branch d (N.of_nat (Datatypes.length l0)) l) as e.
  destruct e ; try discriminate. specialize (IHn _ _ H1).
  econstructor ; eauto.
  destruct v0 ; try discriminate.
  remember (nthopt (N.to_nat n0) l) as e ; destruct e ; try discriminate.
  econstructor ; eauto.
Qed.

(** Convert CPS terms to strings so we can hope to read them. *)
(* 
Section PP.
  Require Import String NPeano Div2.
  Local Open Scope string_scope.

  Definition digit_to_string (n:nat) : string :=
    match n with
      | 0 => "0" | 1 => "1" | 2 => "2" | 3 => "3" | 4 => "4"
      | 5 => "5" | 6 => "6" | 7 => "7" | 8 => "8" | _ => "9"
    end%nat.

  
  Program Fixpoint nat_to_string (n:nat) {measure n} : string :=
    (match n <? 10 as x return n <? 10 = x -> string with
      | true => fun _ => digit_to_string n
      | false => fun pf =>
        let m := NPeano.Nat.div n 10 in
        (nat_to_string m) ++ (digit_to_string (n - 10 * m))
     end eq_refl)%nat.
  Next Obligation.
    apply (NPeano.Nat.div_lt n 10%nat).
    destruct n. unfold NPeano.Nat.ltb in *. simpl in *.
    discriminate. auto with arith.
    auto with arith.
  Defined.

  Definition N_to_string (n:N) : string := nat_to_string (N.to_nat n).

  Section PPsub.
    Variable cps2str : cps -> string.
    Variable val2str : val_c -> string.
    Fixpoint vals2str (vs:list val_c) : string :=
      match vs with
        | nil => ""
        | v::nil => val2str v
        | v::vs => (val2str v) ++ "," ++ (vals2str vs)
      end.
    Fixpoint vars2string (n:nat) : string :=
      match n with
        | 0%nat => ""
        | S 0 => "x0"
        | S n => (vars2string n)++",x"++(nat_to_string n)
      end.
    Fixpoint branch2str (b:branch cps) : string :=
      br (fun d n c => "| D"++(N_to_string d)++"("++(vars2string (N.to_nat n))++") => ("++cps2str c++")") b.
    Fixpoint branches2str (bs:list (branch cps)) : string :=
      match bs with
        | nil => ""
        | b::bs => (branch2str b) ++ (branches2str bs)
      end.
    Definition fn2str (c:cps) : string :=
      "(fun k0 x0 => " ++ (cps2str c) ++ ")".
    Fixpoint fns2str (cs:list cps) : string :=
      match cs with
        | nil => ""
        | [c] => fn2str c
        | c::cs => fn2str c ++ " and " ++ fns2str cs
      end.
  End PPsub.

  Fixpoint cps2str (c:cps) :=
    match c with
      | Halt_c v => "halt " ++ (val2str v)
      | Ret_c (Cont_c c) v => "let k0 := " ++ (val2str v) ++ " in " ++ (cps2str c)
      | Ret_c v1 v2 =>
        "ret " ++ (val2str v1) ++ " " ++ (val2str v2)
      | Call_c v1 v2 v3 => "call " ++ (val2str v1) ++ " " ++ (val2str v2) ++
                                   " " ++ (val2str v3)
      | Match_c v bs => "match " ++ (val2str v) ++ " with " ++ (branches2str cps2str bs)
      | Proj_c v1 i v2 =>
        "proj " ++ (val2str v1) ++ "." ++ (N_to_string i) ++ " then " ++ (val2str v2)
    end
  with val2str (v:val_c) :=
         match v with
           | Var_c i => "x"  ++ (N_to_string i)
           | KVar_c i => "k" ++ (N_to_string i)
           | Lam_c c => "(fun k0 x0 => " ++ (cps2str c) ++ ")"
           | Cont_c c => "(cont k0 => " ++ (cps2str c) ++ ")"
           | Con_c d vs => "D" ++ (N_to_string d) ++ "(" ++ (vals2str val2str vs) ++ ")"
           | Fix_c cs => "Fix(" ++ (fns2str cps2str cs) ++ ")"
         end.
  Definition cps_to_string c := (cps2str c).
  Definition val_to_string v := (val2str v).
  Definition vals_to_string vs := (vals2str val2str vs).

  Definition ans_to_string (a:ans) :=
    match a with
      | Value v => val2str v
      | RetTypeError _ => "return type error"
      | CallTypeError _ => "call type error"
      | MatchTypeError _ => "match type error"
      | MatchMissingCaseError => "match missing case error"
      | ProjError => "projection error"
      | Fuel _ => "out of fuel"
    end.
End PP.
*)
(**************************)
(** * The CPS Translation *)
(**************************)

(** Computable test as to whether a source expression is already a
    value (a.k.a., atomic).  *)
Section IS_VALUEB.
  Variable is_valueb : exp -> bool.
  Fixpoint are_valuesb' (es:list exp) : bool :=
    match es with
      | nil => true
      | e::es => if is_valueb e then are_valuesb' es else false
    end.
End IS_VALUEB.

Fixpoint is_valueb (e:exp) : bool :=
  match e with
    | Var_e _ => true
    | Lam_e _ => true
    | App_e _ _  => false
    | Con_e _ es => are_valuesb' is_valueb es
    | Match_e _ _ => false
    | Let_e _ _ => false
    | Fix_e _ => true
    | Proj_e _ _ => false
  end.
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

(** The inner, naive CBV CPS translation.  This introduces a lot of 
    administrative reductions, but simple things first.  Importantly,
    things that are already values are treated a little specially.  
    This ensures a substitution property 
    [cps_cvt(e{x:=v}) = (cps_cvt e){x:=(cps_vt_val v)}].
 *)
Section CPS_CVT.
  Variable cps_cvt : exp -> val_c.

  Definition cps_cvt_fn_list' (es:list exp) : list cps :=
    map (fun e => Ret_c (cps_cvt e) (KVar_c 0)) es.

  Fixpoint cps_cvt_val' (e:exp) : val_c :=
    match e with
      | Var_e n => Var_c n
      | Lam_e e => Lam_c (Ret_c (cps_cvt e) (KVar_c 0))
      | Con_e d es => Con_c d (List.map cps_cvt_val' es)
      | Fix_e es => Fix_c (cps_cvt_fn_list' es)
      | _ => Var_c 5 (* impossible *)
    end.
  Fixpoint cps_cvts' (es:list exp) (c:cps) : cps :=
    match es with
      | nil => c
      | e::es => Ret_c (cps_cvt e) (Cont_c (cps_cvts' es c))
    end.
  
  Definition cps_cvt_branch' : branch exp -> branch cps :=
    br (fun d n c => (d,n,Ret_c (cps_cvt c) (KVar_c 1))).
  
  Definition cps_cvt_branches' (bs:list (branch exp)) : list (branch cps) :=
    map cps_cvt_branch' bs.

End CPS_CVT.

Fixpoint cps_cvt (e:exp) : val_c :=
  if is_valueb e then Cont_c (Ret_c (KVar_c 0) (cps_cvt_val' cps_cvt e)) else
  match e with
    | App_e e1 e2 =>
      (* cont \k.(ret [e1] (cont \v1.(ret [e2] (cont \v2.call v1 k v2)))) *)
      Cont_c (Ret_c (cps_cvt e1)
                    (Cont_c (Ret_c (cps_cvt e2)
                                   (Cont_c (Call_c (KVar_c 1) (KVar_c 2) (KVar_c 0))))))
    | Con_e d es =>
      Cont_c (cps_cvts' cps_cvt es (Ret_c (KVar_c (N.of_nat (List.length es)))
                                          (Con_c d (list_to_indices es))))
    | Match_e e bs =>
      Cont_c (Ret_c (cps_cvt e)
                    (Cont_c (Match_c (KVar_c 0) (cps_cvt_branches' cps_cvt bs))))
    | Let_e e2 e1 =>
      (* translate as if it were App_e (Lam_e e1) e2 *)
      Cont_c(Ret_c (cps_cvt e2)
                   (Cont_c (Call_c (Lam_c (Ret_c (cps_cvt e1) (KVar_c 0)))
                                   (KVar_c 1) (KVar_c 0))))
    | Proj_e e i =>
      Cont_c (Ret_c (cps_cvt e) (Cont_c (Proj_c (KVar_c 0) i (KVar_c 1))))
    | _ => Var_c 6 (* impossible *)
  end.

Definition cps_cvt_val := cps_cvt_val' cps_cvt.
Definition cps_cvts := cps_cvts' cps_cvt.
Definition cps_cvt_vals := List.map cps_cvt_val.
Definition cps_cvt_branch := cps_cvt_branch' cps_cvt.
Definition cps_cvt_branches := cps_cvt_branches' cps_cvt.
Definition cps_cvt_fn_list := cps_cvt_fn_list' cps_cvt.

(** The top-level CPS translation.  We use [cont \x.Halt x] as the initial
    continuation. *)
Definition cps_cvt_prog (e:exp) := Ret_c (cps_cvt e) (Cont_c (Halt_c (KVar_c 0))).

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
  (forall e, is_value e -> cps_cvt e = Cont_c (Ret_c (KVar_c 0) (cps_cvt_val e))) /\
  (forall es, are_values es ->
              forall d es',
                are_values es' -> 
                cps_cvt (Con_e d (es' ++ es)) =
                Cont_c (Ret_c (KVar_c 0) (Con_c d (cps_cvt_vals (es' ++ es))))).
Proof.
  apply my_is_value_ind ; intros ; auto.
  specialize (H d nil). replace ([] ++ es) with es in H ; auto.
  repeat rewrite app_nil_r. simpl. fold are_valuesb.
  rewrite (proj2 (are_valuesb_corr es') H). auto.
  simpl. fold are_valuesb. rewrite (proj2 (are_valuesb_corr (es' ++ (e::es)))) ; auto.
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

(** Shifting by 0 has no effect. *)
Lemma kshift_zero :
  (forall e d, kshift_cps 0 d e = e) /\ (forall v d, kshift_val 0 d v = v)
  /\ (forall vs d, kshift_vals 0 d vs = vs) /\ (forall bs d, kshift_branches 0 d bs = bs) /\
  (forall cs d, kshift_fn_list 0 d cs = cs).
Proof.
  apply my_cps_ind ; simpl ; intros ;
  fold kshift_vals ; fold kshift_branches ; fold kshift_fn_list ; try congruence.
  if_split. rewrite N.add_0_r. auto. rewrite H ; rewrite H0 ; auto.
Qed.

Lemma ushift_zero :
  (forall e d, ushift_cps 0 d e = e) /\ (forall v d, ushift_val 0 d v = v) /\
  (forall vs d, ushift_vals 0 d vs = vs) /\ (forall bs d, ushift_branches 0 d bs = bs) /\
  (forall cs d, ushift_fn_list 0 d cs = cs).
Proof.
  apply my_cps_ind ; simpl ; intros ;
  fold ushift_vals ; fold ushift_branches ; fold ushift_fn_list ; try congruence.
  if_split. rewrite N.add_0_r ; auto. rewrite H ; rewrite H0 ; auto.
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
                (forall j c, cps_wf i (j + (N.of_nat (length es))) c -> cps_wf i j (cps_cvts es c)) /\
                (are_values es -> vals_wf i 0 (cps_cvt_vals es)) /\
                (forall i', i = 2 + i' -> fn_list_wf i' 0 (cps_cvt_fn_list es))
  ) /\
  (forall i bs, branches_wf i bs -> cpsbranches_wf i 2 (cps_cvt_branches bs)).
Proof.
  apply my_exp_wf_ind ; simpl ; intros ; auto.
  repeat constructor ; auto.
  destruct H. repeat constructor.
  apply (val_weaken _ _ _ H 0 2).
  apply (val_weaken _ _ _ H 0 1).
  destruct H. destruct H0.
  split.
  constructor. constructor.
  apply (val_weaken _ _ _ H 0 1).
  constructor. constructor.
  apply (val_weaken _ _ _ H0 0 2).
  repeat constructor.
  intros. inversion H3.
  destruct H. destruct H0. fold are_valuesb.
  generalize (are_valuesb_corr es). intro.
  destruct (are_valuesb es).
  specialize (H0 (proj1 H2 eq_refl)).
  repeat constructor.
  apply (vals_weaken _ _ _ H0 0 1). auto.
  split.
  constructor. apply H. repeat constructor. lia.
  replace (1+0) with 1 ; auto.
  eapply list_to_indices_wf.
  intros. inversion H3 ; subst.
  destruct H2. specialize (H4 H5). discriminate.
  destruct H.
  split. repeat constructor ; auto. apply (val_weaken _ _ _ H 0 1).
  intro. inversion H2.
  destruct H ; destruct H0.
  split. repeat constructor ; auto.
  apply (val_weaken _ _ _ H 0 1).
  apply (val_weaken _ _ _ H0 0 3).
  intro. inversion H3.
  destruct H. destruct H0. split. repeat constructor ; auto.
  specialize (H1 i eq_refl).
  apply (fn_list_weaken _ _ _ H1 0 1). intros.
  constructor. apply H1 ; auto.
  destruct H. split. repeat constructor ; auto.
  apply (val_weaken _ _ _ H 0 1). intro. inversion H1.
  split ; auto. intros.
  rewrite (N.add_0_r) in H. auto.
  destruct H ; destruct H0. destruct H2. split ; intros.
  repeat constructor. generalize (val_weaken _ _ _ H 0 j).
  rewrite (N.add_0_r). auto.
  apply H0. replace (j + N.of_nat (S (length es))) with (1 + j + N.of_nat (length es)) in H4 ; auto.
  lia. split ; intros. inversion H4 ; subst ; auto.
  subst. repeat constructor ; auto.
  apply (val_weaken _ _ _ H 0 1).  
  constructor ; auto. destruct H. constructor.
  apply (val_weaken _ _ _ H 0 2). constructor. lia.
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

(** Eliminate a user substitution when the index we are substituting for is
    out of range. *)
Lemma usubst_closed :
  (forall i j (e:cps), cps_wf i j e -> forall k, k >= i -> forall v, e{k:=v} = e) /\
  (forall i j (w:val_c), val_wf i j w -> forall k, k >= i -> forall v, w{k:=v} = w) /\
  (forall i j (ws:list val_c), vals_wf i j ws -> forall k, k >= i -> forall v, ws{k:=v} = ws) /\
  (forall i j (bs:list (branch cps)), cpsbranches_wf i j bs ->
                                      forall k, k >= i -> forall v,bs{k:=v}=bs) /\
  (forall i j (cs:list cps), fn_list_wf i j cs ->
                             forall k, k >= i -> forall v,cs{k:=v}=cs).
Proof.
 apply my_wf_ind ; intros ; simpl ; auto ; 
  repeat 
  match goal with
    | [ H : forall k, k >= ?j -> _, H1 : ?k >= ?j |- _ ] => rewrite (H _ H1) ; auto
    | _ => idtac
  end.
 fold usubst_branches. rewrite H0 ; auto.
  repeat if_split.
  rewrite (H (1+k)) ; auto ; lia.
  fold usubst_vals ; rewrite H ; auto.
  fold usubst_fn_list. rewrite H ; auto.
  rewrite H ; auto. lia.
  rewrite H ; auto ; lia.
Qed.

(** We can eliminate substitution for a continuation variable in a CPS'd term. *)
Lemma cps_cvt_ksubst :
  forall i e,
    exp_wf i e ->
    forall k v, 
      (cps_cvt e)[k := v] = cps_cvt e.
Proof.
  intros. rewrite (proj1 (proj2 ksubst_closed) _ _ _ (cps_kvar_closed _ _ H)) ; auto.
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

(** Eliminating user shifts on closed values. *)
Lemma ushift_closed_val : forall v, val_wf 0 0 v -> forall k l, ushift_val k l v = v.
Proof.
  intros.
  assert (val_wf l 0 v). generalize (val_weaken _ _ _ H l 0). simpl.
  replace (l + 0) with l ; try lia. auto.
  eapply (proj1 (proj2 ushift_closed')) ; eauto.
Qed.

(** Eliminating continuation shifts on closed values. *)
Lemma kshift_closed_val : forall v, val_wf 0 0 v -> forall k l, kshift_val k l v = v.
Proof.
  intros.
  assert (val_wf 0 l v). generalize (val_weaken _ _ _ H 0 l). simpl.
  replace (l + 0) with l ; auto ; lia.
  eapply (proj1 (proj2 kshift_closed')) ; eauto.
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

(** Substitution preservation specialized to a 0 index on an CPS expression. *)
Lemma usubst_preserves_wf :
  forall i j e, cps_wf (1+i) j e -> forall v, val_wf 0 0 v -> cps_wf i j (e{0:=v}).
Proof.
  intros. eapply (proj1 usubst_preserves_wf') ; eauto. lia.
Qed.

(** Substitution preservation specialized to a 0 index on an CPS expression. *)
Lemma ksubst_preserves_wf :
  forall i j e, cps_wf i (1+j) e -> forall v, val_wf 0 0 v -> cps_wf i j (e[0:=v]).
Proof.
  intros. eapply (proj1 ksubst_preserves_wf') ; eauto. lia.
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
  replace (1 + N.of_nat (length vs)) with (N.of_nat (S (length vs))) ; auto ; lia.
Qed.

Lemma nth_opt_cps_wf :
  forall i j cs, fn_list_wf i j cs -> forall n c, nthopt n cs = Some c -> cps_wf (2+i) (1+j) c.
Proof.
  induction cs ; simpl ; intros. destruct n ; try discriminate.
  inversion H ; subst ; clear H. destruct n ; simpl in *. injection H0 ; intros ; subst ; auto.
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
  apply (proj1 usubst_preserves_wf' 2 1 c H1 1 eq_refl).
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

Lemma is_valueb_subst v e i : is_value v -> is_valueb (subst v i e) = is_valueb e.
  intro H. apply (proj1 (is_valueb_subst' v H) e i).
Qed.

Lemma are_valuesb_subst v es i : is_value v -> are_valuesb (substs v i es) = are_valuesb es.
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
  replace (1 + (1 + N.of_nat (length es))) with (1 + N.of_nat (S (length es))) ; auto ; try lia.
Qed.

(** CPS conversion commutes with substitution for user variables. *)
Lemma cps_cvt_comm_usubst':
  forall v, is_value v -> exp_wf 0 v -> 
            ((forall i e, exp_wf i e ->
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
                              forall j,
                                j < i ->
                                usubst_vals (cps_cvt_val v) j (cps_cvt_vals es) =
                                cps_cvt_vals (substs v j es)) /\
                           (forall j i',
                              i = 2 + i' -> 
                              j < i' -> usubst_fn_list (cps_cvt_val v) j (cps_cvt_fn_list es) =
                                       cps_cvt_fn_list (substs v (2+j) es)))
             /\
             (forall i bs, branches_wf i bs ->
                           forall j,
                             j < i -> 
                             usubst_branches (cps_cvt_val v) j (cps_cvt_branches bs) =
                             cps_cvt_branches (subst_branches v j bs))).
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
  forall v i e j, is_value v -> exp_wf 0 v -> exp_wf i e -> j < i -> is_valueb e = true -> 
                  usubst_val (cps_cvt_val v) j (cps_cvt_val e) = cps_cvt_val (subst v j e).
Proof.
  intros. apply (proj2 (proj1 (cps_cvt_comm_usubst' v H H0) i e H1) j H2 H3).
Qed.

Lemma cps_cvts_comm_subst :
  forall v i es j k c, is_value v -> exp_wf 0 v -> exps_wf i es -> j < i -> cps_wf 0 k c ->
                       usubst_cps (cps_cvt_val v) j (cps_cvts es c) =
                       cps_cvts (substs v j es) (usubst_cps (cps_cvt_val v) j c).
Proof.
  intros. apply (proj1 (proj1 (proj2 (cps_cvt_comm_usubst' v H H0)) i es H1) j k c H2 H3).
Qed.

Lemma cps_cvt_vals_comm_subst :
  forall v i es j, is_value v -> exp_wf 0 v -> exps_wf i es -> are_valuesb es = true -> j < i -> 
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
  erewrite (proj1 (proj2 usubst_closed)) ; eauto ; try lia.
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
  forall d k,
    val_wf 0 0 k -> 
    forall es2 es1,
      exps_wf 0 es2 -> 
      (cps_cvts es2 (Ret_c (KVar_c (N.of_nat (length (es1 ++ es2))))
                           (Con_c d (list_to_indices (es1 ++ es2)))))[N.of_nat(length es1) := k] =
      cps_cvts es2 (Ret_c k (Con_c d (list_to_indices (es1 ++ es2)))).
Proof.
  induction es2 ; simpl ; intros.
  repeat if_split ; try rewrite <- app_nil_end in * ; try lia.
  erewrite kshift_closed_val ; eauto.
  rewrite ksubst_gt_indices ; auto ; lia.
  inversion H0 ; clear H0 ; subst.
  erewrite (proj1 (proj2 ksubst_closed)). Focus 2.
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
  forall v k (vs1 vs2:list val_c), (vs1 ++ vs2)[k:=v] = (vs1[k:=v]) ++ (vs2[k:=v]).
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
  forall i j vs1 vs2, vals_wf i j (vs1 ++ vs2) <-> (vals_wf i j vs1 /\ vals_wf i j vs2).
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
  erewrite (proj1 (proj2 ksubst_closed) 0 0) ; auto ; try lia.
  fold ksubst_vals. rewrite ksubst_vals_append.
  erewrite (proj1 (proj2 (proj2 ksubst_closed))) ; eauto ; try lia.
  simpl. repeat if_split.
  erewrite (proj1 (proj2 kshift_closed') 0 0) ; [idtac | eapply cps_val_kvar_closed ; eauto].
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
  generalize (proj1 eval_preserves_wf _ _ e H7) (proj1 eval_preserves_wf _ _ e0 H8).
  intros. inversion H2. subst.
  generalize (subst_preserves_exp_wf 0 e1' H9 _ H4). intro.
  generalize (proj1 eval_preserves_wf _ _ e3 H5). intro.
  rewrite <- H1 ; auto ; clear H1.
  rewrite eval_ret. simpl.
  rewrite (cps_cvt_ksubst _ _ H7).
  rewrite (cps_cvt_ksubst _ _ H8).
  rewrite ((proj1 (proj2 kshift_closed')) 0 0 k H3).
  rewrite H ; simpl ; clear H. Focus 2. repeat constructor ; eauto.
  rewrite eval_ret. simpl.
  rewrite eval_ret. simpl.
  rewrite (cps_cvt_ksubst (1+0)) ; auto.
  rewrite ((proj1 (proj2 kshift_closed')) 1 1 (cps_cvt e1')) ; auto. Focus 2.
  eapply (val_weaken 1 0 (cps_cvt e1') _ 0 1). 
  rewrite (proj1 (proj2 kshift_closed') 0 1 (cps_cvt e2)) ; auto. 
  rewrite (proj1 (proj2 ksubst_closed) 0 0 (cps_cvt e2)) ; auto ; try lia.
  rewrite H0 ; simpl ; clear H0.
  Focus 2. repeat constructor.
  eapply (val_weaken 1 0 (cps_cvt e1') _ 0 2). simpl.
  generalize (cps_kvar_closed _ _ H9). simpl. intro.
  rewrite (proj1 (proj2 wf_kshift_zero) 0 0 k H3) ; try lia.
  rewrite (proj1 (proj2 ksubst_closed) _ _ _ H3) ; auto ; try lia.
  generalize (eval_yields_value _ _ e0). intro. 
  rewrite (cps_val _ H).
  rewrite eval_ret. simpl.
  repeat rewrite (proj1 (proj2 kshift_zero)).
  generalize (cps_val_kvar_closed 0 _ H4 H). intro.
  rewrite (proj1 (proj2 ksubst_closed) _ _ (cps_cvt_val v2) H0 0) ; auto ; try lia.
  rewrite eval_ret. simpl.
  repeat rewrite (proj1 (proj2 kshift_zero)).
  repeat rewrite (proj1 (proj2 ksubst_closed) _ _ _ H3) ; auto ; try lia.
  rewrite eval_call. simpl.
  rewrite (proj1 (proj2 kshift_zero)).
  generalize (cps_kvar_closed _ _ H9). intro.
  generalize (val_weaken _ _ _ H1 0 1). simpl. intro.
  repeat rewrite (proj1 (proj2 ksubst_closed) _ _ _ H1) ; auto ; try lia.
  rewrite (proj1 (proj2 usubst_closed) _ _ _ H3) ; auto ; try lia.
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
  simpl. rewrite (proj1 (proj2 kshift_zero)).
  generalize (proj1 (proj2 (proj2 ksubst_closed)) 0 0). unfold ksubstitute. simpl.
  intros. rewrite H3 ; try lia.
  Focus 2.
  apply cps_vals_kvar_closed.
  apply (proj2 eval_preserves_wf _ _ e) ; auto.
  eapply evals_yields_values ; eauto.
  rewrite ksubst_cps_cvts ; auto.
  specialize (H H4 d k nil H1 (nil_c_wf 0 0) v'). simpl in H.
  rewrite H.
  assert (are_values vs). apply (proj1 (are_valuesb_corr _)) ; auto.
  assert (exps_wf 0 vs). eapply (proj2 eval_preserves_wf) ; eauto.
  rewrite (eval_cps_cvt_vals' d vs H6 H5 k nil H1) ; auto. simpl ; tauto.
  (* Let case *)
  inversion H1 ; clear H1 ; subst.
  repeat rewrite eval_ret ; simpl.
  rewrite (proj1 (proj2 ksubst_closed) 0 0) ; eauto ; try lia.
  rewrite H ; eauto.
  Focus 2. repeat constructor. rewrite (proj1 (proj2 ksubst_closed) 1 0) ; eauto ; try lia.
  simpl in *. eapply (val_weaken 1 0 (cps_cvt e2) _ 0 2).
  rewrite (proj1 (proj2 kshift_closed') 0 0) ; eauto.
  rewrite (cps_val v1) ; [idtac | eapply eval_yields_value ; eauto].
  rewrite eval_ret. simpl. rewrite (proj1 (proj2 ksubst_closed) 0 0 (cps_cvt_val v1)) ; try lia.
  Focus 2. apply cps_val_kvar_closed ; eauto. eapply eval_preserves_wf ; eauto.
  repeat rewrite (proj1 (proj2 kshift_zero)).
  rewrite (proj1 (proj2 kshift_closed') 0 0) ; eauto.
  rewrite eval_ret. simpl.
  rewrite (proj1 (proj2 ksubst_closed) 1 0 (cps_cvt e2)) ; try lia.
  Focus 2. apply (cps_kvar_closed 1) ; auto.
  rewrite (proj1 (proj2 kshift_zero)).
  rewrite (proj1 (proj2 ksubst_closed) 1 0 (cps_cvt e2)) ; try lia.
  Focus 2. apply (cps_kvar_closed 1) ; auto.
  rewrite (proj1 (proj2 ksubst_closed) 0 0 k) ; eauto ; try lia.
  rewrite eval_call. simpl. rewrite (proj1 (proj2 ksubst_closed) 1 0 (cps_cvt e2)) ; try lia.
  Focus 2. apply (cps_kvar_closed 1) ; auto.
  rewrite (proj1 (proj2 kshift_zero)). rewrite (proj1 (proj2 usubst_closed) 0 0 k) ; auto ; try lia.
  rewrite (cps_cvt_comm_subst v1 1) ; eauto ; try lia.
  Focus 2. eapply eval_preserves_wf ; eauto.
  unfold substitute in H0. simpl in H0. apply H0 ; auto.
  apply subst_preserves_exp_wf ; eauto. eapply eval_preserves_wf ; eauto.
  (* Match case *)
  inversion H1 ; subst.
  assert (is_value (Con_e d vs)). eapply eval_yields_value ; eauto. inversion H3 ; subst.
  assert (exp_wf 0 (Con_e d vs)). eapply eval_preserves_wf ; eauto. inversion H4 ; subst.
  rewrite eval_ret. simpl. rewrite (proj1 (proj2 ksubst_closed) 0 0 (cps_cvt e)) ; eauto ; try lia.
  assert(cpsbranches_wf 0 1 (ksubst_branches' ksubst_cps k 1 (cps_cvt_branches' cps_cvt bs))).
  fold ksubst_branches.
  eapply (proj2 (proj2 (proj2 ksubst_preserves_wf'))) ; eauto ; try lia.
  apply (proj2 (proj2 cps_kvar_closed')) ; auto. 
  rewrite H ; eauto. Focus 2. repeat constructor. eauto.
  rewrite cps_val ; eauto.
  rewrite eval_ret. simpl. fold kshift_branches ksubst_branches ksubst_vals cps_cvt_branches.
  rewrite (proj1 (proj2 (proj2 (proj2 kshift_closed'))) 0) ; eauto.
  rewrite (proj1 (proj2 (proj2 ksubst_closed)) 0 0) ; eauto ; try lia.
  rewrite eval_ret. simpl. fold ksubst_branches kshift_vals cps_cvt_vals.
  rewrite (proj1 (proj2 (proj2 kshift_zero))). fold ksubst_branches in H8.
  generalize (find_branch_cps_cvt _ _ _ _ e1 (Con_c d (cps_cvt_vals vs)) k).
  assert (length vs = length (cps_cvt_vals vs)). unfold cps_cvt_vals. rewrite map_length. auto.
  rewrite H9. intro.
  rewrite eval_match ; eauto.
  simpl.
  generalize (find_branch_preserves_wf _ _ H7 _ _ _ e1). rewrite N.add_0_r. intro.
  assert (val_wf (N.of_nat (length vs)) 0 (cps_cvt e')).
  apply (cps_kvar_closed) ; auto.
  repeat (rewrite (proj1 (proj2 ksubst_closed) (N.of_nat (length vs)) 0 (cps_cvt e')) ; eauto ; try lia).
  rewrite (proj1 (proj2 kshift_closed') 0 0 k) ; eauto.
  rewrite (proj1 (proj2 ksubst_closed) 0 0 k) ; eauto ; try lia.
  rewrite cps_cvt_comm_usub_list ; auto. 
  apply H0 ; auto.
  apply subst_list_preserves_exp_wf ; auto. rewrite N.add_0_r ; auto.
  (* Proj case *)
  inversion H0 ; subst ; clear H0.
  repeat rewrite eval_ret.
  simpl. rewrite (proj1 (proj2 kshift_closed') 0 0 k).
  rewrite (proj1 (proj2 ksubst_closed) 0 0) ; eauto ; try lia. Focus 2. auto.
  rewrite H ; auto. Focus 2. repeat constructor. eapply (val_weaken 0 0 k H1 0 1).
  rewrite (proj1 (proj2 kshift_zero)). simpl.
  rewrite eval_ret. simpl. fold ksubst_fn_list. fold cps_cvt_fn_list.
  assert (exps_wf 2 es).
  generalize (proj1 eval_preserves_wf _ _ e0 H4). intro. inversion H0 ; subst. auto.
  assert (fn_list_wf 0 0 (cps_cvt_fn_list es)).
  apply (cps_fn_list_closed 0 es) ; auto.
  rewrite (proj2 (proj2 (proj2 (proj2 ksubst_closed))) 0 0) ; auto ; try lia.
  rewrite (proj1 (proj2 kshift_closed') 0 1 k) ; [idtac | eapply (val_weaken 0 0 k H1 0 1)].
  rewrite eval_ret. simpl. fold kshift_fn_list.
  rewrite (proj2 (proj2 (proj2 (proj2 kshift_closed'))) _ _ _ H2).
  rewrite (proj1 (proj2 (ksubst_closed)) 0 0 k) ; eauto ; try lia.
  generalize (cps_cvt_list_nth _ _ _ e1) ; intro.
  rewrite eval_proj ; eauto.
  replace (Fix_c (cps_cvt_fn_list es)) with (cps_cvt_val (Fix_e es)) ; auto.
  replace (Lam_c (Ret_c (cps_cvt e') (KVar_c 0))) with (cps_cvt_val (Lam_e e')) ; auto.
  rewrite (cps_cvt_val_comm_subst _ 1) ; auto ; try lia. Focus 2.
  constructor. apply (nthopt_preserves_wf _ _ H0 _ _ e1).
  rewrite (proj1 (proj2 ksubst_closed) 1 1) ; try lia. simpl. tauto.
  rewrite <- (cps_cvt_comm_subst _ 2) ; eauto ; try lia ; simpl.
  Focus 2. apply (nthopt_preserves_wf _ _ H0 _ _ e1). fold cps_cvt_fn_list.
  apply (fun H1 H2 H3 => proj1 (proj2 usubst_preserves_wf') 2 1 (cps_cvt e') H1 1 H2 (Fix_c (cps_cvt_fn_list es)) H3 1) ; auto ; try lia.
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
  rewrite (proj1 (proj2 ksubst_closed) 0 0) ; try lia.
  Focus 2. eapply cps_val_kvar_closed ; eauto. eapply (proj1 eval_preserves_wf) ; eauto.
  rewrite (proj1 kshift_zero).
  rewrite ksubst_cps_cvts2 ; auto.
  simpl. rewrite (proj1 (proj2 ksubst_closed) 0 0) ; eauto ; try lia.
  fold ksubst_vals cps_cvt_vals. 
  rewrite ksubst_vals_append.
  erewrite (proj1 (proj2 (proj2 ksubst_closed))) ; eauto ; try lia. simpl.
  repeat if_split.
  rewrite (proj1 (proj2 kshift_closed') 0 0).
  Focus 2. eapply cps_val_kvar_closed ; eauto. eapply (proj1 eval_preserves_wf) ; eauto.
  rewrite ksubst_gt_indices ; try lia.
  specialize (H0 H8 d k (ws ++ [cps_cvt_val v]) H2).
  assert (vals_wf 0 0 (ws ++ [cps_cvt_val v])).
  rewrite vals_wf_append. split ; auto. constructor.
  eapply cps_val_kvar_closed ; eauto. eapply (proj1 eval_preserves_wf) ; eauto. constructor.
  specialize (H0 H1 v').
  rewrite <- app_assoc in H0. simpl in H0. rewrite H0.
  rewrite (proj1 (proj2 ksubst_closed) 0 0) ; try lia ; auto.
  rewrite ksubst_vals_append.
  rewrite (proj1 (proj2 (proj2 ksubst_closed)) 0 0) ; try lia ; auto. simpl.
  repeat if_split. rewrite (proj1 (proj2 kshift_closed') 0 0).
  Focus 2. eapply cps_val_kvar_closed ; eauto. eapply (proj1 eval_preserves_wf) ; eauto.
  rewrite ksubst_gt_indices ; try lia.
  rewrite <- app_assoc. tauto.
  Grab Existential Variables.
  apply (cps_kvar_closed) ; eauto.
  apply (cps_kvar_closed) ; eauto.
  apply (cps_kvar_closed) ; eauto.
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

*)
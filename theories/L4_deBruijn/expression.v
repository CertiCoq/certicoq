Require Import Arith BinNat String List Omega Program Psatz.
Require Import Common.Common.
Open Scope N_scope.
Opaque N.add.
Opaque N.sub.

(** A tactic for simplifying numeric tests. *)
Ltac if_split := 
  match goal with
    | [ |- context[if ?e then _ else _] ] => 
      destruct e; simpl; try lia; auto; try subst
  end.

Class Eq (A:Type) :=
  {
    eq_dec: forall (x y:A), {x = y} + {x<>y}
  }.

(** using [N] instead of [nat] **)
Instance NEq: Eq N := { eq_dec := N.eq_dec }.
Instance NatEq: Eq nat := { eq_dec := eq_nat_dec }.

Definition lt_dec (x y:N): {x < y} + { x >= y}.
  refine (match x <? y as z return (x <? y) = z -> {x < y} + {x >= y} with
            | true => fun H => left _ (proj1 (N.ltb_lt x y) H)
            | false => fun H => right _
          end eq_refl).
  intro. unfold N.ltb in *. rewrite H0 in H. discriminate.
Defined.

Lemma Nlt_or_ge: forall n m:N, n < m \/ m <= n.
Proof. 
  intros n m. lia.
Qed.

Lemma Nmax_plusr: forall x y, exists j, Nmax x y = j + y.
Proof.
  intros x y. destruct (N.max_spec x y) as [[h j]|[h j]].  
  - exists 0. lia. 
  - exists (x - y). replace (x - y + y) with x. assumption. lia.
Qed.
Lemma Nmax_plusl: forall x y, exists j, Nmax x y = j + x.
Proof.
  intros x y. replace (N.max x y) with (N.max y x); try lia.
  apply Nmax_plusr.
Qed.

(**************************)
(** * Source Expressions. *)
(**************************)

(* data constructors *)
Definition dcon := N.
Definition dcon0 := N0.

(** Source expressions, represented using deBruijn notation *)
Inductive exp: Type :=
| Var_e: N -> exp
| Lam_e: exp -> exp
| App_e: exp -> exp -> exp
| Con_e: dcon -> exps -> exp
| Match_e: exp -> branches_e -> exp
| Let_e: exp -> exp -> exp
| Fix_e: efnlst -> N -> exp  (* implicitly lambdas *)
with exps: Type :=
| enil: exps
| econs: exp -> exps -> exps
with efnlst: Type :=
| eflnil: efnlst
| eflcons: exp -> efnlst -> efnlst
with branches_e: Type :=
| brnil_e: branches_e
| brcons_e: dcon -> N -> exp -> branches_e -> branches_e.
Notation "[| e |]" := (econs e enil).
Notation "[! f !]" := (eflcons f eflnil).
Hint Constructors exp exps branches_e.
Scheme exp_ind' := Induction for exp Sort Prop
with exps_ind'  := Induction for exps Sort Prop
with efnlst_ind'  := Induction for efnlst Sort Prop
with branches_e_ind' := Induction for branches_e Sort Prop.
Combined Scheme my_exp_ind from
         exp_ind', exps_ind', efnlst_ind', branches_e_ind'.
(* Notes on source expressions:  

   [Let_e e1 e2] corresponds to (let x0 := e1 in e2)

   [Fix_e [e1;e2;...;en]] produces an n-tuple of functions.  Each expression
   is treated as binding (a) the n-tuple, and then (b) a function argument.
   (Thus going under Fix_e increases index by 2).

   So this is similar to saying something like:

    let rec f1 = \x1.e1
        and f2 = \x2.e2
        ...
        and fn = \xn.en
    in
      (f1,f2,...,fn)

   When [e] evaluates to [Fix_e [e1;e2;...;en]], then [Proj_e e i] evaluates
   to [ei{0 := Fix_e[e1;e2;...;en]}].  That is, we unwind the recursion when
   you project something out of the tuple.

   For [Match_e] each [branch], (d, n, e), binds [n] variables,
   corresponding to the arguments to the data constructor d.  
*)

Fixpoint exps_length (es:exps) : N :=
  match es with
    | enil => N0
    | econs _ es => 1 + (exps_length es)
  end.

(** Find the nth component in exps **)
Fixpoint enthopt (n:nat) (xs:efnlst): option exp :=
  match n, xs with 
    | 0%nat, eflcons h _ => Some h
    | S n, eflcons _ t => enthopt n t
    | _, _ => None
  end.

(** [exp_wf i e] ensures there is no free variable above [i]. *)
Inductive exp_wf: N -> exp -> Prop :=
| var_e_wf: forall i j, j < i -> exp_wf i (Var_e j)
| lam_e_wf: forall i e, exp_wf (1 + i) e -> exp_wf i (Lam_e e)
| app_e_wf: forall i e1 e2, exp_wf i e1 -> exp_wf i e2 ->
                             exp_wf i (App_e e1 e2)
| con_e_wf: forall i d es, exps_wf i es -> exp_wf i (Con_e d es)
| match_e_wf: forall i e bs, exp_wf i e -> branches_wf i bs ->
                              exp_wf i (Match_e e bs)
| let_e_wf: forall i e1 e2, exp_wf i e1 -> exp_wf (1 + i) e2 ->
                             exp_wf i (Let_e e1 e2)
| fix_e_wf: forall i (es:efnlst) k, efnlst_wf (2 + i) es ->
                                     exp_wf i (Fix_e es k)
with exps_wf: N -> exps -> Prop :=
| enil_wf: forall i, exps_wf i enil
| econs_wf: forall i e es, exp_wf i e -> exps_wf i es -> exps_wf i (econs e es)
with efnlst_wf: N -> efnlst -> Prop :=
| flnil_wf_e: forall i, efnlst_wf i eflnil
| flcons_wf_e: forall i e es, exp_wf i e -> efnlst_wf i es ->
                           efnlst_wf i (eflcons e es)
with branches_wf: N -> branches_e -> Prop :=
| brnil_wf: forall i, branches_wf i brnil_e
| brcons_wf: forall i d n e bs, exp_wf (n + i) e -> branches_wf i bs ->
                                branches_wf i (brcons_e d n e bs).
Hint Constructors exp_wf exps_wf branches_wf.
Scheme exp_wf_ind2 := Induction for exp_wf Sort Prop
with exps_wf_ind2 := Induction for exps_wf Sort Prop
with efnlst_wf_ind2 := Induction for efnlst_wf Sort Prop
with branches_wf_ind2 := Induction for branches_wf Sort Prop.
Combined Scheme my_exp_wf_ind from
         exp_wf_ind2, exps_wf_ind2, efnlst_wf_ind2, branches_wf_ind2.


(** Weakening with respect to [exp_wf]. *)
Lemma weaken_wf' :
  (forall i e, exp_wf i e -> forall j, i < j -> exp_wf j e) /\
  (forall i es, exps_wf i es -> forall j, i < j -> exps_wf j es) /\
  (forall i es, efnlst_wf i es -> forall j, i < j -> efnlst_wf j es) /\
  (forall i bs, branches_wf i bs -> forall j, i < j -> branches_wf j bs).
Proof.  
  apply my_exp_wf_ind; intros; econstructor; auto; try lia; 
  match goal with
    | [ H: forall _, _ -> exp_wf _ ?e |- exp_wf _ ?e] => apply H; lia
    | _ => idtac
  end.
  apply (H (2 + j)). lia.
Qed.

Lemma weaken_wf: forall i e, exp_wf i e -> forall j, i < j -> exp_wf j e.
  apply (proj1 weaken_wf').
Qed.

(** We can always weaken a closed expression. *)
Lemma weaken_closed: forall e i, exp_wf 0 e -> exp_wf i e.
  intros. destruct i; auto; eapply weaken_wf; eauto; lia.
Qed.

Lemma weaken_closeds: forall es i, exps_wf 0 es -> exps_wf i es.
  intros; destruct i; auto; eapply (proj1 (proj2 weaken_wf')); eauto; lia.
Qed.

Lemma weaken_branches: forall bs i, branches_wf 0 bs -> branches_wf i bs.
  intros; destruct i; auto; eapply (proj2 (proj2 weaken_wf')); eauto; lia.
Qed.

Hint Resolve weaken_closed weaken_closeds weaken_branches.

(* optimised *)
(** Shift all variables [i] equal or above [k] by [n]. *)
Section SHIFT.
  Variable shift: N -> N -> exp -> exp.
  Fixpoint shift_exps' n k bs :=
    match bs with
    | enil => enil
    | econs e es => econs (shift n k e) (shift_exps' n k es)
    end.
  Fixpoint shift_efnlst n k bs :=
    match bs with
    | eflnil => eflnil
    | eflcons e es => eflcons (shift n k e) (shift_efnlst n k es)
    end.
  Fixpoint shift_branches' n k bs :=
    match bs with
    | brnil_e => brnil_e
    | brcons_e d na e brs => brcons_e d na (shift n (k+na) e) (shift_branches' n k brs)
    end.
End SHIFT.

Fixpoint shift n k e := 
  match e with
    | Var_e i => Var_e (if lt_dec i k then i else i + n)
    | App_e e1 e2 => App_e (shift n k e1) (shift n k e2)
    | Lam_e e' => Lam_e (shift n (1 + k) e')
    | Con_e d es => Con_e d (shift_exps' shift n k es)
    | Let_e e1 e2 => Let_e (shift n k e1) (shift n (1 + k) e2)
    | Match_e e bs => Match_e (shift n k e) (shift_branches' shift n k bs)
    | Fix_e es k => Fix_e (shift_efnlst shift n (2 + k) es) k
  end.

Definition shifts := shift_exps' shift.
Definition shift_fns := shift_efnlst shift.
Definition shift_branches := shift_branches' shift.

Lemma shift_0:
  (forall d i, shift 0 i d = d) /\
  (forall es i, shifts 0 i es = es) /\
  (forall es i, shift_fns 0 i es = es) /\
  (forall bs i, shift_branches 0 i bs = bs).
Proof.
  apply my_exp_ind; simpl; intros; try reflexivity;
  try (solve[apply f_equal; rewrite H; reflexivity]);
  try (solve[apply f_equal2; try rewrite H; try rewrite H0; reflexivity]).
  - if_split. replace (n+0) with n. reflexivity. lia.
Qed.
(*
(* unoptimised *)
(** Shift all variables [i] equal or above [k] by [1]. *)
Section SHFT.
  Variable shft: N -> exp -> exp.
  Definition shfts' k es := List.map (shft k) es.
  Definition shft_branch' (k:N) (b:dcon*N*exp) :=
    br (fun d n e => (d,n,shft (1+k) e)) b.
  Definition shft_branches' k bs := List.map (shft_branch' k) bs.
End SHFT.

Fixpoint shft k e := 
  match e with
    | Var_e i => Var_e (if lt_dec i k then i else i + 1)
    | App_e e1 e2 => App_e (shft k e1) (shft k e2)
    | Lam_e e' => Lam_e (shft (1 + k) e')
    | Con_e d es => Con_e d (shfts' shft k es)
    | Let_e e1 e2 => Let_e (shft k e1) (shft (1 + k) e2)
    | Match_e e bs => Match_e (shft k e) (shft_branches' shft k bs)
    | Fix_e es => Fix_e (shfts' shft (2 + k) es)
    | Proj_e e m => Proj_e (shft k e) m
  end.
Definition shfts := shfts' shft.
Definition shft_branch := shft_branch' shft.
Definition shft_branches := shft_branches' shft.

(* optimised *)
(** Substitute [v] for variable [k] in [e]. *)
Section SUBST.
  Variable subst: exp -> N -> exp -> exp.
  Definition substs' v k es := List.map (subst v k) es.
  Definition subst_branch' v k b := br (fun d n e => (d,n,subst v (n+k) e)) b.
  Definition subst_branches' v k bs := List.map (subst_branch' v k) bs.
End SUBST.
  
Fixpoint subst (v:exp) k (e:exp): exp :=
  match e with
    | Var_e i => if lt_dec i k then Var_e i
                 else if eq_dec i k then shift k 0 v
                      else Var_e (i - 1)
    | App_e e1 e2 => App_e (subst v k e1) (subst v k e2)
    | Lam_e e' => Lam_e (subst v (1 + k) e')
    | Con_e d es => Con_e d (substs' subst v k es)
    | Let_e e1 e2 => Let_e (subst v k e1) (subst v (1 + k) e2)
    | Match_e e bs => Match_e (subst v k e) (subst_branches' subst v k bs)
    | Fix_e es => Fix_e (substs' subst v (2 + k) es)
    | Proj_e e m => Proj_e (subst v k e) m
  end.
Definition substs := substs' subst.
Definition subst_branch := subst_branch' subst.
Definition subst_branches := subst_branches' subst.
***)

(** Substitute [v] for variable [k] in [e];
*** no shifting, only for evaluation of closed expressions. *)
Function sbst (v:exp) k (e:exp): exp :=
  match e with
    | Var_e i => if lt_dec i k then Var_e i
                 else if eq_dec i k then v else Var_e (i - 1)
    | App_e e1 e2 => App_e (sbst v k e1) (sbst v k e2)
    | Lam_e e' => Lam_e (sbst v (1 + k) e')
    | Con_e d es => Con_e d (sbsts v k es)
    | Let_e e1 e2 => Let_e (sbst v k e1) (sbst v (1 + k) e2)
    | Match_e e bs => Match_e (sbst v k e) (sbst_branches v k bs)
    | Fix_e es k => Fix_e (sbst_efnlst v (2 + k) es) k
  end
with sbsts (v:exp) k (es:exps) : exps :=
       match es with
         | enil => enil
         | econs f fs => econs (sbst v k f) (sbsts v k fs)
       end
with sbst_efnlst (v:exp) k (es:efnlst) : efnlst :=
       match es with
         | eflnil => eflnil
         | eflcons f fs => eflcons (sbst v k f) (sbst_efnlst v k fs)
       end
with sbst_branches (v:exp) k (bs:branches_e) : branches_e :=
       match bs with
         | brnil_e => brnil_e
         | brcons_e d n e bs =>
           brcons_e d n (sbst v (n+k) e) (sbst_branches v k bs)
       end.

(** Notation for optimised substitution. **
Class Substitute (v:Type) (t:Type) := { substitute: v -> N -> t -> t }.
Notation "M { j := N }" := (substitute N j M)
                      (at level 10, right associativity).
Instance ExpSubstitute: Substitute exp exp :=
  { substitute := subst}.
Instance ExpsSubstitute: Substitute exp (list exp) :=
  { substitute := substs}.
Instance BranchSubstitute: Substitute exp (dcon * N * exp) :=
  { substitute := subst_branch}.
Instance BranchesSubstitute: Substitute exp (list (dcon * N * exp)) := 
  { substitute := subst_branches}.
**)

(** Notation for unoptimised substitution. *)
Class Sbstitute (v:Type) (t:Type) := { sbstitute: v -> N -> t -> t }.
Notation "M { j ::= N }" := (sbstitute N j M)
                      (at level 10, right associativity).
Instance ExpSbstitute: Sbstitute exp exp :=
  { sbstitute := sbst}.
Instance ExpsSbstitute: Sbstitute exp exps :=
  { sbstitute := sbsts}.
Instance EfnlstSbstitute: Sbstitute exp efnlst :=
  { sbstitute := sbst_efnlst}.
Instance BranchesSbstitute: Sbstitute exp branches_e := 
  { sbstitute := sbst_branches}.

Lemma Var_e_sbst_inv:
  forall e j v x, Var_e j = sbst v x e -> exists k, e = Var_e k.
Proof.
  induction e; simpl; intros; try discriminate.
  - exists n. reflexivity.
Qed.

(* These lemmas come from "A Head-to-Head Comparison of deBruijn
   Indices and Names" by Stefan Berghofer and Christian Urban. It's
   notable that they and others remark that coming up with these on
   your own is quite difficult...

   I don't actually need these yet, so they are not quite up to date
   with the rest of the development.  *)
(*
Lemma shift_twice:
  forall N i j m n, i <= j -> j <= i + m ->
 shift n j (shift m i N) = shift (m + n) i N.
Proof.
  assert ((forall N i j m n, i <= j -> j <= i + m ->
 shift n j (shift m i N) = shift (m + n) i N) /\
          (forall Ns i j m n, i <= j -> j <= i + m ->
 shifts n j (shifts m i Ns) = shifts (m + n) i Ns)).
  apply my_exp_ind; intros; simpl; auto ;
  try (rewrite H; auto; try lia; rewrite H0; auto; try lia; auto).
  repeat if_split. apply f_equal. lia.
  tauto.
Qed.

Lemma shift_subst :
  forall N i k j L, k <= j ->
 shift i k (N{j := L}) = (shift i k N){j+i := L}.
Proof.
  assert ((forall N i k j L, k <= j ->
 shift i k (N{j := L}) = (shift i k N){j+i := L}) /\
          (forall Ns i k j L, k <= j ->
 shifts i k (Ns{j := L}) = (shifts i k Ns){j+i := L})).
  apply my_exp_ind; intros; simpl; auto ;
  try (rewrite H; auto; rewrite H0; auto).
  repeat if_split. destruct (lt_dec j k); try lia.
  rewrite shift_twice; auto; lia.
  destruct (lt_dec n k); try lia; auto. apply f_equal. lia.
  apply f_equal. rewrite H; try lia. simpl.
  replace (1 + j + i) with (1 + (j + i)); auto; lia. 
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
  apply my_exp_ind; simpl; intros; auto ;
  try (rewrite H; auto; try lia; rewrite H0; auto).
  repeat if_split. replace (n + (1 + j) - 1) with (n + j); auto; lia.
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
  apply my_exp_ind; intros; simpl in *; auto ;
  try (rewrite H; auto; rewrite H0; auto).
  repeat if_split.
  assert (0 <= j - i). lia.
  generalize (shift_subst N i 0 (j - i) L H0). intros.
  unfold substitute in H1. simpl in H1.
  rewrite H1. replace (j - i + i) with j; auto. lia.
  destruct (eq_dec n 0). lia.
  generalize  (shift_away_subst L 0 i (n - 1)). intro.
  unfold substitute in H0. simpl in H0.
  specialize (H0 (subst L (n - 1 - i) N)). rewrite H0; auto. lia. lia.
  apply f_equal.
  rewrite H. replace (1 + j - (1 + i)) with (j - i). auto. lia. lia.
  tauto.
Qed.
*)

Fixpoint sbst_list (e:exp) (vs:exps): exp :=
  match vs with
    | enil => e
    | econs v vs => sbst_list (e{0::=v}) vs
  end.

(** Find a branch in a match expression corresponding to a given constructor
    and arity. *)
Fixpoint find_branch (d:dcon) (m:N) (bs:branches_e) : option exp :=
  match bs with
    | brnil_e => None
    | brcons_e d' n e bs =>
      if eq_dec d d' then (if eq_dec n m then Some e else None)
                     else find_branch d m bs
  end.

Fixpoint efnlength (es:efnlst) :=
  match es with
  | eflnil => 0%nat
  | eflcons _ l => S (efnlength l)
  end.

(** Building a Fixpoint substitution. **)
Definition sbst_fix (es:efnlst) (e : exp) : exp :=
  let les := efnlength es in
    fold_left
      (fun bod ndx => e{0::= Fix_e es (N.of_nat ndx)})
      (list_to_zero les) e.

(** Big-step evaluation for [exp]. *)
Inductive eval: exp -> exp -> Prop :=
| eval_Lam_e: forall e, eval (Lam_e e) (Lam_e e)
| eval_App_e: forall e1 e1' e2 v2 v,
                 eval e1 (Lam_e e1') ->
                 eval e2 v2 ->
                 eval (e1'{0 ::= v2}) v -> 
                 eval (App_e e1 e2) v
| eval_Con_e: forall d es vs, evals es vs -> eval (Con_e d es) (Con_e d vs)
| eval_Let_e: forall e1 v1 e2 v2,
                 eval e1 v1 ->
                 eval (e2{0::=v1}) v2 ->
                 eval (Let_e e1 e2) v2
| eval_Match_e: forall e bs d vs e' v,
                   eval e (Con_e d vs) ->
                   find_branch d (exps_length vs) bs = Some e' ->
                   eval (sbst_list e' vs) v ->
                   eval (Match_e e bs) v
| eval_Fix_e: forall es k, eval (Fix_e es k) (Fix_e es k)
| eval_FixApp_e: forall e (es:efnlst) n e2 v2 e' e'',
    eval e (Fix_e es n) ->
    eval e2 v2 ->
    enthopt (N.to_nat n) es = Some e' ->
    eval (App_e (sbst_fix es e') v2) e'' ->
    eval (App_e e e2) e''
with evals: exps -> exps -> Prop :=
     | evals_nil: evals enil enil
     | evals_cons: forall e es v vs, eval e v -> evals es vs ->
                                        evals (econs e es) (econs v vs).
Scheme eval_ind2 := Induction for eval Sort Prop
with evals_ind2 := Induction for evals Sort Prop.
Combined Scheme my_eval_ind from eval_ind2, evals_ind2.

(** some sanity checks of [eval] **)
Lemma eval_idempotent:
  (forall e d, eval e d -> eval d d) /\
  (forall es ds, evals es ds -> evals ds ds).
Proof.
  apply my_eval_ind; simpl; intros; try constructor; try assumption.
Qed.

Lemma eval_single_valued:
  (forall e d, eval e d -> forall f, eval e f -> d = f) /\
  (forall es ds, evals es ds -> forall fs, evals es fs -> ds = fs).
Proof.
  apply my_eval_ind; simpl; intros.
  - inversion H. reflexivity.
  - inversion H2; subst.
    * assert (j0:Lam_e e1' = Lam_e e1'0). { apply H. assumption. }
                                          injection j0; intros h0. subst.
      assert (j1:v2 = v0). { apply H0. assumption. } subst.
      apply H1. assumption.
    * specialize (H _ H5); discriminate.
  - inversion H0. subst. apply f_equal2. reflexivity.
    apply H. assumption.
  - inversion H1. subst.
    assert (j0:v1 = v0). { apply H. assumption. }
    subst. apply H0. assumption.
  - inversion H1. subst.
    specialize (H _ H4). injection H; intros h0 h1. subst. clear H.
    rewrite H5 in e1. injection e1; intros h2. subst. clear e1.
    apply H0. assumption.
  - inversion H. subst. reflexivity.
  - inversion H2; subst.
    * specialize (H _ H5); discriminate.
    * specialize (H _ H5); injection H; intros; subst.
      specialize (H0 _ H6); subst v0.
      assert (e' = e'0) by congruence; subst e'0.
      now apply H1.
  - inversion H. reflexivity.
  - inversion H1. subst. rewrite (H v0); try assumption.
    rewrite (H0 vs0); try assumption. reflexivity.
Qed.

Example x1: exp := Lam_e (Var_e 0).  (* identity *)
Lemma Lx1: forall (e d:exp), eval e d -> eval (App_e x1 e) d.
Proof.
  intros e d h. unfold x1. eapply eval_App_e. apply eval_Lam_e.
  apply h. simpl. apply (proj1 eval_idempotent _ _ h).
Qed.

Example x2: exp := App_e x1 x1.  (* (fun x => x) (fun x => x) *)
Lemma Lx2: forall (e d:exp), eval e d -> eval (App_e x2 e) d.
Proof.
  intros e d h. unfold x2, x1. eapply eval_App_e. 
  - eapply eval_App_e; try constructor.
  - eassumption.
  - simpl. apply (proj1 eval_idempotent _ _ h).
Qed.


(** For testing: a fuel-based interpreter for partial big-step on [exp]. *)
Function eval_n (n:nat) (e:exp) {struct n}: option exp := 
  match n with
    | 0%nat => None
    | S n => match e with
               | Lam_e d => Some (Lam_e d)
               | Fix_e es k => Some (Fix_e es k)
               | Con_e d es => 
                 match evals_n n es with
                     | None => None
                     | Some vs => Some (Con_e d vs)
                 end
               | App_e e1 e2 =>
                 match eval_n n e1 with
                   | Some (Lam_e e1') => 
                     match eval_n n e2 with
                       | None => None
                       | Some e2' => eval_n n (e1'{0 ::= e2'})
                     end
                   | Some (Fix_e es k) =>
                     match eval_n n e2 with
                     | None => None
                     | Some e2' =>
                       match enthopt (N.to_nat k) es with
                       | Some e' =>
                         let t' := sbst_fix es e' in
                         eval_n n (App_e t' e2')
                       | _ => None
                       end
                     end
                   | _ => None
                  end
               | Let_e e1 e2 =>
                 match eval_n n e1 with
                   | None => None
                   | Some v1 => eval_n n (e2{0::=v1})
                 end
               | Match_e e bs =>
                 match eval_n n e with
                   | Some (Con_e d vs) =>
                     match find_branch d (exps_length vs) bs with
                       | None => None
                       | Some e' => eval_n n (sbst_list e' vs)
                     end
                   | _ => None
                 end
               | _ => None
             end
  end
with evals_n n (es:exps) : option exps :=
       match n with
         | 0%nat => None
         | S n => 
           match es with
             | enil => Some enil
             | econs e es => 
               match (eval_n n e, evals_n n es) with
                 | (Some v, Some vs) => Some (econs v vs)
                 | (_, _) => None
               end
           end
       end.
Functional Scheme eval_n_ind2 := Induction for eval_n Sort Prop
with evals_n_ind2 := Induction for evals_n Sort Prop.
Combined Scheme eval_evals_n_ind from eval_n_ind2, evals_n_ind2.

Lemma eval_n_monotone:
  forall (n:nat) e f, eval_n n e = Some f ->
                      forall (m:nat), eval_n (n + m) e = Some f.
Admitted.

Lemma evals_n_monotone:
  forall (n:nat) es fs, evals_n n es = Some fs ->
                      forall (m:nat), evals_n (n + m) es = Some fs.
Admitted.

(***
Lemma eval_n_weaken:
  forall (n:nat),
  (forall e f, eval_n n e = Some f ->
                 forall m, eval_n (n+m) e = Some f) /\
  (forall (es:exps) fs, evals_n n es = Some fs ->
                   forall m, evals_n (n+m) es = Some fs) /\
  (forall (es:efnlst) fs, evals_n n es = Some fs ->
                   forall m, evals_n (n+m) es = Some fs). /\
.
Proof.

Lemma eval_n_monotone:
  (forall (n:nat) e f, eval_n n e = Some f -> eval_n (S n) e = Some f).
Proof.
  induction n; intros.
  - simpl; discriminate.
  - destruct e; simpl; try discriminate; try assumption.
    destruct (eval_n n e1).




(***
Lemma eval_n_monotone:
  forall n:nat,
  (forall e sf, eval_n n e = sf -> forall f, sf = Some f ->
                 eval_n (S n) e = Some f) /\
  (forall es sfs, evals_n n es = sfs -> forall fs, sfs = Some fs ->
                   evals_n (S n) es = Some fs).
Proof.
  intros n.
  Check (eval_evals_n_ind). 
           (fun e f =>
              eval_n n e = Some f -> forall m : nat, eval_n (n + m) e = Some f)).
***)

Lemma eval_n_monotone:
  (forall (n:nat) e sf, eval_n n e = sf -> forall f, sf = Some f ->
                 eval_n (S n) e = Some f).
Proof.
  intros n e.
  functional induction (eval_n n e); intros;
  try solve [simpl; rewrite <- H0; assumption].
  - admit.
  - admit.
  - 


  try discriminate; try assumption.
  - destruct n0; destruct es.
    + simpl in e2. discriminate.
    + simpl in e2. discriminate.
    + simpl in e2. injection e2; intros h. rewrite h. assumption.
    + simpl in e2. destruct (eval_n n0 e); destruct (evals_n n0 es).



Lemma eval_n_monotone:
  (forall (m n:nat) e f, eval_n n e = Some f ->
                 eval_n (n+m) e = Some f).
Proof.
  induction m; intros n e f h.
  - replace (n + 0)%nat with n; try omega. assumption.
  - specialize (IHm (S n)).
    replace (n + S m)%nat with (S n + m)%nat; try omega.
    apply IHm.

  functional induction (eval_n n e); simpl; intros;
  try discriminate; try assumption.
  - 


Lemma eval_n_monotone:
  (forall n e f, eval_n n e = Some f ->
                 forall m, (n < m)%nat -> eval_n m e = Some f).
Proof.
  intros n e f.
  functional induction (eval_n n e); intros; try discriminate;
  assert (h:m = S (m - 1)); try omega; rewrite h; clear h; try assumption.
  - rewrite <- H.
    change (evals_n (m - 1) es = Some vs).
  simpl. injection H; intros h0. rewrite <- h0. 

 simpl. reflexivity.


Lemma eval_n_monotone:
  (forall n e f, eval_n n e = Some f ->
                 forall m, eval_n (n+m) e = Some f).
Proof.
  intros n e f.
  functional induction (eval_n n e); simpl; intros;
  try discriminate; try assumption.
  - 



  apply (eval_n_ind
           (fun n e oe =>
              forall (f:exp), oe = Some f ->
                              forall m : nat, eval_n (n + m) e = Some f));
    simpl; intros; try discriminate; try assumption.
  - 

Lemma eval_n_weaken:
  (forall n e f, eval_n n e = Some f ->
                 forall m, eval_n (n+m) e = Some f) /\
  (forall n es fs, evals_n n es = Some fs ->
                   forall m, evals_n (n+m) es = Some fs).
Proof.
  Check eval_n_ind.
  Check (eval_evals_n_ind). 
           (fun n e f =>
              eval_n n e = Some f -> forall m : nat, eval_n (n + m) e = Some f)).
***********)


(** [eval_n] is sound w.r.t. [eval] **)
Lemma eval_n_Some_Succ:
  forall e (n:nat) v, eval_n n e = Some v -> n = (S (n - 1))%nat.
Proof.
  induction n; intros.
  - simpl in H. discriminate.
  - omega.
Qed.
Lemma evals_n_Some_Succ:
  forall es (n:nat) vs, evals_n n es = Some vs -> n = (S (n - 1))%nat.
Proof.
  induction n; intros.
  - simpl in H. discriminate.
  - omega.
Qed.

Lemma evaln_eval: 
  forall (n:nat),
  (forall (e:exp) v, eval_n n e = Some v -> eval e v) /\
  (forall (es:exps) vs, evals_n n es = Some vs -> evals es vs).
Proof.
  apply (eval_evals_n_ind (fun n e ov => forall v, ov = Some v -> eval e v)
        (fun n es ovs => forall vs, ovs = Some vs -> evals es vs));
  intros; try discriminate.
  + injection H; intros h0. subst. constructor.
  + injection H; intros h0. subst. constructor.
  + injection H0; intros h0. rewrite <- h0. constructor. apply H. assumption.
  + econstructor.
    * specialize (H _ e4). eapply H.
    * specialize (H0 _ e5). eapply H0.
    * specialize (H1 _ H2). apply H1.
  + eapply eval_FixApp_e.
    * specialize (H _ e4). eapply H.
    * specialize (H0 _ e5). apply H0.
    * apply e6.
    * now apply H1.
  + econstructor.
    * specialize (H _ e4). eapply H.
    * specialize (H0 _ H1). apply H0.
  + econstructor; eauto. 
  + injection H; intros h0. subst. constructor.
  + injection H1; intros h0. subst. constructor.
    * apply H. assumption.
    * apply H0. assumption.
Qed.

(** [eval_n] is complete w.r.t. [eval] **)
Lemma eval_evaln:
  (forall (e v:exp), eval e v -> exists (n:nat), eval_n n e = Some v) /\
  (forall (es vs:exps), evals es vs -> exists (n:nat), evals_n n es = Some vs).
Proof.
  apply my_eval_ind; intros; try (solve [exists 1%nat; reflexivity]).
  - destruct H as [x h]. destruct H0 as [x0 h0]. destruct H1 as [x1 h1].
    exists (x+x0+x1)%nat.
    assert (j:=eval_n_Some_Succ _ _ _ h).
    assert (j0:=eval_n_Some_Succ _ _ _ h0).
    assert (j1:=eval_n_Some_Succ _ _ _ h1).
    assert (k:= eval_n_monotone _ _ _ h).
    assert (k0:= eval_n_monotone _ _ _ h0).
    assert (k1:= eval_n_monotone _ _ _ h1).
    rewrite j.
    replace (S (x - 1) + x0 + x1)%nat
    with (S (x + (x0 + x1 - 1)))%nat; try lia.
    simpl. rewrite k.
    replace (x + (x0 + x1 - 1))%nat with (x0 + (x + x1 - 1))%nat; try lia.
    rewrite k0.
    replace (x0 + (x + x1 - 1))%nat with (x1 + (x + x0 - 1))%nat; try lia.
    rewrite k1. reflexivity.
  - destruct H as [x h]. exists (x+1)%nat.
    assert (j:=evals_n_Some_Succ _ _ _ h).
    assert (k:= evals_n_monotone _ _ _ h).
    rewrite j.
    replace (S (x - 1) + 1)%nat with (S (x + 0))%nat; try lia.
    simpl. rewrite k. reflexivity.
  - destruct H as [x h]. destruct H0 as [x0 h0].
    assert (j:=eval_n_Some_Succ _ _ _ h).
    assert (j0:=eval_n_Some_Succ _ _ _ h0).
    assert (k:= eval_n_monotone _ _ _ h).
    assert (k0:= eval_n_monotone _ _ _ h0).
    exists (x+x0)%nat.
    rewrite j.
    replace (S (x - 1) + x0)%nat with (S (x + (x0 - 1)))%nat; try lia.
    simpl. rewrite k.
    replace (x + (x0 - 1))%nat with (x0 + (x - 1))%nat; try lia.
    rewrite k0. reflexivity.
  - destruct H as [x h]. destruct H0 as [x0 h0].
    assert (j:=eval_n_Some_Succ _ _ _ h).
    assert (j0:=eval_n_Some_Succ _ _ _ h0).
    assert (k:= eval_n_monotone _ _ _ h).
    assert (k0:= eval_n_monotone _ _ _ h0).
    exists (x+x0)%nat.
    rewrite j.
    replace (S (x - 1) + x0)%nat with (S (x + (x0 - 1)))%nat; try lia.
    simpl. rewrite k.
    replace (x + (x0 - 1))%nat with (x0 + (x - 1))%nat; try lia.
    rewrite e1. rewrite k0. reflexivity.
  - destruct H as [x h]. destruct H0 as [x0 h0]. destruct H1 as [x1 h1].
    exists (x+x0+x1)%nat.
    assert (j:=eval_n_Some_Succ _ _ _ h).
    assert (j0:=eval_n_Some_Succ _ _ _ h0).
    assert (j1:=eval_n_Some_Succ _ _ _ h1).
    assert (k:= eval_n_monotone _ _ _ h).
    assert (k0:= eval_n_monotone _ _ _ h0).
    assert (k1:= eval_n_monotone _ _ _ h1).
    rewrite j.
    replace (S (x - 1) + x0 + x1)%nat
    with (S (x + (x0 + x1 - 1)))%nat; try lia.
    simpl. rewrite k.
    replace (x + (x0 + x1 - 1))%nat with (x0 + (x + x1 - 1))%nat; try lia.
    rewrite k0.
    replace (x0 + (x + x1 - 1))%nat with (x1 + (x + x0 - 1))%nat; try lia.
    rewrite e3, k1. reflexivity.
  - destruct H as [x h]. destruct H0 as [x0 h0].
    assert (j:=eval_n_Some_Succ _ _ _ h).
    assert (j0:=evals_n_Some_Succ _ _ _ h0).
    assert (k:= eval_n_monotone _ _ _ h).
    assert (k0:= evals_n_monotone _ _ _ h0).
    exists (x+x0)%nat.
    rewrite j.
    replace (S (x - 1) + x0)%nat with (S (x + (x0 - 1)))%nat; try lia.
    simpl. rewrite k.
    replace (x + (x0 - 1))%nat with (x0 + (x - 1))%nat; try lia.
    rewrite k0. reflexivity.
Qed.

(** some concrete examples **)
Example Ke: exp := Lam_e (Lam_e (Var_e 1)).
Example Se: exp := Lam_e (Lam_e (Lam_e
            (App_e (App_e (Var_e 2) (Var_e 0)) (App_e (Var_e 1) (Var_e 0))))).
Example SKKe: exp := App_e (App_e Se Ke) Ke.
Eval vm_compute in (eval_n 1000 (App_e SKKe (Con_e 10 enil))).
Goal eval (App_e SKKe (Con_e 10 enil)) (Con_e 10 enil).
Proof.
  unfold SKKe, Se, Ke. repeat econstructor.
Qed.

Infix "$" := App_e   (at level 201, left associativity).
Definition Ve0 := (Var_e 0).
Definition Ve1 := (Var_e 1).
Definition Ve2 := (Var_e 2).
Definition Ve3 := (Var_e 3).
Definition Ve4 := (Var_e 4).
Definition Ve5 := (Var_e 5).

Definition unsome (x:option exp) : exp :=
  match x with 
    | Some e => e
    | None => Var_e 9999
  end.

(** natural numbers in Church representation **)
Section ChurchNaturals.
Notation ZZ := (Lam_e (Lam_e Ve1)).
Notation SS := (Lam_e (Lam_e (Lam_e (Ve0 $ (Ve2 $ Ve1 $ Ve0))))).
Notation one := (SS $ ZZ).
Notation two := (SS $ one).
Notation three := (SS $ two).
Notation four := (SS $ three).
Notation five := (SS $ four).
Notation six := (SS $ five).
Notation add := (Lam_e (Lam_e (Ve1 $ Ve0 $ SS))).
Notation mul := (Lam_e (Lam_e (Ve1 $ ZZ $ (add $ Ve0)))).

Example One := Eval compute in (unsome (eval_n 100 one)).
Example Two := Eval compute in (unsome (eval_n 100 two)).
Example Three := Eval vm_compute in (unsome (eval_n 100 three)).
Example Four := Eval vm_compute in (unsome (eval_n 100 four)).
Example Five := Eval vm_compute in (unsome (eval_n 100 five)).
Example Six := Eval vm_compute in (unsome (eval_n 100 six)).

Goal eval (SS $ ZZ) One. repeat econstructor. Qed.
Goal eval (add $ ZZ $ one) One. repeat econstructor. Qed.
Goal eval (add $ one $ ZZ) One. repeat econstructor. Qed.
Goal (eval_n 1000 (add $ two $ one)) = Some Three.
vm_compute. reflexivity. Qed.
Goal (eval_n 1000 (add $ two $ three)) = Some Five.
vm_compute. reflexivity. Qed.
Goal (eval_n 1000 (mul $ two $ three)) = Some Six.
vm_compute. reflexivity. Qed.
End ChurchNaturals.
Reset ChurchNaturals.

(** booleans using native data constructors (with no arguments) **)
Notation TT := (0:dcon).
Notation TTT := (Con_e TT enil).
Notation FF := (1:dcon).
Notation FFF := (Con_e FF enil).
(* if b then e1 else e2 *)
Notation ite :=
  (Lam_e (Lam_e (Lam_e
             (Match_e Ve2 (brcons_e TT 0 Ve1 (brcons_e FF 0 Ve0 brnil_e)))))).
Goal eval (ite $ TTT $ FFF $ TTT) FFF.
repeat econstructor. Qed.
Goal eval (ite $ FFF $ FFF $ TTT) TTT.
repeat econstructor. Qed.

(** lists using native data constructors: Cons takes 2 arguments **)
Notation dNil := (2:dcon).
Notation Nil := (Con_e dNil enil).
Notation dCons := (3:dcon).
Notation Cons := (Lam_e (Lam_e (Con_e dCons (econs Ve1 [|Ve0|])))).
Notation cdr :=
  (Lam_e (Match_e Ve0 (brcons_e dNil 0 Nil (brcons_e dCons 2 Ve1 brnil_e)))).

Goal eval (cdr $ Nil) Nil.
eapply eval_App_e.
- eapply eval_Lam_e.
- eapply eval_Con_e. eapply evals_nil.
- eapply eval_Match_e.
  + compute. eapply eval_Con_e. eapply evals_nil.
  + compute. apply f_equal. reflexivity.
  + compute. eapply eval_Con_e. eapply evals_nil.
Qed.

(* test match on a data constructor with an argument *)
Goal eval (cdr $ (Cons $ TTT $ Nil)) Nil.
repeat (try econstructor; try vm_compute).
Qed.

Goal eval (Cons $ TTT $ Nil)
     (Con_e dCons (econs (Con_e TT enil) [|Con_e dNil enil|])).
repeat (try econstructor; try vm_compute).
Qed.
Goal eval (cdr $ (Cons $ FFF $ (Cons $ TTT $ Nil)))
     (Con_e dCons (econs (Con_e TT enil) [|Con_e dNil enil|])).
repeat (try econstructor; try vm_compute).
Qed.


(** Natural numbers using native data constructors **)
Notation ZZ := (0:dcon).
Notation ZZZ := (Con_e ZZ enil).
Notation SS := (1:dcon).
Notation SSS := (Lam_e (Con_e SS [|Ve0|])).
Notation one := (SSS $ ZZZ).
Notation two := (SSS $ one).
Notation three := (SSS $ two).
Notation four := (SSS $ three).
Notation five := (SSS $ four).
Notation six := (SSS $ five).

Example One := Eval compute in (unsome (eval_n 1000 one)).
Print One.
Example Two := Eval compute in (unsome (eval_n 100 two)).
Example Three := Eval vm_compute in (unsome (eval_n 100 three)).
Example Four := Eval vm_compute in (unsome (eval_n 100 four)).
Example Five := Eval vm_compute in (unsome (eval_n 100 five)).
Example Six := Eval vm_compute in (unsome (eval_n 100 six)).

Goal eval (SSS $ one) Two.
repeat econstructor. 
Qed.

Goal eval (SSS $ three) Four.
repeat econstructor. 
Qed.

(** fixpoints **)
Definition copy : exp :=
  (Fix_e [!Lam_e (Match_e Ve0 (brcons_e ZZ 0 ZZZ 
            (brcons_e SS 1 (SSS $ ((Var_e 2) $ Ve0)) brnil_e)))!] 0).

Goal eval (copy $ ZZZ) ZZZ.
unfold copy.
econstructor 7 ; try vm_compute; try constructor. econstructor.
repeat (try econstructor ; try vm_compute).
Qed.

Eval vm_compute in eval_n 100 (copy $ six).


(**** Fixpoints???  ****
Goal eval (copy $ one) One.
unfold copy. eapply eval_App_e.
- eapply eval_Lam_e. 
- eapply eval_App_e.
  + eapply eval_Lam_e. 
  + repeat econstructor.
  + simpl. eapply eval_Con_e. repeat econstructor.
- vm_compute. eapply eval_Match_e.
  + eapply eval_Con_e. repeat econstructor.
  + unfold find_branch. repeat if_split. 
    * discriminate.
    * apply f_equal. eapply eval_Proj_e.
    

repeat (try econstructor; try vm_compute).
Qed.

Definition copy : exp :=
  Lam_e (Fix_e ((eflcons (Match_e Ve1
                            (brcons_e ZZ 0 ZZZ
                                      (brcons_e SS 1 (Proj_e Ve0 1) brnil_e))) eflnil))).

Goal eval (copy $ ZZZ) ZZZ.
repeat (try econstructor; try vm_compute).


Definition add :=
  (Lam_e (Lam_e (Proj (Fix_e
                   (eflcons (Match_e Ve1
                            (brcons_e ZZ 0 Ve0
                                      (brcons_e SS 1
                                                (Proj_e SSS 0) brnil_e)))
                            eflnil)))).

Goal eval (add $ ZZZ $ ZZZ) ZZZ.
unfold add. eapply eval_App_e. 
- eapply eval_App_e.
  + eapply eval_Lam_e. 
  + eapply eval_Con_e. constructor.
  + eapply eval_Lam_e.
- eapply eval_Con_e. constructor.
- vm_compute. eapply eval_Fix_e.


Goal eval one (Con_e SS [|ZZZ|]).
eapply eval_App_e.
eapply eval_Lam_e.
eapply eval_Con_e. eapply evals_nil.
simpl. eapply eval_Con_e. eapply evals_cons.
eapply eval_Con_e. eapply evals_nil. eapply evals_nil.
Qed.

Example One := Eval compute in (unsome (eval_n 1000 one)). 
Example Two := Eval compute in (unsome (eval_n 100 two)).
Example Three := Eval vm_compute in (unsome (eval_n 100 three)).
Example Four := Eval vm_compute in (unsome (eval_n 100 four)).
Example Five := Eval vm_compute in (unsome (eval_n 100 five)).
Example Six := Eval vm_compute in (unsome (eval_n 100 six)).



(** If [e] is an [i+1] expression, and [v] is a closed expression, then 
    for any [k <= i], substituting [v] for [k] in e yields an [i] expression.

    I wish I could generalize this to non-closed expressions, but haven't
    been able to.  But perhaps the whole point is that I need to shift [v]
    or something.
 *)
Lemma sbst_preserves_wf' :
  (forall i' e, exp_wf i' e ->
     forall i, i' = 1 + i -> forall v, exp_wf 0 v ->
       forall k, k <= i -> exp_wf i (e{k::=v})) /\
  (forall i' es, exps_wf i' es ->
     forall i, i' = 1 + i -> forall v, exp_wf 0 v ->
       forall k, k <= i -> exps_wf i (es{k::=v})) /\
  (forall i' es, efnlst_wf i' es ->
     forall i, i' = 1 + i -> forall v, exp_wf 0 v ->
       forall k, k <= i -> efnlst_wf i (es{k::=v})) /\
  (forall i' bs, branches_wf i' bs ->
     forall i, i' = 1 + i -> forall v, exp_wf 0 v ->
       forall k, k <= i -> branches_wf i (bs{k::=v})).
Proof.
  apply my_exp_wf_ind; simpl; intros; subst; eauto.
  - repeat if_split; try (constructor; auto; lia).
  - constructor. apply H; try lia; auto.
  - constructor; auto. apply H0; try lia; auto.
  - constructor; auto. apply H; try lia; auto.
  - constructor; auto. 
  - constructor; auto. 
  - constructor; auto. apply H; try lia; auto.
Qed.

(** Corrollary:  if [e] is an [i+1] expression, and [v] is closed, then 
   substituting [v] for [0] in [e] yields an [i] expression. *)
Lemma sbst_preserves_exp_wf :
  forall i e, exp_wf (1 + i) e -> forall v, exp_wf 0 v ->
                                            exp_wf i (e {0::= v}).
Proof.
  intros. eapply (proj1 sbst_preserves_wf'); eauto; lia.
Qed.

Lemma subst_list_preserves_exp_wf :
  forall vs, exps_wf 0 vs -> 
             forall i e, exp_wf ((exps_length vs) + i) e ->
                         exp_wf i (sbst_list e vs).
Proof.
  induction vs; simpl; intros; subst; auto. 
  inversion H; clear H; subst.
  replace (1 + exps_length vs + i) with (1 + (exps_length vs + i)) in H0;
    try lia.
  apply IHvs; auto. apply sbst_preserves_exp_wf; auto.
Qed.
  
Lemma sbst_preserves_exps_wf :
  forall i es, exps_wf (1 + i) es -> 
               forall v, exp_wf 0 v -> exps_wf i (es {0 ::= v}).
Proof.
  intros. eapply (proj1 (proj2 sbst_preserves_wf')); eauto; lia.
Qed.
Lemma sbst_preserves_branches_wf :
  forall i bs, branches_wf (1 + i) bs ->
               forall v, exp_wf 0 v -> branches_wf i (bs {0 ::= v}).
Proof.
  intros; eapply (proj2 (proj2 sbst_preserves_wf')); eauto; lia.
Qed.
Hint Resolve sbst_preserves_exp_wf sbst_preserves_exps_wf 
     sbst_preserves_branches_wf.

Lemma nthopt_preserves_wf :
  forall i es, efnlst_wf i es ->
               forall n e, enthopt n es = Some e -> exp_wf i e.
Proof.
  induction es; simpl; intros. 
  - destruct n; discriminate.
  - inversion H; subst. destruct n; simpl in *.
    + injection H0; intros; subst; auto. 
    + specialize (IHes H5 n e0).
      apply IHes. auto.
Qed.

Lemma find_branch_preserves_wf :
  forall i bs, branches_wf i bs ->
               forall d m e, find_branch d m bs = Some e -> exp_wf (m+i) e.
Proof.
  induction 1; simpl; intros a b c; repeat if_split; intro H1;
  try discriminate.
  - injection H1; intros; subst; auto. 
  - eapply IHbranches_wf; eauto.
Qed.
Hint Resolve find_branch_preserves_wf.

(** Evaluation preserves closed expressions.  I wish I could generalize this
   to evaluation preserves [i] expressions. *)
Lemma eval_preserves_wf' :
  (forall e v, eval e v -> exp_wf 0 e -> exp_wf 0 v) /\
  (forall es vs, evals es vs -> exps_wf 0 es -> exps_wf 0 vs).
Proof.
  apply my_eval_ind; simpl; intros; auto.
  - inversion H2; clear H2; subst.
    specialize (H H6); clear H6. specialize (H0 H7); clear H7.
    inversion H; clear H; subst. apply H1; auto. 
  - inversion H0; auto. 
  - inversion H1; auto.
  - inversion H1; clear H1; subst. apply H0; auto.
    apply subst_list_preserves_exp_wf. specialize (H H5). inversion H; subst.
    auto. eapply find_branch_preserves_wf; eauto.
  - inversion H0; subst. clear H0.
    specialize (H H3). inversion H; subst.
    apply (fun H' => sbst_preserves_exp_wf 0 (Lam_e e') H' (Fix_e es) H).
    constructor.  eapply nthopt_preserves_wf; eassumption.
  - inversion H1; subst. constructor; auto.
Qed.
Definition eval_preserves_wf := proj1 eval_preserves_wf'.
Definition evals_preserves_wf := proj2 eval_preserves_wf'.

(** Characterize values **)
Inductive is_value: exp -> Prop :=
| var_is_value: forall i, is_value (Var_e i)
| lam_is_value: forall e, is_value (Lam_e e)
| con_is_value: forall d es, are_values es -> is_value (Con_e d es)
| fix_is_value: forall es, is_value (Fix_e es)
with are_values: exps -> Prop :=
| enil_are_values: are_values enil
| econs_are_values: forall e es, is_value e -> are_values es ->
                                 are_values (econs e es).
Scheme is_value_ind2 := Induction for is_value Sort Prop
with are_values_ind2 := Induction for are_values Sort Prop.
Combined Scheme my_is_value_ind from is_value_ind2, are_values_ind2.
Hint Constructors is_value are_values.

(** Show that evaluation always yields a value. *)
Lemma eval_yields_value' :
  (forall e v, eval e v -> is_value v) /\
  (forall es vs, evals es vs -> are_values vs).
Proof.
  apply my_eval_ind; simpl; intros; auto; try constructor; auto.
Qed.
Definition eval_yields_value := proj1 eval_yields_value'.
Definition evals_yields_values := proj2 eval_yields_value'.
Hint Resolve eval_yields_value evals_yields_values.

(** Computable test as to whether a source expression is already a
    value (a.k.a., atomic).  *)
Fixpoint is_valueb (e:exp): bool :=
  match e with
    | Var_e _ => true
    | Lam_e _ => true
    | App_e _ _  => false
    | Con_e _ es => are_valuesb es
    | Match_e _ _ => false
    | Let_e _ _ => false
    | Fix_e _ => true
    | Proj_e _ _ => false
  end
with are_valuesb (es:exps): bool :=
       match es with
         | enil => true
         | econs f fs => if is_valueb f then are_valuesb fs else false
       end.

Lemma is_valueb_corr' :
  (forall e, is_valueb e = true <-> is_value e) /\
  (forall es, are_valuesb es = true <-> are_values es) /\
  (forall (es:efnlst), True) /\
  (forall (bs:branches_e), True).
Proof.
  apply my_exp_ind; simpl; intros; split; intros; auto;
  try discriminate; try inversion H1.
  - constructor. rewrite <- H. auto.
  - inversion H0; subst. rewrite H. auto.
  - inversion H0; try discriminate.
  - destruct (is_valueb e); try discriminate. constructor.
    + apply H; auto.
    + apply H0; auto. 
  - inversion H1; subst. destruct (is_valueb e). 
    + tauto. 
    + apply H. auto.
Qed.
Definition is_valueb_corr := proj1 is_valueb_corr'.
Definition are_valuesb_corr := proj1 (proj2 is_valueb_corr').
Hint Rewrite is_valueb_corr.
Hint Rewrite are_valuesb_corr.
Hint Resolve is_valueb_corr.
Hint Resolve are_valuesb_corr.

Fixpoint exps_append (es1 es2:exps) : exps :=
  match es1 with
    | enil => es2
    | econs e es => econs e (exps_append es es2)
  end.
Lemma exps_append_enil_r:
  forall (es:exps), exps_append es enil = es.
Proof.
  induction es; simpl. reflexivity. rewrite IHes. reflexivity.
Qed.

Lemma are_values_append :
  forall es1 es2, (are_values es1 /\ are_values es2) <->
                  are_values (exps_append es1 es2).
Proof.
  induction es1 ; simpl ; intros ; split ; intro.
  - destruct H ; auto.
  - destruct H ; auto.
  - destruct H. inversion H. subst. constructor ; auto. rewrite <- IHes1. auto.
  - inversion H ; subst. rewrite <- IHes1 in H3. destruct H3. split ; auto.
Qed.
Hint Resolve are_values_append.

***************)
Require Import Coq.Arith.Arith Coq.ZArith.ZArith Coq.NArith.BinNat
        Coq.Lists.List Coq.micromega.Lia Coq.micromega.Lia Coq.Program.Program
        Coq.micromega.Psatz.
Require Import FunInd.
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

(** Inversion tactic *)
Ltac inv H := inversion H; clear H; subst.

(** Try rewriting (with inductive hyps usually) *)
Ltac rewrite_hyps :=
  repeat match goal with
    | [ H : _ |- _ ] => rewrite !H
  end.

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

Lemma Nmax_plusr: forall x y, exists j, N.max x y = j + y.
Proof.
  intros x y. destruct (N.max_spec x y) as [[h j]|[h j]].  
  - exists 0. lia. 
  - exists (x - y). replace (x - y + y) with x. assumption. lia.
Qed.
Lemma Nmax_plusl: forall x y, exists j, N.max x y = j + x.
Proof.
  intros x y. replace (N.max x y) with (N.max y x); try lia.
  apply Nmax_plusr.
Qed.

(**************************)
(** * Source Expressions. *)
(**************************)

(* data constructors *)
Definition dcon : Set := inductive * N.
#[export] Instance DconEq : Eq dcon := _.

(** Source expressions, represented using deBruijn notation *)
Inductive exp: Type :=
| Var_e: N -> exp
| Lam_e: name -> exp -> exp
| App_e: exp -> exp -> exp
| Con_e: dcon -> exps -> exp
| Match_e: exp -> forall (pars:N) (* # of parameters *), branches_e -> exp
| Let_e: name -> exp -> exp -> exp
| Fix_e: efnlst -> N -> exp  (* implicitly lambdas *)
| Prf_e: exp
| Prim_val_e : primitive -> exp
| Prim_e: positive -> exp
with exps: Type :=
| enil: exps
| econs: exp -> exps -> exps
with efnlst: Type :=
| eflnil: efnlst
| eflcons: name -> exp -> efnlst -> efnlst
with branches_e: Type :=
| brnil_e: branches_e
(* in  [brcons_e d (n,lnames) ...], is there a guarantee that [n=length lnames]?
If yes, does the wf definition for LambdaBoxLocal imply the above? *)
| brcons_e: dcon -> (N * (* # args *) list name (* arg names *)) -> exp ->
            branches_e -> branches_e.
Notation "[| e |]" := (econs e enil).
Notation "[! fn := f !]" := (eflcons fn%bs f eflnil).
#[export] Hint Constructors exp exps branches_e : core.
Scheme exp_ind' := Induction for exp Sort Prop
with exps_ind'  := Induction for exps Sort Prop
with efnlst_ind'  := Induction for efnlst Sort Prop
with branches_e_ind' := Induction for branches_e Sort Prop.
Combined Scheme my_exp_ind from
         exp_ind', exps_ind', efnlst_ind', branches_e_ind'.
(* Notes on source expressions:  

   [Let_e e1 e2] corresponds to (let x0 := e1 in e2)

   [Fix_e [e1;e2;...;en]] produces an n-tuple of functions.  Each expression
   is treated as binding n functions.
   (Thus going under Fix_e increases index by n).

   For [Match_e] each [branch], (d, n, e), binds [n] variables,
   corresponding to the arguments to the data constructor d.  
*)

Fixpoint exps_length (es:exps) : N :=
  match es with
    | enil => N0
    | econs _ es => 1 + (exps_length es)
  end.

Fixpoint efnlst_length (es:efnlst) : N :=
  match es with
    | eflnil => N0
    | eflcons _ _ es => 1 + (efnlst_length es)
  end.

(** Find the nth component in exps **)
Fixpoint enthopt (n:nat) (xs:efnlst): option exp :=
  match n, xs with 
    | 0%nat, eflcons _ h _ => Some h
    | S n, eflcons _ _ t => enthopt n t
    | _, _ => None
  end.

Definition nargs (n : N * list name) : N := fst n.
Definition arg_names (n : N * list name) : list name := snd n.

Definition isLambda (e : exp) :=
  match e with
  | Lam_e _ _ => True
  | _ => False
  end.

(** [exp_wf i e] ensures there is no free variable above [i]. *)
Inductive exp_wf: N -> exp -> Prop :=
| var_e_wf: forall i j, j < i -> exp_wf i (Var_e j)
| lam_e_wf: forall i n e,
    exp_wf (1 + i) e -> exp_wf i (Lam_e n e)
| app_e_wf: forall i e1 e2,
    exp_wf i e1 -> exp_wf i e2 ->
    exp_wf i (App_e e1 e2)
| con_e_wf: forall i d es,
    exps_wf i es -> exp_wf i (Con_e d es)
| match_e_wf: forall i e n bs,
    exp_wf i e -> branches_wf i bs ->
    exp_wf i (Match_e e n bs)
| let_e_wf: forall i n e1 e2,
    exp_wf i e1 -> exp_wf (1 + i) e2 ->
    exp_wf i (Let_e n e1 e2)
| fix_e_wf: forall i (es:efnlst) k,
    k < efnlst_length es ->
    efnlst_wf (efnlst_length es + i) es ->
    exp_wf i (Fix_e es k)
(* Fix?: Axiom applied to anything should reduce to Axiom *)
| prf_e_wf : forall i, exp_wf i Prf_e
| prim_e_wf : forall i p, exp_wf i (Prim_val_e p)
with exps_wf: N -> exps -> Prop :=
| enil_wf: forall i, exps_wf i enil
| econs_wf: forall i e es,
    exp_wf i e -> exps_wf i es -> exps_wf i (econs e es)
with efnlst_wf: N -> efnlst -> Prop :=
| flnil_wf_e: forall i, efnlst_wf i eflnil
| flcons_wf_e: forall i f e es,    
    exp_wf i e -> isLambda e -> efnlst_wf i es ->
    efnlst_wf i (eflcons f e es)
with branches_wf: N -> branches_e -> Prop :=
| brnil_wf: forall i, branches_wf i brnil_e
| brcons_wf: forall i d n e bs,
    exp_wf (nargs n + i) e -> branches_wf i bs ->
    branches_wf i (brcons_e d n e bs).
#[export] Hint Constructors exp_wf exps_wf branches_wf : core.
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
  apply H. lia.
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

#[export] Hint Resolve weaken_closed weaken_closeds weaken_branches : core.

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
    | eflcons f e es => eflcons f (shift n k e) (shift_efnlst n k es)
    end.
  Fixpoint shift_branches' n k bs :=
    match bs with
    | brnil_e => brnil_e
    | brcons_e d na e brs => brcons_e d na (shift n (k+nargs na) e)
                                     (shift_branches' n k brs)
    end.
End SHIFT.

Fixpoint shift n k e := 
  match e with
    | Var_e i => Var_e (if lt_dec i k then i else i + n)
    | App_e e1 e2 => App_e (shift n k e1) (shift n k e2)
    | Lam_e na e' => Lam_e na (shift n (1 + k) e')
    | Con_e d es => Con_e d (shift_exps' shift n k es)
    | Let_e na e1 e2 => Let_e na (shift n k e1) (shift n (1 + k) e2)
    | Match_e e p bs => Match_e (shift n k e) p (shift_branches' shift n k bs)
    | Fix_e es k' => Fix_e (shift_efnlst shift n (efnlst_length es + k) es) k'
    | Prf_e => Prf_e
    | Prim_val_e p => Prim_val_e p
    | Prim_e p => Prim_e p
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
  try (solve[apply f_equal2; try rewrite H; try rewrite H0; reflexivity]);
  try (solve[apply f_equal3; try rewrite H; try rewrite H0; try rewrite H1;
             reflexivity]).
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
*)
(* optimised *)

(** Substitute [v] for variable [k] in [e];
*** with shifting *)
Function subst (v:exp) k (e:exp): exp :=
  match e with
    | Var_e i => if lt_dec i k then Var_e i
                 else if eq_dec i k then shift k 0 v else Var_e (i - 1)
    | App_e e1 e2 => App_e (subst v k e1) (subst v k e2)
    | Lam_e na e' => Lam_e na (subst v (1 + k) e')
    | Con_e d es => Con_e d (substs v k es)
    | Let_e na e1 e2 => Let_e na (subst v k e1) (subst v (1 + k) e2)
    | Match_e e p bs => Match_e (subst v k e) p (subst_branches v k bs)
    | Fix_e es k' => Fix_e (subst_efnlst v (efnlst_length es + k) es) k'
    | Prf_e => Prf_e
    | Prim_val_e p => Prim_val_e p
    | Prim_e p => Prim_e p
  end
with substs (v:exp) k (es:exps) : exps :=
       match es with
         | enil => enil
         | econs f fs => econs (subst v k f) (substs v k fs)
       end
with subst_efnlst (v:exp) k (es:efnlst) : efnlst :=
       match es with
         | eflnil => eflnil
         | eflcons fna f fs => eflcons fna (subst v k f) (subst_efnlst v k fs)
       end
with subst_branches (v:exp) k (bs:branches_e) : branches_e :=
       match bs with
         | brnil_e => brnil_e
         | brcons_e d n e bs =>
           brcons_e d n (subst v (nargs n+k) e) (subst_branches v k bs)
       end.

(** Substitute [v] for variable [k] in [e];
*** no shifting, only for evaluation of closed expressions. *)
Function sbst (v:exp) k (e:exp): exp :=
  match e with
    | Var_e i => if lt_dec i k then Var_e i
                 else if eq_dec i k then v else Var_e (i - 1)
    | App_e e1 e2 => App_e (sbst v k e1) (sbst v k e2)
    | Lam_e na e' => Lam_e na (sbst v (1 + k) e')
    | Con_e d es => Con_e d (sbsts v k es)
    | Let_e na e1 e2 => Let_e na (sbst v k e1) (sbst v (1 + k) e2)
    | Match_e e p bs => Match_e (sbst v k e) p (sbst_branches v k bs)
    | Fix_e es k' => Fix_e (sbst_efnlst v (efnlst_length es + k) es) k'
    | Prf_e => Prf_e
    | Prim_val_e p => Prim_val_e p
    | Prim_e p => Prim_e p
  end
with sbsts (v:exp) k (es:exps) : exps :=
       match es with
         | enil => enil
         | econs f fs => econs (sbst v k f) (sbsts v k fs)
       end
with sbst_efnlst (v:exp) k (es:efnlst) : efnlst :=
       match es with
         | eflnil => eflnil
         | eflcons fna f fs => eflcons fna (sbst v k f) (sbst_efnlst v k fs)
       end
with sbst_branches (v:exp) k (bs:branches_e) : branches_e :=
       match bs with
         | brnil_e => brnil_e
         | brcons_e d n e bs =>
           brcons_e d n (sbst v (nargs n+k) e) (sbst_branches v k bs)
       end.

(** Notation for optimised substitution. **)
Class Substitute (v:Type) (t:Type) := { substitute: v -> N -> t -> t }.
Notation "M { j := N }" := (substitute N j M)
                      (at level 10, right associativity).
#[export] Instance ExpSubstitute: Substitute exp exp :=
  { substitute := subst}.
#[export] Instance ExpsSubstitute: Substitute exp exps :=
  { substitute := substs}.
#[export] Instance BranchSubstitute: Substitute exp _ :=
  { substitute := subst_efnlst}.
#[export] Instance BranchesSubstitute: Substitute exp _ := 
  { substitute := subst_branches}.

(** Notation for unoptimised substitution. *)
Class Sbstitute (v:Type) (t:Type) := { sbstitute: v -> N -> t -> t }.
Notation "M { j ::= N }" := (sbstitute N j M)
                      (at level 10, right associativity).
#[export] Instance ExpSbstitute: Sbstitute exp exp :=
  { sbstitute := sbst}.
#[export] Instance ExpsSbstitute: Sbstitute exp exps :=
  { sbstitute := sbsts}.
#[export] Instance EfnlstSbstitute: Sbstitute exp efnlst :=
  { sbstitute := sbst_efnlst}.
#[export] Instance BranchesSbstitute: Sbstitute exp branches_e := 
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

   They are used to formalize the LambdaBoxMut to LambdaBoxLocal translation. *)

Lemma efnlst_length_shift v k es :
  efnlst_length (shift_fns v k es) = efnlst_length es.
Proof. induction es; simpl; try rewrite_hyps; trivial. Qed.

Lemma efnlst_length_sbst v k es :
  efnlst_length (sbst_efnlst v k es) = efnlst_length es.
Proof. induction es; simpl; try rewrite_hyps; trivial. Qed.

Lemma efnlst_length_subst v k es :
  efnlst_length (subst_efnlst v k es) = efnlst_length es.
Proof. induction es; simpl; try rewrite_hyps; trivial. Qed.

#[export] Hint Rewrite efnlst_length_shift efnlst_length_subst efnlst_length_sbst : core.

Lemma shift_twice:
  forall N i j m n, i <= j -> j <= i + m ->
 shift n j (shift m i N) = shift (m + n) i N.
Proof.
  assert ((forall N i j m n, i <= j -> j <= i + m ->
 shift n j (shift m i N) = shift (m + n) i N) /\
          (forall Ns i j m n, i <= j -> j <= i + m ->
                              shifts n j (shifts m i Ns) = shifts (m + n) i Ns) /\
          (forall Ns i j m n, i <= j -> j <= i + m ->
                                    shift_fns n j (shift_fns m i Ns) =
                                    shift_fns (m + n) i Ns) /\
          (forall Ns i j m n, i <= j -> j <= i + m ->
                           shift_branches n j (shift_branches m i Ns) =
                           shift_branches (m + n) i Ns)).
  apply my_exp_ind; intros; simpl; auto ;
  try (rewrite H; auto; try lia; rewrite H0; auto; autorewrite with core; try lia; auto).
  repeat if_split. apply f_equal. lia.
  f_equal.
  rewrite H; auto; autorewrite with core; try lia. 
  tauto.
Qed.

Lemma shift_subst :
  forall N i k j L, k <= j ->
 shift i k (N{j := L}) = (shift i k N){j+i := L}.
Proof.
  assert ((forall N i k j L, k <= j ->
 shift i k (N{j := L}) = (shift i k N){j+i := L}) /\
          (forall Ns i k j L, k <= j ->
                              shifts i k (Ns{j := L}) = (shifts i k Ns){j+i := L}) /\
          (forall Ns i k j L, k <= j ->
                         shift_fns i k (Ns{j := L}) = (shift_fns i k Ns){j+i := L}) /\
          (forall Ns i k j L, k <= j ->
                         shift_branches i k (Ns{j := L}) =
                         (shift_branches i k Ns){j+i := L})).
  apply my_exp_ind; intros; simpl; auto ;
  try (rewrite H; auto; autorewrite with core; rewrite H0; auto; try lia).
  repeat if_split. destruct (lt_dec j k); try lia.
  rewrite shift_twice; auto; lia.
  destruct (lt_dec n k); try lia; auto. apply f_equal. lia.
  apply f_equal. rewrite H; simpl; f_equal; try lia.
  simpl; repeat (f_equal; try lia). 
  repeat (f_equal; try lia).
  simpl in H. unfold shift_fns in H. rewrite H.
  repeat (f_equal; autorewrite with core; try lia; auto).
  repeat (f_equal; autorewrite with core; try lia; auto).
  repeat (f_equal; autorewrite with core; simpl; try lia; auto).
  rewrite H. simpl. f_equal; lia. lia.
  tauto.
Qed.

Lemma shift_away_subst :
  forall (L:exp) k i j (P:exp), k <= i -> i < k + (j + 1) ->
                    (shift (1 + j) k L){i := P} = shift j k L.
Proof.
  assert ((forall (L:exp) k i j (P:exp), k <= i -> i < k + (j + 1) ->
                                         (shift (1 + j) k L){i := P} = shift j k L) /\
          (forall (Ls:exps) k i j (P:exp), k <= i -> i < k + (j + 1) ->
                                           (shifts (1 + j) k Ls){i := P} = shifts j k Ls) /\
  (forall Ls k i j (P:exp), k <= i -> i < k + (j + 1) ->
                       (shift_fns (1 + j) k Ls){i := P} = shift_fns j k Ls) /\
  (forall Ls k i j (P:exp), k <= i -> i < k + (j + 1) ->
                       (shift_branches (1 + j) k Ls){i := P} = shift_branches j k Ls)).
  apply my_exp_ind; simpl; intros; auto ;
  try (rewrite H; auto; try lia; try rewrite H0; autorewrite with core; auto); try lia.
  repeat if_split. replace (n + (1 + j) - 1) with (n + j); auto; lia.
  tauto.
Qed.

(** According to Berghofer and Urban, this is a critical property of
    substitution, though we don't use it here. 
**)
Lemma substitution :
  forall (M N L:exp) i j, i <= j ->
    M{i := N}{j := L} = M{1+j := L}{i := N{ j-i := L}}.
Proof.
  assert ((forall (M:exp) N L i j, i <= j -> M{i := N}{j := L} = M{1+j := L}{i := N{ j-i := L}}) /\ (forall (Ms:exps) N L i j, i <= j -> Ms{i := N}{j := L} = Ms{1+j := L}{i := N{ j-i := L}}) /\
   (forall (Ms:efnlst) N L i j, i <= j -> Ms{i := N}{j := L} = Ms{1+j := L}{i := N{ j-i := L}}) /\
   (forall (Ms:branches_e) N L i j, i <= j -> Ms{i := N}{j := L} = Ms{1+j := L}{i := N{ j-i := L}})).
  apply my_exp_ind; intros; simpl in *; auto ;
  try (rewrite H; auto; try rewrite H0; autorewrite with core; auto; try lia).
  repeat if_split.
  assert (0 <= j - i) by lia.
  generalize (shift_subst N i 0 (j - i) L H0). intros.
  unfold substitute in H1. simpl in H1.
  rewrite H1. replace (j - i + i) with j; auto. lia.
  destruct (eq_dec n 0). lia.
  generalize (shift_away_subst L 0 i (n - 1)). intro.
  unfold substitute in H0. simpl in H0.
  specialize (H0 (subst L (n - 1 - i) N)). rewrite H0; auto. lia. lia.
  apply f_equal. replace (1 + j - (1 + i)) with (j - i). auto. lia. 
  apply f_equal. replace (1 + j - (1 + i)) with (j - i). auto. lia.
  f_equal. repeat (f_equal; try lia).
  repeat (f_equal; try lia).
  tauto.
Qed.

Fixpoint sbst_list (e:exp) (vs:exps): exp :=
  match vs with
    | enil => e
    | econs v vs => (sbst_list e vs){0::=v}
  end.

(** Find a branch in a match expression corresponding to a given constructor
    and arity. *)
Fixpoint find_branch (d:dcon) (m:N) (bs:branches_e) : option exp :=
  match bs with
    | brnil_e => None
    | brcons_e d' n e bs =>
      if eq_dec d d' then (if eq_dec (nargs n) m then Some e else None)
                     else find_branch d m bs
  end.

Fixpoint efnlength (es:efnlst) :=
  match es with
  | eflnil => 0%nat
  | eflcons _ _ l => S (efnlength l)
  end.

(** Skipping parameters *)
Fixpoint exps_skipn (n : N) (e : exps) : exps :=
  match n with
  | 0%N => e
  | _ =>
    match e with
    | enil => e
    | econs _ e' => exps_skipn (N.pred n) e'
    end
  end.

(** Building a Fixpoint substitution. **)
Definition sbst_fix (es:efnlst) (e : exp) : exp :=
  let les := efnlength es in
    fold_left
      (fun e ndx => e{0 ::= Fix_e es (N.of_nat ndx)})
      (list_to_zero les) e.

(** Big-step evaluation for [exp]. *)
Inductive eval: exp -> exp -> Prop :=
| eval_Lam_e: forall na e, eval (Lam_e na e) (Lam_e na e)
| eval_App_e: forall e1 na e1' e2 v2 v,
    eval e1 (Lam_e na e1') ->
    eval e2 v2 ->
    eval (e1'{0 ::= v2}) v -> 
    eval (App_e e1 e2) v
| eval_Con_e: forall d es vs,
    evals es vs ->
    eval (Con_e d es) (Con_e d vs)
| eval_Let_e: forall na e1 v1 e2 v2,
    eval e1 v1 ->
    eval (e2{0::=v1}) v2 ->
    eval (Let_e na e1 e2) v2
| eval_Match_e: forall e p bs d vs e' v,
    eval e (Con_e d vs) ->
    find_branch d (exps_length vs) bs = Some e' ->
    eval (sbst_list e' vs) v ->
    eval (Match_e e p bs) v
| eval_Fix_e: forall es k, eval (Fix_e es k) (Fix_e es k)
| eval_FixApp_e: forall e (es:efnlst) n e2 v2 e' e'',
    eval e (Fix_e es n) ->
    eval e2 v2 ->
    enthopt (N.to_nat n) es = Some e' ->
    eval (App_e (sbst_fix es e') v2) e'' ->
    eval (App_e e e2) e''
| eval_ProofApp_e : forall f a a',
    eval f Prf_e ->
    eval a a' ->
    eval (App_e f a) Prf_e
| eval_Prf_e : eval Prf_e Prf_e
| eval_Prim_val_e p : eval (Prim_val_e p) (Prim_val_e p)
with evals: exps -> exps -> Prop :=
     | evals_nil: evals enil enil
     | evals_cons: forall e es v vs,
         eval e v ->
         evals es vs ->
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
    * assert (j0:Lam_e na e1' = Lam_e na0 e1'0).
      { apply H. assumption. }
      injection j0; intros h0 h1. subst.
      assert (j1:v2 = v0). { apply H0. assumption. } subst.
      apply H1. assumption.
    * specialize (H _ H5); discriminate.
    * specialize (H _ H5); discriminate.
  - inversion H0. subst. apply f_equal2. reflexivity.
    apply H. assumption.
  - inversion H1. subst.
    assert (j0:v1 = v0). { apply H. assumption. }
    subst. apply H0. assumption.
  - inversion H1. subst.
    specialize (H _ H5). injection H; intros h0 h1. subst. clear H.
    rewrite H7 in e1. injection e1; intros h2. subst. clear e1.
    apply H0. assumption.
  - inversion H. subst. reflexivity.
  - inversion H2; subst.
    * specialize (H _ H5); discriminate.
    * specialize (H _ H5); injection H; intros; subst.
      specialize (H0 _ H6); subst v0.
      assert (e' = e'0) by congruence; subst e'0.
      now apply H1.
    * specialize (H _ H5); discriminate.
  - inversion H1; subst.
    * specialize (H _ H4); discriminate.
    * specialize (H _ H4); discriminate.
    * reflexivity.
  - inversion H. reflexivity.
  - inversion H. reflexivity.
  - inversion H. reflexivity.
  - inversion H1. subst. rewrite (H v0); try assumption.
    rewrite (H0 vs0); try assumption. reflexivity.
Qed.

Declare Scope name.
Bind Scope name with name.
Delimit Scope name with name.
Arguments nNamed i%_bs.
Definition nNameds (s : string) : name := nNamed s.

Notation " [: x ] " := (cons (nNameds x) nil) : name.
Notation " '[:' x , y , .. , z ] " :=
  (cons (nNameds x) (cons (nNameds y) .. (cons (nNameds z) nil) ..)) : name.
Local Open Scope name.

Coercion nNameds : string >-> name.
Arguments Lam_e n%_bs _.
Arguments eflcons n%_bs _ _.

Example x1: exp := Lam_e "x" (Var_e 0).  (* identity *)
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
               | Lam_e na d => Some (Lam_e na d)
               | Fix_e es k => Some (Fix_e es k)
               | Prf_e => Some Prf_e
               | Con_e d es => 
                 match evals_n n es with
                     | None => None
                     | Some vs => Some (Con_e d vs)
                 end
               | App_e e1 e2 =>
                 match eval_n n e1 with
                   | Some (Lam_e _ e1') => 
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
                   | Some Prf_e =>
                     match eval_n n e2 with
                     | None => None
                     | Some _ => Some Prf_e
                     end
                   | _ => None
                  end
               | Let_e _ e1 e2 =>
                 match eval_n n e1 with
                   | None => None
                   | Some v1 => eval_n n (e2{0::=v1})
                 end
               | Match_e e p bs =>
                 match eval_n n e with
                 | Some (Con_e d vs) =>
                   match find_branch d (exps_length vs) bs with
                     | None => None
                     | Some e' => eval_n n (sbst_list e' vs)
                   end
                   | _ => None
                 end
               | Prim_val_e p => Some (Prim_val_e p)
               | Var_e e => None
               | Prim_e p => None                                                   
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
  + injection H. intros <-; constructor.
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
  + subst.
    injection H1. intros <-. specialize (H _ e4). eapply eval_ProofApp_e; eauto.
  + econstructor.
    * specialize (H _ e4). eapply H.
    * specialize (H0 _ H1). apply H0.
  + econstructor; eauto. 
  + injection H; intros; subst. constructor.
  + injection H; intros h0. subst. constructor.
  + injection H1; intros h0. subst. constructor.
    * apply H. assumption.
    * apply H0. assumption.
Qed.
(* Print Assumptions evaln_eval. *)

(** [eval_n] is complete w.r.t. [eval] **)
Lemma eval_n_Some_Succ:
  forall e (n:nat) v, eval_n n e = Some v -> n = (S (n - 1))%nat.
Proof.
  induction n; intros.
  - simpl in H. discriminate.
  - lia.
Qed.
Lemma evals_n_Some_Succ:
  forall es (n:nat) vs, evals_n n es = Some vs -> n = (S (n - 1))%nat.
Proof.
  induction n; intros.
  - simpl in H. discriminate.
  - lia.
Qed.

Open Scope nat_scope.
Lemma pre_eval_evaln:
  (forall (e v:exp),
      eval e v -> exists (n:nat),
        forall m, m >= n -> eval_n (S m) e = Some v) /\
  (forall (es vs:exps),
      evals es vs -> exists (n:nat),
        forall m, m >= n -> evals_n (S m) es = Some vs).
Proof.
  assert (j:forall m, m > 0 -> m = S (m - 1)).
  { induction m; intuition auto with arith. }
  apply my_eval_ind; intros; try (exists 0; intros mx h; reflexivity).
  - destruct H, H0, H1. exists (S (max x (max x0 x3))). intros m h.
    assert (j1:= max_fst x (max x0 x3)). 
    assert (lx: m > x). lia.
    assert (j2:= max_snd x (max x0 x3)).
    assert (j3:= max_fst x0 x3).
    assert (lx0: m > x0). lia.
    assert (j4:= max_snd x0 x3).
    assert (j5:= max_fst x0 x3).
    assert (lx1: m > x3). lia.
    simpl. rewrite (j m); try lia. rewrite H; try lia.
    rewrite H0; try lia. rewrite H1; try lia. reflexivity.
  - destruct H. exists (S x). intros m hm. simpl. rewrite (j m); try lia.
    rewrite H; try lia. reflexivity.
  - destruct H, H0. exists (S (max x x0)). intros mx h.
    assert (l1:= max_fst x x0). assert (l2:= max_snd x x0).
    simpl. rewrite (j mx); try lia. rewrite H; try lia.
    rewrite H0; try lia. reflexivity.
  - destruct H, H0. exists (S (max x x0)). intros mx h.
    assert (l1:= max_fst x x0). assert (l2:= max_snd x x0).
    simpl. rewrite (j mx); try lia. rewrite H; try lia.
    rewrite e1. rewrite H0; try lia. reflexivity.
  - destruct H, H0, H1. exists (S (max x (max x0 x3))). intros m h.
    assert (j1:= max_fst x (max x0 x3)). 
    assert (lx: m > x). lia.
    assert (j2:= max_snd x (max x0 x3)).
    assert (j3:= max_fst x0 x3).
    assert (lx0: m > x0). lia.
    assert (j4:= max_snd x0 x3).
    assert (j5:= max_fst x0 x3).
    assert (lx1: m > x3). lia.
    simpl. rewrite (j m); try lia. rewrite H; try lia.
    rewrite H0; try lia. rewrite e3. apply H1. try lia.
  - destruct H, H0. exists (S (max x x0)). intros mx h.
    assert (l1:= max_fst x x0). assert (l2:= max_snd x x0).
    simpl. rewrite (j mx); try lia. rewrite H; try lia.
    rewrite H0; try lia. reflexivity.
  - destruct H, H0. exists (S (max x x0)). intros mx h.
    assert (l1:= max_fst x x0). assert (l2:= max_snd x x0).
    simpl. rewrite (j mx); try lia. rewrite H; try lia.
    rewrite H0; try lia. reflexivity.
Qed.

Lemma eval_evaln:
  forall t s,
    eval t s -> exists n, forall m, m >= n -> eval_n m t = Some s.
Proof.
  intros t s h.
  destruct (proj1 pre_eval_evaln _ _ h).
  exists (S x). intros m hm. specialize (H (m - 1)).
  assert (k: m = S (m - 1)). { lia. }
  rewrite k. apply H. lia.
Qed.
(* Print Assumptions eval_evaln. *)
  
Lemma eval_n_up:
 forall t s tmr,
   eval_n tmr t = Some s -> exists n, forall m, m >= n -> eval_n m t = Some s.
Proof.
  intros.
  (* Check (eval_evaln _ _ (proj1 (evaln_eval tmr) _ _ H)). *)
  destruct (eval_evaln _ _ (proj1 (evaln_eval tmr) _ _ H)).
  exists x. apply H0.
Qed.

(** some concrete examples **)
Open Scope N_scope.
Example Ke: exp := Lam_e "x" (Lam_e "y" (Var_e 1)).
Example Se: exp := Lam_e "x" (Lam_e "y" (Lam_e "z"
            (App_e (App_e (Var_e 2) (Var_e 0)) (App_e (Var_e 1) (Var_e 0))))).
Example SKKe: exp := App_e (App_e Se Ke) Ke.
Definition index := mkInd (kername_of_string "someind") 0.
Definition conex := (index, 10).

(* Eval vm_compute in (eval_n 1000 (App_e SKKe (Con_e conex enil))). *)
Goal eval (App_e SKKe (Con_e conex enil)) (Con_e conex enil).
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

(* (** natural numbers in Church representation **) *)
(* Section ChurchNaturals. *)
(* Notation ZZ := (Lam_e "x" (Lam_e "y" Ve1)). *)
(* Notation SS := (Lam_e "x" (Lam_e "y" (Lam_e "z" (Ve0 $ (Ve2 $ Ve1 $ Ve0))))). *)
(* Notation one := (SS $ ZZ). *)
(* Notation two := (SS $ one). *)
(* Notation three := (SS $ two). *)
(* Notation four := (SS $ three). *)
(* Notation five := (SS $ four). *)
(* Notation six := (SS $ five). *)
(* Notation add := (Lam_e "x" (Lam_e "y" (Ve1 $ Ve0 $ SS))). *)
(* Notation mul := (Lam_e "x" (Lam_e "y" (Ve1 $ ZZ $ (add $ Ve0)))). *)

(* Example One := Eval compute in (unsome (eval_n 100 one)). *)
(* Example Two := Eval compute in (unsome (eval_n 100 two)). *)
(* Example Three := Eval vm_compute in (unsome (eval_n 100 three)). *)
(* Example Four := Eval vm_compute in (unsome (eval_n 100 four)). *)
(* Example Five := Eval vm_compute in (unsome (eval_n 100 five)). *)
(* Example Six := Eval vm_compute in (unsome (eval_n 100 six)). *)

(* Goal eval (SS $ ZZ) One. repeat econstructor. Qed. *)
(* Goal eval (add $ ZZ $ one) One. repeat econstructor. Qed. *)
(* Goal eval (add $ one $ ZZ) One. repeat econstructor. Qed. *)
(* Goal (eval_n 1000 (add $ two $ one)) = Some Three. *)
(* vm_compute. reflexivity. Qed. *)
(* Goal (eval_n 1000 (add $ two $ three)) = Some Five. *)
(* vm_compute. reflexivity. Qed. *)
(* Goal (eval_n 1000 (mul $ two $ three)) = Some Six. *)
(* vm_compute. reflexivity. Qed. *)
(* End ChurchNaturals. *)

(** booleans using native data constructors (with no arguments) **)
Notation boolind := (mkInd (kername_of_string "bool") 0).

Notation TT := ((boolind, 0):dcon).
Notation TTT := (Con_e TT enil).
Notation FF := ((boolind, 1):dcon).
Notation FFF := (Con_e FF enil).
(* if b then e1 else e2 *)
Import ListNotations.
Notation ite :=
  (Lam_e "x" (Lam_e "y" (Lam_e "z"
             (Match_e Ve2 0 (brcons_e TT (0,[]) Ve1 (brcons_e FF (0,[]) Ve0 brnil_e)))))).
             
Goal eval (ite $ TTT $ FFF $ TTT) FFF.
  repeat econstructor. Qed.
Goal eval (ite $ FFF $ FFF $ TTT) TTT.
repeat econstructor. Qed.


(** lists using native data constructors: Cons takes 2 arguments **)
Notation listind := (mkInd (kername_of_string "list") 0).
Notation dNil := ((listind,0):dcon).
Notation Nil := (Con_e dNil enil).
Notation dCons := ((listind,1):dcon).
Notation Cons := (Lam_e "x" (Lam_e "y" (Con_e dCons (econs Ve1 [|Ve0|])))).
Notation cdr :=
  (Lam_e "x" (Match_e Ve0 0 (brcons_e dNil (0,[]) Nil
   (brcons_e dCons (2,[: "x", "xs" ]) Ve0 brnil_e)))).

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
Notation natind := (mkInd (kername_of_string "nat") 0).
Notation ZZ := ((natind,0):dcon).
Notation ZZZ := (Con_e ZZ enil).
Notation SS := ((natind,1):dcon).
Notation SSS := (Lam_e "x" (Con_e SS [|Ve0|])).
Notation one := (SSS $ ZZZ).
Notation two := (SSS $ one).
Notation three := (SSS $ two).
Notation four := (SSS $ three).
Notation five := (SSS $ four).
Notation six := (SSS $ five).

(* Example One := Eval compute in (unsome (eval_n 1000 one)). *)
(* Example Two := Eval compute in (unsome (eval_n 100 two)). *)
(* Example Three := Eval vm_compute in (unsome (eval_n 100 three)). *)
(* Example Four := Eval vm_compute in (unsome (eval_n 100 four)). *)
(* Example Five := Eval vm_compute in (unsome (eval_n 100 five)). *)
(* Example Six := Eval vm_compute in (unsome (eval_n 100 six)). *)

(* Goal eval (SSS $ one) Two. *)
(* repeat econstructor.  *)
(* Qed. *)

(* Goal eval (SSS $ three) Four. *)
(* repeat econstructor.  *)
(* Qed. *)

(** fixpoints **)
Definition copy : exp :=
  (Fix_e [!"copy" := Lam_e "x" (Match_e Ve0 0 (brcons_e ZZ (0,[]) ZZZ 
            (brcons_e SS (1, [: "n"]) (SSS $ ((Var_e 2) $ Ve0)) brnil_e)))!] 0).

Goal eval (copy $ ZZZ) ZZZ.
unfold copy.
econstructor 7 ; try vm_compute; try constructor. econstructor.
unfold sbst_fix.
repeat (try econstructor ; try vm_compute).
Qed.

(* Eval vm_compute in eval_n 100 (copy $ six). *)


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
*)

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
  - constructor; auto. simpl.
    rewrite efnlst_length_sbst. eassumption. 
    rewrite efnlst_length_sbst. apply H; try lia; auto.
  - constructor; auto. 
  - constructor; auto.
    + destruct e; simpl in i0; try contradiction. exact I.
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
  replace (1 + exps_length vs + i) with (exps_length vs + (1 + i)) in H0;
    try lia.
  apply sbst_preserves_exp_wf; auto.
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
#[export] Hint Resolve sbst_preserves_exp_wf sbst_preserves_exps_wf 
     sbst_preserves_branches_wf : core.

Lemma nthopt_preserves_wf :
  forall i es, efnlst_wf i es ->
               forall n e, enthopt n es = Some e -> exp_wf i e.
Proof.
  induction es; simpl; intros. 
  - destruct n; discriminate.
  - inversion H; subst. destruct n0; simpl in *.
    + injection H0; intros; subst; auto. 
    + specialize (IHes H7 n0 e0).
      apply IHes. auto.
Qed.

Lemma efnlength_efnlst_length es :
  N.of_nat (efnlength es) = efnlst_length es.
Proof.
  induction es; simpl; lia.
Qed.

Lemma sbst_fix_preserves_wf :
  forall es, efnlst_wf (efnlst_length es) es ->
        forall e, exp_wf (efnlst_length es) e ->
                  exp_wf 0 (sbst_fix es e).
Proof.
  intros.
  unfold sbst_fix.
  revert e H0.
  remember (Fix_e es) as fixe.
  intros.
  assert (Heq : N.of_nat (efnlength es) <= efnlst_length es).
  { rewrite efnlength_efnlst_length. lia. }
        
  revert Heq H0. generalize es at 1 3 4 as es'.
  intros es'.
  remember (list_to_zero (N.to_nat (efnlst_length es'))).
  revert es' Heql e.
  induction l. simpl; intros.
  destruct es'; simpl in *; auto. simpl in *.
  rewrite Nnat.N2Nat.inj_add in *. discriminate.
  intros.
  destruct es'; simpl in *; auto; try discriminate.
  rewrite Nnat.N2Nat.inj_add in *. 
  injection Heql. intros. specialize (IHl _ H1).
  apply IHl. simpl in *. lia. eapply sbst_preserves_exp_wf. eauto.
  subst fixe. constructor. simpl in *. subst. lia. 
  now rewrite N.add_0_r.
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
Local Hint Resolve find_branch_preserves_wf : core.

Lemma exps_skipn_preserves_wf k p vs :
  exps_wf k vs -> exps_wf k (exps_skipn p vs).
Proof.
  revert p; induction vs; intros; simpl.
  - now destruct p.
  - destruct p; trivial.
    apply IHvs. now inv H.
Qed.
Local Hint Resolve exps_skipn_preserves_wf : core.

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
  - inversion H2; subst. 
    specialize (H0 H7). specialize (H H6).
    inversion H. subst.
    apply H1.
    assert (wfe':=nthopt_preserves_wf _ _ H9 _ _ e3).
    rewrite N.add_0_r in *.
    constructor.
    now eapply sbst_fix_preserves_wf.
    eauto.
  - inversion H1; subst. constructor; auto.
Qed.
Definition eval_preserves_wf := proj1 eval_preserves_wf'.
Definition evals_preserves_wf := proj2 eval_preserves_wf'.

(** Characterize values **)
Inductive is_value: exp -> Prop :=
| var_is_value: forall i, is_value (Var_e i)
| lam_is_value: forall na e, is_value (Lam_e na e)
| con_is_value: forall d es, are_values es -> is_value (Con_e d es)
| fix_is_value: forall es k, is_value (Fix_e es k)
| prf_is_value: is_value Prf_e
| prim_is_value p : is_value (Prim_val_e p)
(* | prim_is_value: forall p, is_value (Prim_e p) *)
with are_values: exps -> Prop :=
| enil_are_values: are_values enil
| econs_are_values: forall e es, is_value e -> are_values es ->
                                 are_values (econs e es).
Scheme is_value_ind2 := Induction for is_value Sort Prop
with are_values_ind2 := Induction for are_values Sort Prop.
Combined Scheme my_is_value_ind from is_value_ind2, are_values_ind2.
#[export] Hint Constructors is_value are_values : core.

(** Show that evaluation always yields a value. *)
Lemma eval_yields_value' :
  (forall e v, eval e v -> is_value v) /\
  (forall es vs, evals es vs -> are_values vs).
Proof.
  apply my_eval_ind; simpl; intros; auto; try constructor; auto.
Qed.
Definition eval_yields_value := proj1 eval_yields_value'.
Definition evals_yields_values := proj2 eval_yields_value'.
#[export] Hint Resolve eval_yields_value evals_yields_values : core.

(** Computable test as to whether a source expression is already a
    value (a.k.a., atomic).  *)
Fixpoint is_valueb (e:exp): bool :=
  match e with
    | Var_e _ => true
    | Lam_e _ _ => true
    | App_e _ _  => false
    | Con_e _ es => are_valuesb es
    | Match_e _ _ _ => false
    | Let_e _ _ _ => false
    | Fix_e _ _ => true
    | Prf_e => true
    | Prim_val_e _ => true
    | Prim_e p => false (* arguable *)
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
  - inv H.   
  - destruct (is_valueb e); try discriminate. constructor.
    + apply H; auto.
    + apply H0; auto. 
  - inversion H1; subst. destruct (is_valueb e). 
    + tauto. 
    + apply H. auto.
Qed.
Definition is_valueb_corr := proj1 is_valueb_corr'.
Definition are_valuesb_corr := proj1 (proj2 is_valueb_corr').
#[export] Hint Rewrite is_valueb_corr : core.
#[export] Hint Rewrite are_valuesb_corr : core.
#[export] Hint Resolve is_valueb_corr : core.
#[export] Hint Resolve are_valuesb_corr : core.

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
#[export] Hint Resolve are_values_append : core.

Lemma exp_wf_shift :
  (forall i e, exp_wf i e -> forall j, shift j i e = e) /\
  (forall i es, exps_wf i es -> forall j, shifts j i es = es) /\
  (forall i es, efnlst_wf i es -> forall j, shift_fns j i es = es) /\
  (forall i bs, branches_wf i bs -> forall j, shift_branches j i bs = bs).
Proof.
  apply my_exp_wf_ind; simpl; intros; try rewrite_hyps; trivial.
  destruct lt_dec. reflexivity. contradiction.
  f_equal. now rewrite N.add_comm.
Qed.

Lemma closed_subst_sbst v :
  exp_wf 0 v ->
  (forall t k, sbst v k t = subst v k t) /\
  (forall es k, sbsts v k es = es{k := v}) /\
  (forall es k, sbst_efnlst v k es = es{k:=v}) /\
  (forall bs k, sbst_branches v k bs = bs{k:=v}).
Proof.
  intros Hv.
  apply my_exp_ind; simpl; intros; try rewrite_hyps; trivial.
  destruct lt_dec. reflexivity.
  destruct N.eq_dec. subst n.
  symmetry; now apply exp_wf_shift.
  reflexivity.
Qed.

(** Weakening with respect to [exp_wf]. *)
Lemma weaken_wf_le :
  (forall i e, exp_wf i e -> forall j, i <= j -> exp_wf j e) /\
  (forall i es, exps_wf i es -> forall j, i <= j -> exps_wf j es) /\
  (forall i es, efnlst_wf i es -> forall j, i <= j -> efnlst_wf j es) /\
  (forall i bs, branches_wf i bs -> forall j, i <= j -> branches_wf j bs).
Proof.  
  apply my_exp_wf_ind; intros; econstructor; auto; try lia; 
  match goal with
    | [ H: forall _, _ -> exp_wf _ ?e |- exp_wf _ ?e] => apply H; lia
    | _ => idtac
  end.
  apply H. lia.
Qed.

Lemma subst_preserves_wf' :
  (forall i' e, exp_wf i' e ->
     forall i, i' = 1 + i -> forall v, exp_wf 0 v ->
       forall k, k <= i -> exp_wf i (e{k:=v})) /\
  (forall i' es, exps_wf i' es ->
     forall i, i' = 1 + i -> forall v, exp_wf 0 v ->
       forall k, k <= i -> exps_wf i (es{k:=v})) /\
  (forall i' es, efnlst_wf i' es ->
     forall i, i' = 1 + i -> forall v, exp_wf 0 v ->
       forall k, k <= i -> efnlst_wf i (es{k:=v})) /\
  (forall i' bs, branches_wf i' bs ->
     forall i, i' = 1 + i -> forall v, exp_wf 0 v ->
       forall k, k <= i -> branches_wf i (bs{k:=v})).
Proof.
  apply my_exp_wf_ind; simpl; intros; subst; eauto.
  - repeat if_split; try (constructor; auto; lia).
    rewrite (proj1 exp_wf_shift _ _ H0).
    eapply (proj1 weaken_wf_le); eauto; lia.
  - constructor. apply H; try lia; auto.
  - constructor; auto. apply H0; try lia; auto.
  - constructor; auto.
    rewrite efnlst_length_subst. eassumption.
    rewrite efnlst_length_subst; apply H; try lia; auto.
  - constructor; auto. 
  - constructor; auto.
    + destruct e; contradiction || constructor.
  - constructor; auto. apply H; try lia; auto.
Qed.

Lemma value_value_subst n v :
  is_value v -> exp_wf 0 v ->
  (forall e, is_value e -> is_value (subst v n e)) /\
  (forall es, are_values es -> are_values (substs v n es)).
Proof.
  intros vv wfv.
  apply my_is_value_ind; simpl; intros; try constructor; trivial.
  intros.
  destruct lt_dec. constructor.
  destruct N.eq_dec. now rewrite (proj1 exp_wf_shift).
  constructor.
Qed.  

Lemma wf_value_self_eval :
  (forall v, is_value v -> exp_wf 0 v -> eval v v) /\
  (forall vs, are_values vs -> exps_wf 0 vs -> evals vs vs).
Proof.
  apply my_is_value_ind; simpl; intros; auto; try constructor; auto.
  inv H. lia.
  inv H0. auto.
  
  inv H1. intuition auto.
  inv H1. intuition auto.
Qed.

Lemma sbst_closed_id v :
  (forall k t, exp_wf k t -> forall j, k <= j -> sbst v j t = t) /\
  (forall k es, exps_wf k es -> forall j, k <= j -> es{j::=v} = es) /\
  (forall k es, efnlst_wf k es -> forall j, k <= j -> es{j::=v} = es) /\
  (forall k bs, branches_wf k bs -> forall j, k <= j -> bs{j::=v} = bs).
Proof.
  apply my_exp_wf_ind; simpl; intros; try solve [rewrite_hyps; auto; lia]; trivial.
  destruct (lt_dec j j0). reflexivity.
  destruct (N.eq_dec j j0). lia. lia.
Qed.

Lemma subst_closed_id v :
  (forall k t, exp_wf k t -> forall j, k <= j -> subst v j t = t) /\
  (forall k es, exps_wf k es -> forall j, k <= j -> es{j:=v} = es) /\
  (forall k es, efnlst_wf k es -> forall j, k <= j -> es{j:=v} = es) /\
  (forall k bs, branches_wf k bs -> forall j, k <= j -> bs{j:=v} = bs).
Proof.
  apply my_exp_wf_ind; simpl; intros; try solve [rewrite_hyps; auto; lia]; trivial.
  destruct (lt_dec j j0). reflexivity.
  destruct (N.eq_dec j j0). lia. lia.
Qed.


Lemma shift0 :
  (forall e, forall i, shift 0 i e = e) /\
  (forall es, forall i, shifts 0 i es = es) /\
  (forall es, forall i, shift_fns 0 i es = es) /\
  (forall bs, forall i, shift_branches 0 i bs = bs).
Proof.
  apply my_exp_ind; intros; try rewrite_hyps; simpl; try rewrite_hyps; trivial.
  destruct lt_dec. reflexivity. now rewrite N.add_0_r.
Qed.

Fixpoint exps_as_list (e:exps) : list exp :=
match e with
| enil => []
| econs h tl => h::(exps_as_list tl)
end.

Fixpoint exps_from_list (es: list exp) : exps :=
match es with
| [] => enil
| h::tl => econs h (exps_from_list tl)
end.

Fixpoint efnlst_as_list (e:efnlst) : list (name * exp) :=
match e with
| eflnil => []
| eflcons n e tl => (n,e)::(efnlst_as_list tl)
end.

Fixpoint efnlst_from_list (e: list (name * exp)) : efnlst :=
match e with
| [] => eflnil
| (n,e)::tl =>  eflcons n e (efnlst_from_list tl)
end.


Fixpoint branches_as_list (e:branches_e) : list (dcon * (N * list name) * exp) :=
match e with
| brnil_e => []
| brcons_e d ns e tl => (d,ns,e)::(branches_as_list tl)
end.

Fixpoint branches_from_list (e:list (dcon * (N * list name) * exp)) : branches_e :=
match e with
| [] => brnil_e
| (d,ns,e)::tl => brcons_e d ns e (branches_from_list tl)
end.


Definition sbst_real_list :exp -> (list exp) -> exp :=
fold_right  (fun v ee => ee{0 ::= v}).

Lemma sbst_list_real (le : exps) (e:exp):
  sbst_list e le = sbst_real_list e (exps_as_list le).
Proof using.
  induction le;[reflexivity | ].
  simpl. congruence.
Qed.

(* Eval compute in (list_to_zero 4). *)
(* Eval compute in (seq 0 4). *)


Lemma list_to_zero_rev n: list_to_zero n = rev (List.seq 0 n).
Proof.
  rewrite <- (rev_involutive (list_to_zero n )).
  f_equal.
  induction n; [reflexivity | ].
  simpl list_to_zero. simpl rev. rewrite IHn. clear IHn.
  replace (S n) with (n + 1)%nat by lia.
  (* rewrite seq_add. reflexivity. *)
Abort.

Lemma sbst_fix_real (e : exp) (es:efnlst):
  sbst_fix es e = 
    sbst_real_list 
      e 
      (map (fun ndx => Fix_e es (N.of_nat ndx)) (List.seq 0 (efnlength es))).
Proof using.
  (* unfold sbst_fix. rewrite list_to_zero_rev. *)
  (* rewrite <- fold_left_rev_right. *)
  (* unfold sbst_real_list. rewrite rev_involutive. *)
  (* f_equal. *)
  (* symmetry. *)
  (* apply fold_right_map. *)
Abort.

Open Scope Z_scope.
Function maxFree (e:exp): Z :=
  match e with
    | Var_e i => Z.of_N i
    | App_e e1 e2 => Z.max (maxFree e1) (maxFree e2)
    | Lam_e _ e' => maxFree e' -1
    | Con_e _ es => maxFreeC es
    | Let_e na a f => Z.max (maxFree a) (maxFree f - 1)
    | Match_e e p bs => Z.max (maxFree e) (maxFreeB bs)
    | Fix_e es k' => maxFreeF es - (Z.of_N (efnlst_length es))
    | Prf_e => -1
    | Prim_val_e _ => -1
    | Prim_e _ => -1
  end
with maxFreeC (es:exps) : Z :=
    match es with
    | enil => -1
    | econs f fs => Z.max (maxFree f) (maxFreeC fs)
    end
with maxFreeF (es:efnlst) : Z :=
    match es with
    | eflnil => -1
    | eflcons _ f fs => Z.max (maxFree f) (maxFreeF fs)
    end
with maxFreeB  (bs:branches_e) : Z :=
       match bs with
    | brnil_e => -1
    | brcons_e _ n b bs => Z.max (maxFree b - (Z.of_N (nargs n))) (maxFreeB bs)
       end.

Lemma exp_wf_maxFree: 
  (forall n (s : exp),
    exp_wf n s 
    -> maxFree s < Z.of_N n)
 /\
  (forall n (s : exps),
    exps_wf n s
    -> maxFreeC s < Z.of_N n)
 /\
  (forall n (s : efnlst),
    efnlst_wf n s 
    -> maxFreeF s < Z.of_N n)
 /\
  (forall n (s : branches_e),
    branches_wf n s 
    -> maxFreeB s < Z.of_N n).
Proof using.
  apply my_exp_wf_ind; intros; simpl in *; try lia.
Qed.


Close Scope Z_scope.

Definition fnames (e:efnlst) : list name :=
map fst (efnlst_as_list e).

(*

Zoe: Commenting the following out as they have dependencies to SquiggleEq.
     We should fix that if this code is still relevant.

(* the suffix s stands for "simpler".
 Unlike eval_n, this is not a mutual fixpoint.
 In the Con_e cases, we convert [exps] to [list exp] and use list functions.
 An advantage is that when evaluating constructor argument,
 the fuel stays constant, and does not need to be threaded through
 (as decrements) the arguments. *)
Function eval_ns (n:nat) (e:exp) {struct n}: option exp := 
  match n with
  | 0%nat => None
  | S n =>
    match e with
    | Lam_e na d => Some (Lam_e na d)
    | Fix_e es k => Some (Fix_e es k)
    | Prf_e => Some Prf_e
    | Con_e d es =>
      match ExtLibMisc.flatten (map (eval_ns n) (exps_as_list es)) with
      | None => None
      | Some vs => Some (Con_e d (exps_from_list vs))
      end
    | App_e e1 e2 =>
      match eval_ns n e1 with
      | Some (Lam_e _ e1') => 
        match eval_ns n e2 with
        | None => None
        | Some e2' => eval_ns n (e1'{0 ::= e2'})
        end
      | Some (Fix_e es k) =>
        match eval_ns n e2 with
        | None => None
        | Some e2' =>
          match enthopt (N.to_nat k) es with
          | Some e' =>
            let t' := sbst_fix es e' in
            eval_ns n (App_e t' e2')
          | _ => None
          end
        end
      | Some Prf_e => (* Some Prf_e *)
        match eval_ns n e2 with
        | None => None
        | Some e2' => Some Prf_e
        end                     
      | _ => None
      end
    | Let_e _ e1 e2 =>
      match eval_ns n e1 with
      | None => None
      | Some v1 => eval_ns n (e2{0::=v1})
      end
    | Match_e e p bs =>
      match eval_ns n e with
      | Some (Con_e d vs) =>
        match find_branch d (exps_length vs) bs with
        | None => None
        | Some e' => eval_ns n (sbst_list e' vs)
        end
      | _ => None
      end
    | Var_e e => None
    | Prim_e e => None
    end
  end.


Lemma eval_ns_Some_Succ:
  forall e (n:nat) v, eval_ns n e = Some v -> n = (S (n - 1))%nat.
Proof.
  induction n; intros.
  - simpl in H. discriminate.
  - lia.
Qed.


(* similar to eval_n_monotone *)
Lemma eval_ns_monotone:
  forall (n:nat) e f, eval_ns n e = Some f ->
                      forall (m:nat), eval_ns (n + m) e = Some f.
Admitted.


From CertiCoq Require Import CpdtTactics.
Lemma exps_as_list_from_list vs:
  exps_from_list (exps_as_list vs) = vs.
Proof using.
  induction vs; crush.
Qed.



(** [eval_n] is complete w.r.t. [eval] **)
Lemma eval_evalns:
  (forall (e v:exp), eval e v -> exists (n:nat), eval_ns n e = Some v) /\
  (forall (es vs:exps), evals es vs -> exists (n:nat), flatten (map (eval_ns n) (exps_as_list es))
                                          = Some (exps_as_list vs)).
Proof.
  apply my_eval_ind; intros; try (solve [exists 1%nat; reflexivity]).
  (* prove that if eval_ns becomes Some _, then n>0, similar to eval_n_Some_Succ
    then prove evan_ns_monotone*)
  - destruct H as [x h]. destruct H0 as [x0 h0]. destruct H1 as [x1 h1].
    exists (x+x0+x1)%nat. simpl in *.
    assert (j:=eval_ns_Some_Succ _ _ _ h).
    assert (j0:=eval_ns_Some_Succ _ _ _ h0).
    assert (j1:=eval_ns_Some_Succ _ _ _ h1).
    assert (k:= eval_ns_monotone _ _ _ h).
    assert (k0:= eval_ns_monotone _ _ _ h0).
    assert (k1:= eval_ns_monotone _ _ _ h1).
    rewrite j.
    replace (S (x - 1) + x0 + x1)%nat
    with (S (x + (x0 + x1 - 1)))%nat; try lia.
    simpl. rewrite k.
    replace (x + (x0 + x1 - 1))%nat with (x0 + (x + x1 - 1))%nat; try lia.
    rewrite k0.
    replace (x0 + (x + x1 - 1))%nat with (x1 + (x + x0 - 1))%nat; try lia.
    rewrite k1. reflexivity.
  - destruct H as [x h]. exists (x+1)%nat.
    simpl. rewrite Nat.add_comm. simpl.
    rewrite h. simpl.
    rewrite exps_as_list_from_list. reflexivity.
  - destruct H as [x h]. destruct H0 as [x0 h0].
    assert (j:=eval_ns_Some_Succ _ _ _ h).
    assert (j0:=eval_ns_Some_Succ _ _ _ h0).
    assert (k:= eval_ns_monotone _ _ _ h).
    assert (k0:= eval_ns_monotone _ _ _ h0).
    exists (x+x0)%nat.
    rewrite j.
    replace (S (x - 1) + x0)%nat with (S (x + (x0 - 1)))%nat; try lia.
    simpl. rewrite k.
    replace (x + (x0 - 1))%nat with (x0 + (x - 1))%nat; try lia.
    rewrite k0. reflexivity.
  - destruct H as [x h]. destruct H0 as [x0 h0].
    assert (j:=eval_ns_Some_Succ _ _ _ h).
    assert (j0:=eval_ns_Some_Succ _ _ _ h0).
    assert (k:= eval_ns_monotone _ _ _ h).
    assert (k0:= eval_ns_monotone _ _ _ h0).
    exists (x+x0)%nat.
    rewrite j.
    replace (S (x - 1) + x0)%nat with (S (x + (x0 - 1)))%nat; try lia.
    simpl. rewrite k.
    replace (x + (x0 - 1))%nat with (x0 + (x - 1))%nat; try lia.
    rewrite e1. rewrite k0. reflexivity.
  - destruct H as [x h]. destruct H0 as [x0 h0]. destruct H1 as [x1 h1].
    exists (x+x0+x1)%nat.
    assert (j:=eval_ns_Some_Succ _ _ _ h).
    assert (j0:=eval_ns_Some_Succ _ _ _ h0).
    assert (j1:=eval_ns_Some_Succ _ _ _ h1).
    assert (k:= eval_ns_monotone _ _ _ h).
    assert (k0:= eval_ns_monotone _ _ _ h0).
    assert (k1:= eval_ns_monotone _ _ _ h1).
    rewrite j.
    replace (S (x - 1) + x0 + x1)%nat
    with (S (x + (x0 + x1 - 1)))%nat; try lia.
    simpl. rewrite k.
    replace (x + (x0 + x1 - 1))%nat with (x0 + (x + x1 - 1))%nat; try lia.
    rewrite k0.
    replace (x0 + (x + x1 - 1))%nat with (x1 + (x + x0 - 1))%nat; try lia.
    rewrite e3, k1. reflexivity.
  - destruct H as [x h].
    destruct H0 as [x0 h0].
    assert (j:=eval_ns_Some_Succ _ _ _ h).
    assert (j0:=eval_ns_Some_Succ _ _ _ h0).
    assert (k:= eval_ns_monotone _ _ _ h).
    assert (k0:= eval_ns_monotone _ _ _ h0).
    exists (S (x+x0)%nat). simpl. rewrite k.
    rewrite Nat.add_comm. rewrite k0. reflexivity.
  - simpl. exrepnd. exists (n0+n)%nat.
    assert (k:= eval_ns_monotone _ _ _ H0). clear H0.
    rewrite k.
    erewrite <- flattenLift2;
      [ | | rewrite H1; firstorder];[rewrite H1; refl | ].
    intros.
    apply in_map with (f:= (eval_ns n))in H.
    apply isSomeIf in H1.
    eapply flattenSomeIn in H1; eauto.
    remember (eval_ns n b) as r.
    destruct r; [ | firstorder].
    symmetry.
    rewrite Nat.add_comm.
    apply  eval_ns_monotone.
    auto.
Qed.

*)

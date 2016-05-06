Require Import Arith BinNat String List Omega Ensembles.
Require Import CpdtTactics.
Require Import cps Ensembles_util.
Import ListNotations.
(* Require Maps. *)
(* Import Nnat. *)

(* useful definitions and proof for L6 - cps language *)
(* 
 SUBTERM - proper subterm relation

 OCCUR   - number of occurence of variables

 BINDING - list of variable bindings, unique binding property
 
 OTHER  - unclassified fact about cps/cps.v

 *)

Ltac destructAll :=
  match goal with
    | [ H : _ /\ _ |- _] => destruct H; destructAll
    | [ H : exists E, _ |- _ ] => destruct H; destructAll
    | _ => subst
  end.


Definition var_dec := M.elt_eq.

Inductive subterm_e: exp -> exp -> Prop :=
(* immediate *)
| subterm_constr: forall x t c ys e, subterm_e e (Econstr x t c ys e)
| subterm_proj: forall v t n y e, subterm_e e (Eproj v t n y e)
| subterm_prim: forall x t f ys e, subterm_e e (Eprim x t f ys e)
(* remote *)
| subterm_constr':
    forall x t c ys e e', subterm_e e' e -> subterm_e e' (Econstr x t c ys e)
| subterm_proj':
    forall v t n y e e', subterm_e e' e -> subterm_e e' (Eproj v t n y e)
| subterm_prim':
    forall x t f ys e e', subterm_e e' e -> subterm_e e' (Eprim x t f ys e)
(* in fdefs *)
| subterm_fds:
    forall e' fds e,
      subterm_fds_e e' fds -> subterm_e e' (Efun fds e)
with subterm_fds_e: exp -> fundefs -> Prop :=
     | subterm_cons:
         forall e f t ys fds', subterm_fds_e e (Fcons f t ys e fds')
     | subterm_cons':
         forall e' e f t ys fds', subterm_e e' e -> subterm_fds_e e' (Fcons f t ys e fds')
     | subterm_cons_fds:
         forall e' fds' f t ys e , subterm_fds_e e' fds' -> subterm_fds_e e' (Fcons f t ys e fds').

Inductive subfds_fds: fundefs -> fundefs -> Prop :=
| subfds_cons':
    forall fds' fds f t ys e,
      subfds_fds fds' fds ->
      subfds_fds fds' (Fcons f t ys e fds)
| subfds_cons:
    forall fds f t ys e, subfds_fds fds (Fcons f t ys e fds).


Definition subterm_or_eq: exp -> exp -> Prop :=
  fun e' e => subterm_e e' e \/ e' = e.

Definition subfds_or_eq: fundefs -> fundefs -> Prop :=
  fun fds' fds => subfds_fds fds' fds \/ fds' = fds.

Definition subfds_e: fundefs -> exp -> Prop := 
  fun fds  e =>
    exists fds' e', subterm_or_eq (Efun fds' e') e /\  subfds_or_eq fds fds'.

Definition subfds_or_eq_left:
  forall fds' fds fds'',
    subfds_fds fds fds' -> subfds_or_eq fds' fds'' -> subfds_or_eq fds fds''.
Proof.
  induction fds'; intros.
  - inversion H; subst. eapply IHfds'. apply H3. admit. admit.
Admitted.  

Theorem subfds_e_subfds:
  forall fds e fds', subfds_fds fds' fds -> subfds_e fds e -> subfds_e fds' e.
Proof.
  destruct fds; intros.
  - destruct H0; destructAll. exists x. exists x0. split.
    assumption.  eapply subfds_or_eq_left. apply H. assumption.
  - inversion H. 
Qed.


Definition num_occur_list (lv:list var) (v:var) : nat :=
  fold_right (fun v' n => if (var_dec v v') then 1 + n
                          else n) 0 lv.

(* number of time var occurs in exp (free or not) *)
(* Inductive num_occur: exp -> var -> nat -> Prop := *)
(* | Num_occ_constr: *)
(*   forall x t c ys e v n, *)
(*     num_occur e v n -> *)
(*     num_occur (Econstr x t c ys e) v (n + (num_occur_list ys v)) *)
(* | Num_occ_prim: *)
(*     forall x t f ys e v n, *)
(*       num_occur e v n -> *)
(*       num_occur (Eprim x t f ys e) v (n + (num_occur_list ys v)) *)
(* | Num_occ_case: *)
(*     forall v' cl v, *)
(*       num_occur (Ecase v' cl) v (num_occur_list (v'::(snd (split cl))) v) *)
(* | Num_occ_proj: *)
(*     forall e v n  y v' t n', *)
(*       num_occur  e v n ->  *)
(*       num_occur (Eproj v' t n' y e) v (num_occur_list [y] v + n) *)
(* | Num_occ_app: *)
(*     forall f ys v, *)
(*                  num_occur (Eapp f ys) v (num_occur_list (f::ys) v) *)
(* | Num_occ_fun: *)
(*     forall e v n m fl, *)
(*       num_occur e v n -> *)
(*       num_occur_fds fl v m -> *)
(*       num_occur (Efun fl e) v (n + m ) *)
(* with num_occur_fds: fundefs -> var -> nat -> Prop := *)
(*      | Num_occ_nil : *)
(*          forall v, *)
(*            num_occur_fds Fnil v 0 *)
(*      | Num_occ_cons : *)
(*          forall v t n v' ys e fds' m, *)
(*            num_occur e v n -> *)
(*            num_occur_fds fds' v m -> *)
(*            num_occur_fds (Fcons v' t ys e fds') v (n + m). *)


(* (* number of times var occurs in a context *) *)
(* Inductive num_occur_ec: exp_ctx -> var -> nat -> Prop := *)
(* | Noec_hole: forall v, num_occur_ec Hole_c v 0 *)
(* | Noec_constr: forall c v n x t ys g, *)
(*                  num_occur_ec c v n ->  *)
(*                  num_occur_ec (Econstr_c x t g ys c) v (num_occur_list ys v + n) *)
(* | Noec_prim: forall c v n x t f ys,  *)
(*                num_occur_ec c v n ->  *)
(*                num_occur_ec (Eprim_c x t f ys c) v (num_occur_list ys v + n ) *)
(* | Noec_proj: forall  v n y v' t n' c, *)
(*                num_occur_ec c v n -> *)
(*                num_occur_ec (Eproj_c v' t n' y c) v (num_occur_list [y] v + n) *)
(* | Noec_fun1: forall n m fds c v, *)
(*                num_occur_ec c v n -> *)
(*                num_occur_fds fds v m -> *)
(*                num_occur_ec (Efun1_c fds c) v (n+m) *)
(* | Noec_fun2: forall n m fdc e v , *)
(*                num_occur e v n -> *)
(*                num_occur_fdc fdc v m -> *)
(*                num_occur_ec (Efun2_c fdc e) v (n + m) *)
(* with num_occur_fdc : fundefs_ctx -> var -> nat -> Prop := *)
(*      | Nofc_fcons1 : forall v n m fds t ys c f, *)
(*                        num_occur_ec c v n -> *)
(*                        num_occur_fds fds v m ->  *)
(*                        num_occur_fdc (Fcons1_c f t ys c fds) v  (n + m) *)
(*      | Nofc_fcons2 : forall e v n m fdc f t ys, *)
(*                        num_occur e v n -> *)
(*                        num_occur_fdc fdc v m -> *)
(*                        num_occur_fdc (Fcons2_c f t ys e fdc) v (n + m). *)


(* (* number of times var occurs in exp in an applied position *) *)
(* Inductive num_occur_app: exp -> var -> nat -> Prop := *)
(* | Num_oa_constr: *)
(*   forall x t c ys e v n, *)
(*     num_occur_app e v n -> num_occur_app (Econstr x t c ys e) v n *)
(* | Num_oa_prim: *)
(*     forall x t f ys e v n, *)
(*       num_occur_app e v n -> num_occur_app (Eprim x t f ys e) v n *)
(* | Num_oa_case: *)
(*     forall v' cl v, *)
(*       num_occur_app (Ecase v' cl) v (num_occur_list [v'] v) *)
(* | Num_oa_proj: *)
(*     forall e v n  y v' t n', (* TODO: A&J counts y here *) *)
(*       num_occur_app e v n ->  *)
(*       num_occur_app (Eproj v' t n' y e) v (num_occur_list [y] v + n) *)
(* | Num_oa_app: *)
(*     forall f ys v, *)
(*       num_occur_app (Eapp f ys) v (num_occur_list [f] v) *)
(* | Num_oa_fun: *)
(*     forall e v n m fl, *)
(*       num_occur_app e v n -> *)
(*       num_occur_app_fds fl v m -> *)
(*       num_occur_app (Efun fl e) v (n + m ) *)
(* with num_occur_app_fds: fundefs -> var -> nat -> Prop := *)
(*      | Num_oa_nil : forall v, *)
(*                       num_occur_app_fds Fnil v 0 *)
(*      | Num_oa_cons : forall v t n v' ys e fds' m, *)
(*                        num_occur_app e v n -> *)
(*                        num_occur_app_fds fds' v m -> *)
(*                        num_occur_app_fds (Fcons v' t ys e fds') v (n + m). *)

(* (* number of times var occurs in exp in an escaping position *) *)
(* Inductive num_occur_esc: exp -> var -> nat -> Prop := *)
(* | Num_oe_constr: *)
(*   forall x t c ys e v n, *)
(*     num_occur_esc e v n -> *)
(*     num_occur_esc (Econstr x t c ys e) v (n + (num_occur_list ys v)) *)
(* | Num_oe_prim: *)
(*     forall x t f ys e v n, *)
(*       num_occur_esc e v n -> *)
(*       num_occur_esc (Eprim x t f ys e) v (n + (num_occur_list ys v)) *)
(* | Num_oe_case: *)
(*     forall v' cl v, *)
(*       num_occur_esc (Ecase v' cl) v (num_occur_list (snd (split cl)) v) *)
(* | Num_oe_proj: *)
(*     forall e v n  y v' t n', *)
(*       num_occur_esc  e v n ->  *)
(*       num_occur_esc (Eproj v' t n' y e) v n *)
(* | Num_oe_app: *)
(*     forall f ys v, *)
(*       num_occur_esc (Eapp f ys) v (num_occur_list ys v) *)
(* | Num_oe_fun: *)
(*     forall e v n m fl, *)
(*       num_occur_esc e v n -> *)
(*       num_occur_esc_fds fl v m -> *)
(*       num_occur_esc (Efun fl e) v (n + m ) *)
(* with num_occur_esc_fds: fundefs -> var -> nat -> Prop := *)
(*      | Num_oe_nil : *)
(*          forall v, *)
(*            num_occur_esc_fds Fnil v 0 *)
(*      | Num_oe_cons : *)
(*          forall v t n v' ys e fds' m, *)
(*            num_occur_esc e v n -> *)
(*            num_occur_esc_fds fds' v m -> *)
(*            num_occur_esc_fds (Fcons v' t ys e fds') v (n + m).   *)

Inductive bv_e: exp -> list var -> Prop :=
| Constr_bv :
    forall e l x t c ys, bv_e e l -> bv_e (Econstr x t c ys e) (x::l)
| Case_bv :
    forall v cl, bv_e (Ecase v cl) []
| Proj_bv:
    forall v t n y e l, bv_e e l -> bv_e (Eproj v t n y e) (v::l)
| Fun_bv:
    forall fl e l1 l2, bv_f fl l1 -> bv_e e l2 -> bv_e (Efun fl e) (l1 ++ l2)
| App_bv :
    forall f ys, bv_e (Eapp f ys) []
| Prim_bv :
    forall x t f ys e l, bv_e e l -> bv_e (Eprim x t f ys e) (x::l)
with bv_f : fundefs -> list var -> Prop :=
     | Cons_bv :
         forall f t ys e fds l1 l2,
           bv_e e l1 ->
           bv_f fds l2 ->
           bv_f (Fcons f t ys e fds) (f::(ys++(l1++l2)))
     | Nil_bv : bv_f Fnil [].

Hint Constructors bv_e bv_f.

Theorem e_bv_e :
  forall e, exists l, bv_e e l
                      with e_bv_f: forall f, exists l, bv_f f l.
Proof.
  induction e; destructAll; clear e_bv_e; eauto.
  specialize (e_bv_f f). destruct e_bv_f. eauto. 
  induction f; destructAll; clear e_bv_f; eauto.
  specialize (e_bv_e e); destruct e_bv_e. eauto.
Qed.



(*   
  Theorem bv_e_det: forall e l1 l2, bv_e e l1 -> bv_e e l2 -> l1 = l2
   with bv_f_det: forall f l1 l2, bv_f f l1 -> bv_f f l2 -> l1 = l2.                     
  Proof.
    - induction e; clear bv_e_det; intros; auto; inversion H; inversion H0; subst; auto.  
      + specialize (IHe _ _ H7 H14); subst; reflexivity.
      + specialize (IHe _ _ H7 H14); subst; reflexivity.
      + specialize (bv_f_det f _ _ H3 H8); specialize (IHe _ _ H5 H10); subst; reflexivity.
      + specialize (IHe _ _ H7 H14); subst; reflexivity.
    - induction f; clear bv_f_det; intros; auto; inversion H; inversion H0; subst.
      + specialize (bv_e_det e _ _ H7 H15); specialize (IHf _ _ H8 H16); subst; reflexivity.
      + reflexivity.
  Qed.
 *)

Theorem findtag_not_empty:
  forall A cl (k:A) (v:tag), findtag cl v = Some k -> 0 < (length cl).
Proof.
  induction cl; intros.
  - inversion H.
  - simpl in H. destruct a. destruct (M.elt_eq t v).
    + inversion H. simpl. omega.
    + simpl. apply IHcl in H. omega.
Qed.

Inductive split_fds: fundefs -> fundefs -> fundefs -> Prop :=
| Left_f:
    forall lfds rfds lrfds v t ys e,
      split_fds lfds rfds lrfds ->
      split_fds (Fcons v t ys e lfds) rfds (Fcons v t ys e lrfds)
| Right_f:
    forall lfds rfds lrfds v t ys e,
      split_fds lfds rfds lrfds ->
      split_fds lfds (Fcons v t ys e rfds) (Fcons v t ys e lrfds)
| End_f: split_fds Fnil Fnil Fnil.

(** some lemmas about split_fds. *)
Lemma split_fds_nil_l fdefs : split_fds fdefs Fnil fdefs.
  induction fdefs; constructor; eauto.
Qed.

Lemma split_fds_nil_r fdefs : split_fds Fnil fdefs fdefs.
  induction fdefs; constructor; eauto.
Qed.

Lemma split_fds_trans B1 B2 B3 B1' B2' :
  split_fds B1 B1' B2 ->
  split_fds B2 B2' B3 ->
  exists B2,
    split_fds B1' B2' B2 /\ split_fds B1 B2 B3.
Proof.
  intros Hs1 Hs2. revert B1 B1' Hs1. induction Hs2; intros B1 B1' Hs1.
  - inv Hs1. 
    edestruct IHHs2 as [B2'' [Hs3 Hs4]]; eauto.
    eexists. split; eauto. constructor; eauto.
    edestruct IHHs2 as [B2'' [Hs3 Hs4]]; eauto.
    eexists. split; constructor; eauto.
  - edestruct IHHs2 as [B2'' [Hs3 Hs4]]; eauto.
    eexists. split; constructor; eauto.
  - eexists; split; eauto using split_fds_nil_l.
Qed.  

Lemma split_fds_sym B1 B2 B3 :
  split_fds B1 B2 B3 ->
  split_fds B2 B1 B3.
Proof.
  intros Hs1. induction Hs1; now constructor; eauto.
Qed.

Lemma split_fds_Fnil B1 B2 :
  split_fds B1 B2 Fnil ->
  B1 = Fnil /\ B2 = Fnil.
Proof.
  intros H. inv H; eauto.
Qed.

Lemma split_fds_Fcons_l B1 B2 B3 :
  split_fds B1 B2 B3 ->
  B1 <> Fnil -> B3 <> Fnil.
Proof.
  intros H1 H2. inv H1; eauto; congruence.
Qed.

Lemma split_fds_Fcons_r B1 B2 B3 :
  split_fds B1 B2 B3 ->
  B2 <> Fnil -> B3 <> Fnil.
Proof.
  intros H1 H2. inv H1; eauto; congruence.
Qed.


Lemma split_fds_Fnil_eq_l B1 B2 :
  split_fds Fnil B1 B2 -> B1 = B2.
Proof.
  revert B1. induction B2; intros B1 H; auto; inv H; f_equal; eauto.
Qed.

Lemma split_fds_Fnil_eq_r B1 B2 :
  split_fds B1 Fnil B2 -> B1 = B2.
Proof.
  revert B1. induction B2; intros B1 H; auto; inv H; f_equal; eauto.
Qed.


Fixpoint fundefs_append (B1 B2 : fundefs) : fundefs :=
  match B1 with
    | Fcons f t xs xe B => Fcons f t xs xe (fundefs_append B B2)
    | Fnil => B2
  end.
    
Lemma def_funs_append B B1 B2 rho rho' :
  def_funs B (fundefs_append B1 B2) rho rho' =
  def_funs B B1 rho (def_funs B B2 rho rho').
Proof.
  induction B1; simpl; eauto. now rewrite IHB1.
Qed.

Lemma find_def_fundefs_append_r f B1 B2 v:
  find_def f B2 = Some v ->
  find_def f B1 = None ->
  find_def f (fundefs_append B1 B2) = find_def f B2.
Proof.
  induction B1; simpl; intros H1 H2; eauto.
  destruct (M.elt_eq f v0); try discriminate; eauto.
Qed.

Lemma find_def_fundefs_append_l f B1 B2 v:
  find_def f B1 = Some v ->
  find_def f (fundefs_append B1 B2) = find_def f B1.
Proof.
  induction B1; simpl; intros H2; eauto; try discriminate.
  destruct (M.elt_eq f v0); try discriminate; eauto.
Qed.

Lemma fundefs_append_split_fds B1 B2 B3 :
  fundefs_append B1 B2 = B3 ->
  split_fds B1 B2 B3.
Proof.
  revert B1. induction B3; intros B1 Hdefs.
  - destruct B1; simpl in Hdefs; subst. inv Hdefs.
    constructor. eauto.
    eapply split_fds_nil_r.
  - destruct B1; simpl in Hdefs; try congruence. subst.
    constructor.
Qed.

Lemma find_def_fundefs_append_Fcons_neq f v t ys e B1 B2 :
  f <> v ->
  find_def f (fundefs_append B1 (Fcons v t ys e B2)) =
  find_def f (fundefs_append B1 B2).
Proof.
  intros Hneq. revert B2. induction B1; intros B2.
  - simpl. destruct (M.elt_eq f v0); eauto.
  - simpl. destruct (M.elt_eq f v); try contradiction; eauto.
Qed.

Lemma findtag_In_patterns {A} P c (v : A) :
  findtag P c = Some v ->
  List.In (c, v) P.
Proof.
  induction P as [ | [c' e'] P IHP]; intros H; try discriminate.
  simpl in H. edestruct (M.elt_eq c' c).
  - inv H. now left.
  - right. eauto.
Qed.
   
Lemma findtag_append_spec {A} c P P' (v : A) :
  findtag (P ++ P') c = Some v ->
  (findtag P c = Some v) \/
  (findtag P' c = Some v /\ forall v, ~ List.In (c, v) P).
Proof.
  induction P as [| [c' v'] P IHP]; intros H.
  - simpl in H. right; split; eauto.
  - simpl in *.
    destruct (M.elt_eq c' c); eauto.
    destruct (IHP H) as [H1 | [H1 H2]]; eauto.
    right; split; eauto. intros v''.
    intros Hc. inv Hc. inv H0; congruence.
    eapply H2; eauto.
Qed.

Lemma findtag_append_not_In {A} c (P P' : list (tag * A)) :
  (forall v, ~ List.In (c, v) P) ->
  findtag (P ++ P') c = findtag P' c.
Proof.
  induction P as [| [c' v'] P IHP]; simpl; intros H; eauto.
  destruct (M.elt_eq c' c); eauto.
  - exfalso. subst. eapply H. left; eauto.
  - eapply IHP. intros x Hc. eapply H. eauto.
Qed.

Lemma findtag_append_Some {A} c P P' (v : A) :
  findtag P c = Some v ->
  findtag (P ++ P') c = Some v.
Proof.
  induction P as [| [c' v'] P IHP]; simpl; intros H; eauto.
  - inv H.
  - destruct (M.elt_eq c' c); eauto.
Qed.

Lemma getlist_In (rho : env) ys x vs :
  getlist ys rho = Some vs ->
  List.In x ys ->
  exists v, M.get x rho = Some v.
Proof.
  revert x vs. induction ys; intros x vs Hget H. inv H.
  inv H; simpl in Hget.
  - destruct (M.get x rho) eqn:Heq; try discriminate; eauto.
  - destruct (M.get a rho) eqn:Heq; try discriminate; eauto.
    destruct (getlist ys rho) eqn:Heq'; try discriminate; eauto.
Qed.

Lemma findtag_In {A} (P : list (tag * A)) c e :
  findtag P c = Some e -> List.In (c, e) P.
Proof.
  revert e. induction P as [| [c' e'] P IHp]; intros x H; try now inv H.
  simpl in H. inv H.
  destruct (M.elt_eq c' c); inv H1; try now constructor.
  constructor 2. apply IHp; eauto.
Qed.

Lemma Forall2_nthN {A} (R : A -> A -> Prop) (l1 l2 : list A)
      (n : N) (v1 : A):
  Forall2 R l1 l2 ->
  nthN l1 n = Some v1 ->
  exists v2,
    nthN l2 n = Some v2 /\
    R v1 v2.
Proof.
  revert l2 n.
  induction l1 as [| x xs IHxs ]; intros l2 n H Hnth.
  - inv H. discriminate.
  - inv H. destruct n as [| n].
    + simpl in Hnth. inv Hnth.
      eexists. split; simpl; eauto.
    + edestruct IHxs as [v2 [Hnth2 Hr]]; eauto.
Qed.

Lemma nthN_length {A} (l1 l2 : list A) (n : N) (v1 : A) :
  length l1 = length l2 ->
  nthN l1 n = Some v1 ->
  exists v2,
    nthN l2 n = Some v2.
Proof.
  revert l2 n.
  induction l1 as [| x xs IHxs ]; intros l2 n H Hnth.
  - inv H. discriminate.
  - inv H. destruct n as [| n]; destruct l2; try discriminate.
    + simpl in Hnth. inv Hnth.
      eexists. split; simpl; eauto.
    + inv H1. edestruct IHxs as [v2 Hnth2]; eauto.
Qed.

Lemma setlist_Forall2_get (P : val -> val -> Prop)
      xs vs1 vs2 rho1 rho2 rho1' rho2' x : 
  Forall2 P vs1 vs2 ->
  setlist xs vs1 rho1 = Some rho1' ->
  setlist xs vs2 rho2 = Some rho2' ->
  List.In x xs ->
  exists v1 v2,
    M.get x rho1' = Some v1 /\
    M.get x rho2' = Some v2 /\ P v1 v2.
Proof.
  revert rho1' rho2' vs1 vs2.
  induction xs; simpl; intros rho1' rho2' vs1 vs2 Hall Hset1 Hset2 Hin.
  - inv Hin.
  - destruct (Coqlib.peq a x); subst.
    + destruct vs1; destruct vs2; try discriminate.
      destruct (setlist xs vs1 rho1) eqn:Heq1;
        destruct (setlist xs vs2 rho2) eqn:Heq2; try discriminate.
      inv Hset1; inv Hset2. inv Hall.
      repeat eexists; try rewrite M.gss; eauto.
    + destruct vs1; destruct vs2; try discriminate.
      destruct (setlist xs vs1 rho1) eqn:Heq1;
        destruct (setlist xs vs2 rho2) eqn:Heq2; try discriminate.
      inv Hset1; inv Hset2. inv Hall. inv Hin; try congruence.
      edestruct IHxs as [v1 [v2 [Hget1 [Hget2 HP]]]]; eauto.
      repeat eexists; eauto; rewrite M.gso; eauto.
Qed.

Lemma setlist_not_In (xs : list var) (vs : list val) (rho rho' : env) (x : var) : 
  setlist xs vs rho = Some rho' ->
  ~ List.In x xs ->
  M.get x rho = M.get x rho'.
Proof.
  revert vs rho'.
  induction xs; simpl; intros vs rho' Hset Hin.
  - destruct vs; congruence.
  - destruct vs; try discriminate.
    destruct (setlist xs vs rho) eqn:Heq1; try discriminate. inv Hset.
    rewrite M.gso; eauto.
Qed.

Lemma setlist_length (rho rho' rho1 : env)
      (xs : list var) (vs1 vs2 : list val) :
  length vs1 = length vs2 -> 
  setlist xs vs1 rho = Some rho1 ->
  exists rho2, setlist xs vs2 rho' = Some rho2.
Proof.
  revert vs1 vs2 rho1.
  induction xs as [| x xs IHxs ]; intros vs1 vs2 rho1 Hlen Hset.
  - inv Hset. destruct vs1; try discriminate. inv H0.
    destruct vs2; try discriminate. eexists; simpl; eauto. 
  - destruct vs1; try discriminate. destruct vs2; try discriminate.
    inv Hlen. simpl in Hset. 
    destruct (setlist xs vs1 rho) eqn:Heq2; try discriminate.
    edestruct (IHxs _ _ _ H0 Heq2) as  [vs2' Hset2].
    eexists. simpl; rewrite Hset2; eauto.
Qed.

Lemma split_fds_cons_l_append_fundefs f tau xs e B1 B2 B3 : 
  split_fds (Fcons f tau xs e B1) B2 B3 ->
  exists B1' B2',
    B3 = fundefs_append B1' (Fcons f tau xs e B2') /\
    split_fds B1 B2 (fundefs_append B1' B2').
Proof.
  revert B1 B2. induction B3; intros B1 B2 Hspl.
  - inv Hspl.
    + exists Fnil, B3; eauto.
    + edestruct IHB3 as [B1' [B2' [Heq Hspl]]]; eauto.
      exists (Fcons v t l e0 B1'), B2'. rewrite Heq; split; eauto.
      simpl; constructor; eauto.
  - inv Hspl.
Qed.

Lemma split_fds_cons_r_append_fundefs f tau xs e B1 B2 B3 : 
  split_fds B1 (Fcons f tau xs e B2) B3 ->
  exists B1' B2',
    B3 = fundefs_append B1' (Fcons f tau xs e B2') /\
    split_fds B1 B2 (fundefs_append B1' B2').
Proof.
  revert B1 B2. induction B3; intros B1 B2 Hspl.
  - inv Hspl.
    + edestruct IHB3 as [B1' [B2' [Heq Hspl]]]; eauto.
      exists (Fcons v t l e0 B1'), B2'. rewrite Heq; eauto. split; eauto.
      simpl. constructor; eauto.
    + exists Fnil, B3; eauto.
  - inv Hspl.
Qed.

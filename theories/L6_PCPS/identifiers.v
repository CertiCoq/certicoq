Require Import Coq.Lists.List Coq.Lists.SetoidList Coq.NArith.BinNat Coq.PArith.BinPos
        Coq.MSets.MSetRBT Coq.Lists.List Coq.Sets.Ensembles Omega.
Require Import L6.cps L6.cps_util L6.ctx L6.set_util L6.Ensembles_util L6.List_util.
Require Import Libraries.Coqlib.
Import ListNotations.

Import PS.

Open Scope ctx_scope.

Definition FVSet := PS.t.

(** * Function definitions *) 

(** [name_in_fundefs B] is the set of the function names in [B] *)
Fixpoint name_in_fundefs (B : fundefs) : Ensemble var :=
  match B with
    | Fnil => Empty_set var
    | Fcons f' _ _ _ B =>
      Union var (Singleton var f') (name_in_fundefs B)
  end.

(** [fun_in_fundefs B] is the set of functions defined in [B] *)
Fixpoint fun_in_fundefs  (B : fundefs) : Ensemble (var * fTag * list var * exp) :=
  match B with
    | Fnil => Empty_set _
    | Fcons f tau xs e B =>
      Union _ (Singleton _ (f, tau, xs, e))
            (fun_in_fundefs B)
  end.

(** The set of function names is decidable *)
Instance Decidable_name_in_fundefs (B : fundefs) :
  Decidable (name_in_fundefs B).
Proof.
  constructor.
  induction B; intros x.
  - destruct (peq x v); subst.
    left. left. eauto.
    destruct (IHB x). left. right; eauto.
    right. intros Hc. inv Hc. inv H0; congruence. 
    exfalso. eauto.
  - right. intros Hc; inv Hc.
Qed.

(** Lemmas about [split_fds] and [name_in_fundefs] *)
Lemma split_fds_name_in_fundefs B1 B2 B3 :
  split_fds B1 B2 B3 ->
  Same_set var (name_in_fundefs B3)
           (Union var (name_in_fundefs B1) (name_in_fundefs B2)).
Proof with eauto with Ensembles_DB.
  intros Hspl. induction Hspl; simpl; try rewrite IHHspl...
Qed.  

Lemma fundefs_append_name_in_fundefs B1 B2 B3 :
  fundefs_append B1 B2 = B3 ->
  Same_set var (name_in_fundefs B3)
           (Union var (name_in_fundefs B1) (name_in_fundefs B2)).
Proof with eauto with Ensembles_DB.
  revert B3. induction B1; intros B3 Heq; simpl.
  - destruct B3. simpl in Heq. inv Heq. simpl. 
    rewrite IHB1; eauto... simpl. inv Heq.
  - inv Heq. simpl; symmetry...
Qed.

Lemma split_fds_fun_in_fundefs B1 B2 B3 :
  split_fds B1 B2 B3 ->
  Same_set _ (fun_in_fundefs B3)
           (Union _ (fun_in_fundefs B1) (fun_in_fundefs B2)).
Proof with eauto with Ensembles_DB.
  intros Hspl1. induction Hspl1; simpl; try rewrite IHHspl1...
Qed.

Lemma fundefs_append_fun_in_fundefs B1 B2 B3 :
  fundefs_append B1 B2 = B3 ->
  Same_set _ (fun_in_fundefs B3)
           (Union _ (fun_in_fundefs B1) (fun_in_fundefs B2)).
Proof.
  intros H. eapply split_fds_fun_in_fundefs.
  eapply fundefs_append_split_fds; eauto.
Qed.

(** Names of function in a function definition evaluation context *)
Lemma name_in_fundefs_ctx B e1 e2 :
  Same_set _ (name_in_fundefs (B <[ e1 ]>)) (name_in_fundefs (B <[ e2 ]>)).
Proof.
  induction B; simpl;
  (apply Same_set_Union_compat; [ now apply Same_set_refl |]).
  now apply Same_set_refl.
  eassumption.
Qed.


(** Alternative definition of [name_in_fundefs] using set comprehension:  
   [names_in_fundefs b] = $\{ f ~|~ \exists ~xs ~tau ~e,~(f, ~xs, ~tau, ~e) \in B \}$ *)
Lemma name_in_fundefs_big_cup_fun_in_fundefs B :
  Same_set var (name_in_fundefs B) (big_cup (fun_in_fundefs B)
                                            (fun p =>
                                               let '(x, _, _, _) := p in
                                               Singleton var x)).
Proof with eauto with Ensembles_DB.
  induction B; simpl in *.
  - rewrite Union_big_cup, big_cup_Singleton...
  - symmetry...
Qed.

Lemma fun_in_fundefs_name_in_fundefs f tau xs e B :
    fun_in_fundefs B (f, tau, xs, e) ->
    name_in_fundefs B f.
Proof.
  intros H. eapply name_in_fundefs_big_cup_fun_in_fundefs.
  repeat eexists; eauto. constructor.
Qed.

(** ** Lemmas about [find_def] and [def_funs] *)

Lemma find_def_name_in_fundefs f B v:
  find_def f B = Some v ->
  name_in_fundefs B f.
Proof.
  induction B; simpl; intros H; try now inv H.
  destruct (M.elt_eq f v0); inv H.
  left; eauto. right; eauto.
Qed.

Lemma name_not_in_fundefs_find_def_None f B:
  ~ name_in_fundefs B f ->
  find_def f B = None.
Proof.
  induction B; simpl; intros H; eauto.
  destruct (M.elt_eq f v); subst.
  - exfalso. apply H. now left.
  - eapply IHB. intros Hc. apply H. now right.
Qed.

(** [find_def] is sound w.r.t. [fun_in_fundefs] *)
Lemma find_def_correct f B tau xs e :
  find_def f B = Some (tau, xs, e) ->
  fun_in_fundefs B (f, tau, xs, e).
Proof.
  induction B; simpl; intros H; try discriminate.
  destruct (M.elt_eq f v).
  - inv H. left; eauto.
  - right; eauto.
Qed.

Lemma def_funs_spec x v B B' rho rho' :
  M.get x (def_funs B' B rho rho') = Some v ->
  (name_in_fundefs B x /\ v = cps.Vfun rho B' x) \/
  (~ name_in_fundefs B x /\ M.get x rho' = Some v).
Proof.
  induction B; intros Hget.
  - simpl in Hget. rewrite M.gsspec in Hget. destruct (peq x v0).
    + inv Hget. left. split; eauto. constructor; eauto.
    + destruct (IHB Hget) as [[H1 H2] | [H1 H2]]; eauto.
      * left. split; eauto. constructor 2; eauto.
      * right. split; eauto. intros Hc. inv Hc; try (inv H; congruence); eauto.
  - simpl in Hget. right. split; eauto. intros Hc; inv Hc.
Qed.

Lemma def_funs_eq x B B' rho rho' :
  name_in_fundefs B x ->
  M.get x (def_funs B' B rho rho') = Some (cps.Vfun rho B' x).
Proof.
  induction B; intros Hin; inv Hin.
  - simpl. inv H; rewrite M.gss. eauto.
  - simpl. rewrite M.gsspec. destruct (peq x v); subst; eauto.
Qed.

Lemma def_funs_neq x B B' rho rho' :
  ~ name_in_fundefs B x ->
  M.get x (def_funs B' B rho rho') = M.get x rho'.
Proof.
  induction B; intros Hin; simpl; eauto.
  rewrite M.gsspec. destruct (peq x v); subst; eauto.
  exfalso. apply Hin. constructor; eauto. eapply IHB.
  intros Hc.  eapply Hin. constructor 2; eauto.
Qed.

Lemma get_fundefs y v B B' rho :
  M.get y rho = Some v -> ~ name_in_fundefs B y ->
  M.get y (def_funs B' B rho rho) = Some v.
Proof.
  intros Hget Hn.
  rewrite def_funs_neq; eauto.
Qed.

Lemma getlist_fundefs ys vs B B' rho :
  getlist ys rho = Some vs ->
  (forall y, List.In y ys -> ~ name_in_fundefs B y) ->
  getlist ys (def_funs B' B rho rho) = Some vs.
Proof.
  revert rho vs. induction ys; intros rho vs Hget Hall.
  - now inv Hget.
  - simpl in Hget.
    destruct (M.get a rho) eqn:Heq1; try discriminate.
    destruct (getlist ys rho) eqn:Heq2; try discriminate. inv Hget.
    simpl. erewrite IHys; eauto. erewrite get_fundefs; eauto.
    intros Hc. eapply Hall; eauto. left; eauto.
    intros y Hin Hc. eapply Hall; eauto. right; eauto.
Qed.

(** Extend the environment with a block of functions and put them in the set *)
Lemma binding_in_map_def_funs B' B rho S  :
  binding_in_map S rho ->
  binding_in_map (Union _ (name_in_fundefs B) S) (def_funs B' B rho rho).
Proof.
  intros H x' Hs.
  destruct (Decidable_name_in_fundefs B). destruct (Dec x').
  - eexists. rewrite def_funs_eq; eauto.
  - destruct Hs; try contradiction. 
    edestruct H; eauto.
    eexists. erewrite def_funs_neq; eauto.
Qed.

(** * Free variables, inductive definitions *)

(** [occurs_free e] is the set of free variables of [e] *)
Inductive occurs_free : exp -> Ensemble var :=
| Free_Econstr1 :
    forall y x t ys e,
      List.In y ys ->
      occurs_free (Econstr x t ys e) y
| Free_Econstr2 :
    forall y x t ys e,
      ~ x = y ->
      occurs_free e y ->
      occurs_free (Econstr x t ys e) y
| Free_Ecase1 :
    forall x ys, 
      occurs_free (Ecase x ys) x
| Free_Ecase2 :  
    forall y x c e ys,
      occurs_free e y ->
      occurs_free (Ecase x ((c, e) :: ys)) y
| Free_Ecase3 :  
    forall y x c e ys,
      occurs_free (Ecase x ys) y ->
      occurs_free (Ecase x ((c, e) :: ys)) y
| Free_Eproj1 :
    forall y x tau n e,
      occurs_free (Eproj x tau n y e) y
| Free_Eproj2 :
    forall y x tau n y' e,
      x <> y ->
      occurs_free e y ->
      occurs_free (Eproj x tau n y' e) y
| Free_Efun1 :
    forall y defs e,
      ~ (name_in_fundefs defs y) -> 
      occurs_free e y ->
      occurs_free (Efun defs e) y
| Free_Efun2 :
    forall y defs e, 
      occurs_free_fundefs defs y ->
      occurs_free (Efun defs e) y
| Free_Eapp1 :
    forall x ys f,
      occurs_free (Eapp x f ys) x
| Free_Eapp2 :
    forall y x f ys,
      List.In y ys ->
      occurs_free (Eapp x f ys) y
| Free_Eprim1 :
    forall y x p ys e,
      List.In y ys ->
      occurs_free (Eprim x p ys e) y
| Free_Eprim2 :
    forall y x p ys e,
      x <> y ->
      occurs_free e y ->
      occurs_free (Eprim x p ys e) y
| Free_Ehalt :
    forall x, occurs_free (Ehalt x) x
with occurs_free_fundefs : fundefs -> Ensemble var :=
| Free_Fcons1 :
    forall x f tau ys e defs,  
      x <> f ->
      ~ (List.In x ys) ->
      ~ (name_in_fundefs defs x) ->
      occurs_free e x ->
      occurs_free_fundefs (Fcons f tau ys e defs) x
| Free_Fcons2 :
    forall x f tau ys e defs,
      occurs_free_fundefs defs x ->
      x <> f ->
      occurs_free_fundefs (Fcons f tau ys e defs) x.

Hint Constructors occurs_free.
Hint Constructors occurs_free_fundefs.

(** sanity check : The names of the functions cannot appear free in a fundefs block *)
Lemma fun_names_not_free_in_fundefs f defs :
  name_in_fundefs defs f ->
  ~ occurs_free_fundefs defs f.
Proof.
  intros Hname Hfree. 
  induction Hfree; inversion Hname; eauto.
  inv H3. eauto. inv H0; eauto.
Qed.

(** ** Useful set equalities *)

Lemma occurs_free_Econstr x t ys e :
  Same_set var (occurs_free (Econstr x t ys e))
           (Union _ (FromList ys) (Setminus var (occurs_free e) (Singleton var x))).
Proof.
  split; intros x' H; inv H; eauto.
  right. constructor; eauto. intros H. inv H; eauto.
  inv H0. constructor 2; eauto. intros Hc. subst. eauto.
Qed.

Lemma occurs_free_Eprim x f ys e :
  Same_set var (occurs_free (Eprim x f ys e))
           (Union _ (FromList ys) (Setminus var (occurs_free e) (Singleton var x))).
Proof.
  split; intros x' H; inv H; eauto.
  right. constructor; eauto. intros H. inv H; eauto.
  inv H0. eapply Free_Eprim2; eauto. intros Hc. subst. eauto.
Qed.

Lemma occurs_free_Eproj x tag n y e :
  Same_set var (occurs_free (Eproj x tag n y e))
           (Union _ (Singleton var y) (Setminus var (occurs_free e) (Singleton var x))).
Proof.
  split; intros x' H; inv H; eauto. 
  right. constructor; eauto. intros H. inv H; eauto.
  inv H0. eauto.
  inv H0. constructor; eauto.
  intros Hc. subst. eauto.
Qed.

Lemma occurs_free_Ehalt x :
  Same_set var (occurs_free (Ehalt x)) (Singleton _ x).
Proof.
  split; intros x' H; inv H; eauto.
Qed.

Lemma occurs_free_Eapp f ft ys :
  Same_set var (occurs_free (Eapp f ft ys))
           (Union _ (FromList ys) (Singleton var f)).
Proof.
  split; intros x' H; inv H; eauto. inv H0; eauto.
Qed.

Lemma occurs_free_Efun B e :
  Same_set var (occurs_free (Efun B e))
           (Union _ (occurs_free_fundefs B)
                  (Setminus _ (occurs_free e) (name_in_fundefs B))).
Proof.
  split; intros x' H; inv H; eauto.
  right; eauto. constructor; eauto.
  inv H0. eauto. 
Qed.

Lemma occurs_free_Ecase_nil x :
  Same_set var (occurs_free (Ecase x []))
           (Singleton _ x).
Proof.
  split; intros x' H; inv H; eauto.
Qed.

Lemma occurs_free_Ecase_cons x c e P :
  Same_set var (occurs_free (Ecase x ((c, e) :: P)))
           (Union _ (Singleton _ x)
                  (Union _ (occurs_free e)
                         (occurs_free (Ecase x P)))).
Proof.
  split; intros x' H; inv H; eauto.
  inv H0; eauto. inv H0; eauto.
Qed.


Lemma occurs_free_Ecase_app x c e P P' :
  Same_set var (occurs_free (Ecase x (P' ++ ((c, e) :: P))))
           (Union _ (Singleton _ x)
                  (Union _ (occurs_free (Ecase x P'))
                         (Union _ (occurs_free e)
                                (occurs_free (Ecase x P))))).
Proof with eauto with Ensembles_DB.
  induction P' as [| [c' e'] P' IHP']; simpl.
  - rewrite occurs_free_Ecase_nil, occurs_free_Ecase_cons...
  - rewrite !occurs_free_Ecase_cons, IHP', <- !Union_assoc...
Qed.

Lemma occurs_free_fundefs_Fcons f t xs e B :
  Same_set var (occurs_free_fundefs (Fcons f t xs e B))
           (Union var (Setminus var (occurs_free e)
                                (Union var (Singleton var f)
                                       (Union var (FromList xs)
                                              (name_in_fundefs B))))
                  (Setminus var (occurs_free_fundefs B) (Singleton var f))).
Proof.
  split; intros x H; inv H.
  - left. constructor; eauto. intros Hin. inv Hin; eauto.
    inv H. congruence. inv H; eauto.
  - right. constructor; eauto. intros H. inv H. congruence.
  - inv H0. constructor; eauto. 
    intros Hc. subst. eauto.
  - inv H0. constructor 2; eauto. intros Hc; subst; eauto.
Qed.

Lemma occurs_free_fundefs_Fnil :
  Same_set var (occurs_free_fundefs Fnil) (Empty_set var).
Proof.
  split; intros x H; inv H.
Qed.

Ltac normalize_occurs_free :=
  match goal with
    | [|- context[occurs_free (Econstr _ _ _ _)]] =>
      rewrite occurs_free_Econstr
    | [|- context[occurs_free (Eproj _ _ _ _ _)]] =>
      rewrite occurs_free_Eproj
    | [|- context[occurs_free (Ecase _ [])]] =>
      rewrite occurs_free_Ecase_nil
    | [|- context[occurs_free (Ecase _ (_ :: _))]] =>
      rewrite occurs_free_Ecase_cons
    | [|- context[occurs_free (Ecase _ (_ ++ _))]] =>
      rewrite occurs_free_Ecase_app
    | [|- context[occurs_free (Efun _ _)]] =>
      rewrite occurs_free_Efun
    | [|- context[occurs_free (Eapp _ _ _)]] =>
      rewrite occurs_free_Eapp
    | [|- context[occurs_free (Eprim _ _ _ _)]] =>
      rewrite occurs_free_Eprim
    | [|- context[occurs_free_fundefs (Fcons _ _ _ _ _)]] =>
       rewrite occurs_free_fundefs_Fcons
    | [|- context[occurs_free_fundefs Fnil]] =>
      rewrite occurs_free_fundefs_Fnil
  end.

Ltac normalize_occurs_free_in_ctx :=
  match goal with
    | [ H : context[occurs_free (Econstr _ _ _ _)] |- _ ] =>
      rewrite occurs_free_Econstr in H
    | [ H : context[occurs_free (Eproj _ _ _ _ _)]  |- _ ] =>
      rewrite occurs_free_Eproj in H
    | [ H : context[occurs_free (Ecase _ [])] |- _ ] =>
      rewrite occurs_free_Ecase_nil in H
    | [ H : context[occurs_free (Ecase _ (_ :: _))] |- _ ] =>
      rewrite occurs_free_Ecase_cons in H
    | [ H : context[occurs_free (Ecase _ (_ ++ _))] |- _ ] =>
      rewrite occurs_free_Ecase_app in H
    | [ H : context[occurs_free (Efun _ _)] |- _ ] =>
      rewrite occurs_free_Efun in H
    | [ H : context[occurs_free (Eapp _ _ _)] |- _ ] =>
      rewrite occurs_free_Eapp in H
    | [ H : context[occurs_free (Eprim _ _ _ _)] |- _ ] =>
      rewrite occurs_free_Eprim in H
    | [ H : context[occurs_free_fundefs (Fcons _ _ _ _ _)] |- _ ] =>
       rewrite occurs_free_fundefs_Fcons in H
    | [ H : context[occurs_free_fundefs Fnil] |- _ ] =>
      rewrite occurs_free_fundefs_Fnil in H
  end.

(** ** Useful set inclusions *)

Lemma occurs_free_fundefs_Fcons_Included f tau xs e B :
  Included var (occurs_free_fundefs B)
           (Union _ (occurs_free_fundefs (Fcons f tau xs e B)) (Singleton var f)).
Proof.
  intros x H. destruct (var_dec f x); subst; now eauto.
Qed.

Lemma occurs_free_Econstr_Included x t ys e :
  Included var (occurs_free e)
           (Union var (occurs_free (Econstr x t ys e)) (Singleton var x)).
Proof.
  intros x' Hin.
  destruct (var_dec x x'); subst; eauto.
Qed.

Lemma occurs_free_Eproj_Included x tau t y e :
  Included var (occurs_free e)
           (Union var (occurs_free (Eproj x tau t y e)) (Singleton var x)).
Proof.
  intros x' Hin.
  destruct (var_dec x x'); subst; eauto.
Qed.

Lemma occurs_free_Eprim_Included x f ys e :
  Included var (occurs_free e)
           (Union var (occurs_free (Eprim x f ys e)) (Singleton var x)).
Proof.
  intros x' Hin.
  destruct (var_dec x x'); subst; eauto.
Qed.

Lemma occurs_free_Efun_Included B e:
  Included var (occurs_free e)
           (Union var (occurs_free (Efun B e)) (name_in_fundefs B)).
Proof.
  intros x' Hin.
  destruct (@Dec _ _ (Decidable_name_in_fundefs B) x'); subst; eauto.
Qed.

Lemma occurs_free_Ecase_Included P c x e :
  List.In (c, e) P ->
  Included var (occurs_free e)
           (occurs_free (Ecase x P)).
Proof.
  intros Hin x' Hin'. induction P as [ | [c' e'] P IHP]; try now inv Hin.
  inv Hin.
  - inv H. constructor; eauto.
  - eapply Free_Ecase3. eapply IHP; eauto.
Qed.

Lemma occurs_free_in_fun f tau xs e B :
  fun_in_fundefs B (f, tau, xs, e) ->
  Included var (occurs_free e) 
           (Union var (FromList xs) (Union var (name_in_fundefs B)
                                           (occurs_free_fundefs B))).
Proof with eauto with Ensembles_DB.
  induction B; intros H; inv H.
  - inv H0. intros x H.
    destruct (peq x f); simpl; subst; eauto.
    destruct (in_dec var_dec x xs); eauto; subst.
    destruct (@Dec _ _ (Decidable_name_in_fundefs B) x); eauto.
  - intros x H. destruct (peq x v); subst; simpl...
    edestruct (IHB H0 x) as [H'| H']; eauto.
    inv H1...
Qed.

(** FV(B) = $\bigcup_{(f, xs e) \in B}(FV(e) \setminus xs \setminus names(B))$ *)
Lemma occurs_free_fundefs_big_cup B :
  Same_set _ (occurs_free_fundefs B)
           (big_cup (fun_in_fundefs B)
                    (fun p =>
                       (Setminus _ (let '(f, _, xs, e) := p in
                                    (Setminus _ (occurs_free e) (FromList xs)))
                                 (name_in_fundefs B)))).
Proof with eauto with Ensembles_DB.
  induction B; simpl.
  - rewrite occurs_free_fundefs_Fcons. rewrite IHB.
    rewrite Union_big_cup, big_cup_Singleton, Setminus_Union.
    apply Same_set_Union_compat...
    rewrite <- Setminus_big_cup.
    apply Same_Set_big_cup_r...
  - rewrite occurs_free_fundefs_Fnil.
    symmetry...
Qed.

Lemma split_fds_occurs_free_fundefs B1 B2 B3 :
  split_fds B1 B2 B3 ->
  Same_set var (occurs_free_fundefs B3)
           (Union _ (Setminus _ (occurs_free_fundefs B1) (name_in_fundefs B2))
                  (Setminus _ (occurs_free_fundefs B2) (name_in_fundefs B1))).
Proof with eauto 6 with Ensembles_DB.
  intros H1.
  rewrite !occurs_free_fundefs_big_cup, <- !Setminus_big_cup.
  eapply Same_set_trans with
  (s2 := Union var
               (big_cup (fun_in_fundefs B1) _)
               (big_cup (fun_in_fundefs B2) _)).
  - rewrite <- Union_big_cup. rewrite split_fds_fun_in_fundefs; eauto...
  - eapply Same_set_Union_compat; eapply Same_Set_big_cup_r.
    intros [[[f tau] xs] e]; rewrite split_fds_name_in_fundefs; eauto...
    intros [[[f tau] xs] e].
    rewrite split_fds_name_in_fundefs; eauto... 
Qed.

Lemma Same_set_fun_in_fundefs_Same_set_occurs_free_fundefs B1 B2 :
  Same_set _ (fun_in_fundefs B1) (fun_in_fundefs B2) ->
  Same_set _ (occurs_free_fundefs B1) (occurs_free_fundefs B2).
Proof with eauto with Ensembles_DB.
  rewrite !occurs_free_fundefs_big_cup. intros H.
  apply Same_Set_big_cup; eauto.
  intros [[[f tau] xs] e']. 
  rewrite !name_in_fundefs_big_cup_fun_in_fundefs...
Qed.

Lemma occurs_free_dec :
  (forall e, Decidable (occurs_free e)) /\
  (forall B, Decidable (occurs_free_fundefs B)).
Proof.
  exp_defs_induction IHe IHl IHdefs; try inv IHe; try inv IHl;
  try inv IHdefs; constructor; intros x.
  - destruct (in_dec var_dec x l); eauto.
    destruct (var_dec x v); subst. right. intros Hc. inv Hc; eauto.
    destruct (Dec x); eauto.
    right. intros Hc. inv Hc; eauto.
  - destruct (var_dec x v); subst; eauto.
    right; intros Hc. inv Hc; congruence.
  - destruct (var_dec x v); subst; eauto.
    destruct (Dec x); eauto.
    destruct (Dec0 x); eauto.
    right. intros Hc. inv Hc; eauto.
  - destruct (var_dec x v0); subst; eauto.
    destruct (var_dec x v); subst. right. intros Hc. inv Hc; eauto.
    destruct (Dec x); eauto.
    right. intros Hc. inv Hc; eauto.
  - destruct (Decidable_name_in_fundefs f2). destruct (Dec1 x).
    right. intros Hc. inv Hc; eauto. eapply fun_names_not_free_in_fundefs; eauto.
    destruct (Dec x); eauto.
    destruct (Dec0 x); eauto.
    right. intros Hc. inv Hc; eauto.
  - destruct (in_dec var_dec x l); eauto.
    destruct (var_dec x v); subst; eauto.
    right. intros Hc. inv Hc; eauto.
  - destruct (in_dec var_dec x l); eauto.
    destruct (var_dec x v); subst. right. intros Hc. inv Hc; eauto.
    destruct (Dec x); eauto.
    right. intros Hc. inv Hc; eauto.
  - destruct (var_dec x v); subst; eauto.
    right. intros Hc; inv Hc. congruence.
  - destruct (Decidable_name_in_fundefs f5). destruct (Dec1 x).
    right. intros Hc. inv Hc; eauto. eapply fun_names_not_free_in_fundefs; eauto.
    destruct (var_dec x v); subst. right. intros Hc. inv Hc; eauto.
    destruct (Dec0 x); eauto.
    destruct (in_dec var_dec x l). right. intros Hc. inv Hc; eauto.
    destruct (Dec x); eauto. right. intros Hc. inv Hc; eauto.
  - right. intros Hc. inv Hc.
Qed.

(** FV(e) is decidable *)
Instance Decidable_occurs_free e : Decidable (occurs_free e).
Proof.
  now apply occurs_free_dec.
Qed.
(** FV(B) is decidable *)
Instance Decidable_occurs_free_fundefs e : Decidable (occurs_free_fundefs e).
Proof.
  now apply occurs_free_dec.
Qed.   


Lemma split_fds_same_occurs_free_fundefs_Same_set B1 B2 B3 B3' :
  split_fds B1 B2 B3 ->
  split_fds B1 B2 B3' ->
  Same_set _ (occurs_free_fundefs B3) (occurs_free_fundefs B3').
Proof with eauto with Ensembles_DB.
  intros Hspl1 Hspl2. rewrite !occurs_free_fundefs_big_cup.
  apply Same_Set_big_cup.
  - intros [[[f tau] xs] e'].
    rewrite !split_fds_name_in_fundefs; [| eassumption ].
    rewrite (split_fds_name_in_fundefs B1 B2 B3'); [| eassumption ]...
  - rewrite !split_fds_fun_in_fundefs; [| eassumption ].
    rewrite (split_fds_fun_in_fundefs B1 B2 B3'); [| eassumption ]...
Qed.


(** Compatibility with contex application *)
Lemma occurs_free_ctx_mut :
  (forall c e e', Same_set _ (occurs_free e) (occurs_free e') ->
                  Same_set _ (occurs_free (c |[ e ]|))
                           (occurs_free (c |[ e' ]|))) /\
  (forall B e e', Same_set _ (occurs_free e) (occurs_free e') ->
                  Same_set _ (occurs_free_fundefs (B <[ e ]>))
                           (occurs_free_fundefs (B <[ e' ]>))).
Proof with eauto with Ensembles_DB.
  exp_fundefs_ctx_induction IHc IHf; eauto; simpl;
  intros; repeat normalize_occurs_free;
  try (rewrite IHc; [| eassumption ]); try (rewrite IHB; [| eassumption ]);
  eauto with Ensembles_DB.
  rewrite name_in_fundefs_ctx...
  rewrite name_in_fundefs_ctx...
Qed.


Corollary occurs_free_exp_ctx :
  forall c e e', Same_set _ (occurs_free e) (occurs_free e') ->
                 Same_set _ (occurs_free (c |[ e ]|))
                          (occurs_free (c |[ e' ]|)).
Proof.
  apply occurs_free_ctx_mut.
Qed.

Corollary occurs_free_fundefs_ctx :
  forall B e e', Same_set _ (occurs_free e) (occurs_free e') ->
                 Same_set _ (occurs_free_fundefs (B <[ e ]>))
                          (occurs_free_fundefs (B <[ e' ]>)).
Proof.
  apply occurs_free_ctx_mut.
Qed.

Lemma occurs_free_Ecase_ctx_app_mut :
  (forall C x c e P,
     Included _ (occurs_free (C |[ Ecase x ((c, e) :: P)]|))
              (Union _ (occurs_free (C |[ e ]|)) (occurs_free (C |[ Ecase x P ]|)))) /\
  (forall Cf x c e P,
     Included _ (occurs_free_fundefs (Cf <[ Ecase x ((c, e) :: P)]>))
              (Union _ (occurs_free_fundefs (Cf <[ e ]>)) (occurs_free_fundefs (Cf <[ Ecase x P ]>)))).
Proof with eauto with Ensembles_DB. 
  exp_fundefs_ctx_induction IHC IHCf; simpl; intros;
  repeat normalize_occurs_free; try now eauto with Ensembles_DB;
  try (now eapply Included_trans;
       [ apply Included_Union_compat;
         [ now apply Included_refl |
           apply Included_Setminus_compat; [ now eapply IHC | now apply Included_refl ] ] |
         rewrite Setminus_Union_distr; eauto with Ensembles_DB]).
  - eapply Included_trans.
    apply Included_Union_compat. now apply Included_refl.
    apply Included_Union_compat. now apply Included_refl.
    apply Included_Union_compat. now eauto. now apply Included_refl.
    do 4 (apply Union_Included; eauto with Ensembles_DB). 
  - rewrite Union_assoc.
    apply Included_Union_compat.
    eapply Included_trans. now eauto.
    now apply Union_Included; eauto with Ensembles_DB.
    rewrite name_in_fundefs_ctx...
  - eapply Included_trans.
    apply Included_Union_compat; [| now apply Included_refl ].
    apply Included_Setminus_compat. now eauto. now apply Included_refl.
    rewrite Setminus_Union_distr...
  - eapply Included_trans.
    apply Included_Union_compat; [ now apply Included_refl |].
    apply Included_Setminus_compat. now eauto. now apply Included_refl.
    rewrite name_in_fundefs_ctx, !Setminus_Union_distr...
Qed.

Corollary occurs_free_Ecase_ctx_app C x c e P :
  Included _ (occurs_free (C |[ Ecase x ((c, e) :: P)]|))
           (Union _ (occurs_free (C |[ e ]|)) (occurs_free (C |[ Ecase x P ]|))).
Proof. 
  now apply occurs_free_Ecase_ctx_app_mut.
Qed.

Lemma occurs_free_Ecase_ctx_app_mut' :
  (forall C x c e P,
     Included _ (occurs_free (C |[ Ecase x ((c, e) :: P)]|))
              (Union _ (occurs_free e) (occurs_free (C |[ Ecase x P ]|)))) /\
  (forall Cf x c e P,
     Included _ (occurs_free_fundefs (Cf <[ Ecase x ((c, e) :: P)]>))
              (Union _ (occurs_free e) (occurs_free_fundefs (Cf <[ Ecase x P ]>)))).
Proof with eauto with Ensembles_DB. 
  exp_fundefs_ctx_induction IHC IHCf; simpl; intros;
  repeat normalize_occurs_free; try now eauto with Ensembles_DB;
  try (now eapply Included_trans;
       [ apply Included_Union_compat;
         [ now apply Included_refl |
           apply Included_Setminus_compat; [ now eapply IHC | now apply Included_refl ] ] |
         rewrite Setminus_Union_distr; eauto with Ensembles_DB]).
  - eapply Included_trans.
    apply Included_Union_compat. now apply Included_refl.
    apply Included_Union_compat. now apply Included_refl.
    apply Included_Union_compat. now eauto. now apply Included_refl.
    do 4 (apply Union_Included; eauto with Ensembles_DB). 
  - rewrite Union_assoc.
    apply Included_Union_compat.
    eapply Included_trans. now eauto.
    now apply Union_Included; eauto with Ensembles_DB.
    rewrite name_in_fundefs_ctx...
  - eapply Included_trans.
    apply Included_Union_compat; [| now apply Included_refl ].
    apply Included_Setminus_compat. now eauto. now apply Included_refl.
    rewrite Setminus_Union_distr...
  - eapply Included_trans.
    apply Included_Union_compat; [ now apply Included_refl |].
    apply Included_Setminus_compat. now eauto. now apply Included_refl.
    rewrite name_in_fundefs_ctx, !Setminus_Union_distr...
Qed.

Corollary occurs_free_Ecase_ctx_app' C x c e P :
  Included _ (occurs_free (C |[ Ecase x ((c, e) :: P)]|))
           (Union _ (occurs_free  e) (occurs_free (C |[ Ecase x P ]|))).
Proof. 
  now apply occurs_free_Ecase_ctx_app_mut'.
Qed.

(** ** Closed expressions *)

(** An expression is closed if it has no free variables *)
Definition closed_exp (e : exp) : Prop :=
  Same_set var (occurs_free e) (Empty_set var).

Definition closed_fundefs (defs : fundefs) : Prop :=
  Same_set var (occurs_free_fundefs defs) (Empty_set var).

Lemma same_split_fds_closed_fundefs B1 B2 B3 B3' :
  split_fds B1 B2 B3 ->
  split_fds B1 B2 B3' ->
  closed_fundefs B3 -> closed_fundefs B3'.
Proof.
  intros Hspl1 Hspl2 Hcl. unfold closed_fundefs in *.
  rewrite split_fds_same_occurs_free_fundefs_Same_set; eauto.
Qed.

Lemma split_fds_closed_fundefs B1 B2 B3 :
  split_fds B1 B2 B3 ->
  closed_fundefs B1 ->
  closed_fundefs B2 ->
  closed_fundefs B3.
Proof with eauto with Ensembles_DB.
  intros H1 H2 H3. unfold closed_fundefs in *.
  rewrite split_fds_occurs_free_fundefs; eauto.
  rewrite H2, H3...
Qed.

(** * Function blocks defined inside in expressions and function blocks *)

(** [funs_in_exp B e] iff [B] is a block of functions in [e] *)
Inductive funs_in_exp : fundefs -> exp -> Prop :=
| In_Econstr :
    forall fs e x t ys,
      funs_in_exp fs e ->
      funs_in_exp fs (Econstr x t ys e)
| In_Case :
    forall fs x c e P,
      funs_in_exp fs e ->
      List.In (c, e) P ->
      funs_in_exp fs (Ecase x P)
| In_Eproj :    
    forall fs e x tau N ys,
      funs_in_exp fs e ->
      funs_in_exp fs (Eproj x tau N ys e)
| In_Fun1 :
    forall fs e,
      funs_in_exp fs (Efun fs e)          
| In_Fun2 :
    forall fs fs' e,
      funs_in_exp fs e ->
      funs_in_exp fs (Efun fs' e)
| In_Fun3 :
    forall fs fs' e,
      funs_in_fundef fs fs' ->
      funs_in_exp fs (Efun fs' e)
| In_Eprim :
    forall fs e x p ys,
      funs_in_exp fs e ->
      funs_in_exp fs (Eprim x p ys e)
with funs_in_fundef : fundefs -> fundefs -> Prop :=
| In_Fcons1 :
    forall fs fs' x tau ys e,
      funs_in_exp fs e -> 
      funs_in_fundef fs (Fcons x tau ys e fs')
| In_Fcons2 :
    forall fs fs' x tau ys e,
      funs_in_fundef fs fs' ->
      funs_in_fundef fs (Fcons x tau ys e fs').

Hint Constructors funs_in_exp.
Hint Constructors funs_in_fundef.

Lemma split_fds_funs_in_fundef_l B1 B2 B3 B :
  split_fds B1 B2 B3 ->
  funs_in_fundef B B1 ->
  funs_in_fundef B B3.
Proof.
  intros Hsp Hf. induction Hsp.
  - inv Hf. constructor; eauto.
    constructor 2; eauto.
  - constructor 2; eauto.
  - inv Hf.
Qed.

Lemma split_fds_funs_in_fundef_r B1 B2 B3 B :
  split_fds B1 B2 B3 ->
  funs_in_fundef B B2 ->
  funs_in_fundef B B3.
Proof.
  intros Hsp Hf. induction Hsp.
  - constructor 2; eauto.
  - inv Hf. constructor; eauto.
    constructor 2; eauto.
  - inv Hf.
Qed.

Lemma funs_in_fundef_split_fds (B1 B2 B3 : fundefs) B :
  split_fds B1 B2 B3 ->
  funs_in_fundef B B3 ->
  funs_in_fundef B B1 \/ funs_in_fundef B B2.
Proof.
  intros H1 H2; induction H1; eauto.
  - inv H2.
    + left; eauto.
    + destruct IHsplit_fds; eauto.
  - inv H2.
    + right; eauto.
    + destruct IHsplit_fds; eauto.
Qed.

(** ** Closed functions in expressions *)

(** All functions defined in an expression are closed *)
Definition closed_fundefs_in_exp (e : exp) :=
  forall defs, funs_in_exp defs e -> closed_fundefs defs.

(** All nested functions defined in a function block are closed *)
Definition closed_fundefs_in_fundefs (B : fundefs) := 
  forall B' : fundefs, funs_in_fundef B' B -> closed_fundefs B'.


(** * Bound variables *)

(** bound variables - alternative definition without lists or number of occurences *)
Inductive bound_var : exp -> Ensemble var :=
| Bound_Econstr1 :
    forall x t ys e,
      bound_var (Econstr x t ys e) x
| Bound_Econstr2 :
    forall y x t ys e,
      bound_var e y ->
      bound_var (Econstr x t ys e) y
| Bound_Eproj1 :
    forall x y tau n e,
      bound_var (Eproj x tau n y e) x
| Bound_Eproj2 :
    forall y x tau n y' e,
      bound_var e y ->
      bound_var (Eproj x tau n y' e) y
| Bound_Ecase :
    forall x y c e B,
      bound_var e y ->
      List.In (c, e) B ->
      bound_var (Ecase x B) y
| Bound_Efun1 :
    forall y defs e,
      bound_var_fundefs defs y ->
      bound_var (Efun defs e) y
| Bound_Efun2 :
    forall y defs e,
      bound_var e y ->
      bound_var (Efun defs e) y
| Bound_Eprim1 :
    forall x p ys e,
      bound_var (Eprim x p ys e) x
| Bound_Eprim2 :
    forall y x p ys e,
      bound_var e y ->
      bound_var (Eprim x p ys e) y
with bound_var_fundefs : fundefs -> Ensemble var :=
| Bound_Fcons1 :
    forall x f tau ys e defs,
      Ensembles.In var (Union var (Singleton var f) (FromList ys)) x ->
      bound_var_fundefs (Fcons f tau ys e defs) x
| Bound_Fcons2 :
    forall x f tau ys e defs,
      bound_var_fundefs defs x ->
      bound_var_fundefs (Fcons f tau ys e defs) x
| Bound_Fcons3 :
    forall x f tau ys e defs,
      bound_var e x ->
      bound_var_fundefs (Fcons f tau ys e defs) x.

Hint Constructors bound_var.
Hint Constructors bound_var_fundefs.

(** ** Useful set equalities *)

Lemma bound_var_Econstr x t ys e :
  Same_set _ (bound_var (Econstr x t ys e))
           (Union var (bound_var e) (Singleton _ x)).
Proof.
  split; intros x' H; inv H; eauto. inv H0; eauto.
Qed.

Lemma bound_var_Eproj x tau t y e :
  Same_set _ (bound_var (Eproj x tau t y e))
           (Union var (bound_var e) (Singleton _ x)).
Proof.
  split; intros x' H; inv H; eauto. inv H0; eauto.
Qed.

Lemma bound_var_Eprim x f y e :
  Same_set _ (bound_var (Eprim x f y e))
           (Union var (bound_var e) (Singleton _ x)).
Proof.
  split; intros x' H; inv H; eauto. inv H0; eauto.
Qed.

Lemma bound_var_Eapp f ft ys :
  Same_set _ (bound_var (Eapp f ft ys))
           (Empty_set var).
Proof.
  split; intros x' H; inv H; eauto.
Qed.

Lemma bound_var_Ecase_nil x  :
  Same_set _ (bound_var (Ecase x []))
           (Empty_set var).
Proof.
  split; intros x' H; inv H; eauto. inv H4.
Qed.

Lemma bound_var_Ecase_cons x c e P :
  Same_set _ (bound_var (Ecase x ((c, e) :: P)))
           (Union var (bound_var e) (bound_var (Ecase x P))).
Proof.
  split; intros x' H; inv H; eauto.
  - inv H4; eauto. inv H; eauto.
  - econstructor; eauto. left. eauto.
  - inv H0. econstructor; eauto. right. eauto.
Qed.

Lemma bound_var_Ecase_app x P1 P2 :
  Same_set _ (bound_var (Ecase x (P1 ++ P2)))
           (Union var (bound_var (Ecase x P1)) (bound_var (Ecase x P2))).
Proof with eauto with Ensembles_DB.
  induction P1 as [ | [c e] P1 IHP1]; simpl; eauto.
  - rewrite bound_var_Ecase_nil...
  - rewrite !bound_var_Ecase_cons, IHP1...
Qed.


Lemma bound_var_Efun B e :
  Same_set var (bound_var (Efun B e))
           (Union var (bound_var_fundefs B) (bound_var e)).
Proof.
  split; intros x H; inv H; eauto.
Qed.

Lemma bound_var_fundefs_Fcons f tau xs e B1 :
  Same_set var (bound_var_fundefs (Fcons f tau xs e B1))
           (Union var (Singleton var f)
                  (Union var (FromList xs)
                         (Union var (bound_var e) (bound_var_fundefs B1)))).
Proof with eauto with Ensembles_DB.
  split; intros x H; inv H; eauto.
  - inv H6; eauto.
  - inv H0; eauto.
    inv H; now eauto.
Qed.

Lemma bound_var_Ehalt x :
  Same_set _ (bound_var (Ehalt x)) (Empty_set _).
Proof.
  split; intros x' H; inv H.
Qed.

Lemma bound_var_fundefs_Fnil  :
  Same_set var (bound_var_fundefs Fnil) (Empty_set var).
Proof.
  split; intros x H; inv H; eauto.
Qed.

Ltac normalize_bound_var :=
  match goal with
    | [|- context[bound_var (Econstr _ _ _ _)]] =>
      rewrite bound_var_Econstr
    | [|- context[bound_var (Eproj _ _ _ _ _)]] =>
      rewrite bound_var_Eproj
    | [|- context[bound_var (Ecase _ [])]] =>
      rewrite bound_var_Ecase_nil
    | [|- context[bound_var (Ecase _ (_ :: _))]] =>
      rewrite bound_var_Ecase_cons
    | [|- context[bound_var (Ecase _ (_ ++ _))]] =>
      rewrite bound_var_Ecase_app
    | [|- context[bound_var (Efun _ _)]] =>
      rewrite bound_var_Efun
    | [|- context[bound_var (Eapp _ _ _)]] =>
      rewrite bound_var_Eapp
    | [|- context[bound_var (Eprim _ _ _ _)]] =>
      rewrite bound_var_Eprim
    | [|- context[bound_var (Ehalt _)]] =>
      rewrite bound_var_Ehalt
    | [|- context[bound_var_fundefs (Fcons _ _ _ _ _)]] =>
       rewrite bound_var_fundefs_Fcons
    | [|- context[bound_var_fundefs Fnil]] =>
      rewrite bound_var_fundefs_Fnil
  end.

Ltac normalize_bound_var_in_ctx :=
  match goal with
    | [ H : context[bound_var (Econstr _ _ _ _)] |- _ ] =>
      rewrite bound_var_Econstr in H
    | [ H : context[bound_var (Eproj _ _ _ _ _)]  |- _ ] =>
      rewrite bound_var_Eproj in H
    | [ H : context[bound_var (Ecase _ [])] |- _ ] =>
      rewrite bound_var_Ecase_nil in H
    | [ H : context[bound_var (Ecase _ (_ :: _))] |- _ ] =>
      rewrite bound_var_Ecase_cons in H
    | [ H : context[bound_var (Ecase _ (_ ++ _))] |- _ ] =>
      rewrite bound_var_Ecase_app in H
    | [ H : context[bound_var (Efun _ _)] |- _ ] =>
      rewrite bound_var_Efun in H
    | [ H : context[bound_var (Eapp _ _ _)] |- _ ] =>
      rewrite bound_var_Eapp in H
    | [ H : context[bound_var (Eprim _ _ _ _)] |- _ ] =>
      rewrite bound_var_Eprim in H
    | [ H : context[bound_var (Ehalt _)] |- _ ] =>
      rewrite bound_var_Ehalt
    | [ H : context[bound_var_fundefs (Fcons _ _ _ _ _)] |- _ ] =>
       rewrite bound_var_fundefs_Fcons in H
    | [ H : context[bound_var_fundefs Fnil] |- _ ] =>
      rewrite bound_var_fundefs_Fnil in H
  end.


Lemma name_in_fundefs_bound_var_fundefs B :
  Included var (name_in_fundefs B) (bound_var_fundefs B).
Proof with eauto with Ensembles_DB.
  induction B; simpl... normalize_bound_var...
Qed.

Lemma name_in_fundefs_bound_var_Efun B2 e :
  Included var (name_in_fundefs B2) (bound_var (Efun B2 e)).
Proof.
  normalize_bound_var. apply Included_Union_preserv_l.
  now eapply name_in_fundefs_bound_var_fundefs.
Qed.


Lemma split_fds_bound_vars B1 B2 B3 :
  split_fds B1 B2 B3 ->
  Same_set var (bound_var_fundefs B3)
           (Union var (bound_var_fundefs B1) (bound_var_fundefs B2)).
Proof with eauto 6 with Ensembles_DB.
  intros Hspl. induction Hspl; simpl; repeat normalize_bound_var.
  - rewrite IHHspl. rewrite !Union_assoc...
  - rewrite IHHspl...
  - do 3 rewrite bound_var_fundefs_Fnil at 1...
 Qed.

Lemma fundefs_append_bound_vars B1 B2 B3 :
  fundefs_append B1 B2 = B3 ->
  Same_set var (bound_var_fundefs B3)
           (Union var (bound_var_fundefs B1) (bound_var_fundefs B2)).
Proof.
  intros H. eapply split_fds_bound_vars. eapply fundefs_append_split_fds; eauto.
Qed.

Lemma bound_var_comp_mut :
  (forall c e e', Same_set _ (bound_var e) (bound_var e') ->
                  Same_set _ (bound_var (c |[ e ]|))
                           (bound_var (c |[ e' ]|))) /\
  (forall B e e', Same_set _ (bound_var e) (bound_var e') ->
                  Same_set _ (bound_var_fundefs (B <[ e ]>))
                           (bound_var_fundefs (B <[ e' ]>))).
Proof.
  exp_fundefs_ctx_induction IHc IHf; eauto; simpl;
  try now (intros e1 e2 H; repeat normalize_bound_var;
           eauto with Ensembles_DB).
Qed.

Corollary bound_var_comp c e e' :
  Same_set _ (bound_var e) (bound_var e') ->
  Same_set _ (bound_var (c |[ e ]|)) (bound_var (c |[ e' ]|)).
Proof.
  apply bound_var_comp_mut.
Qed.

Corollary bound_var_fundefs_comp B e e' :
   Same_set _ (bound_var e) (bound_var e') ->
   Same_set _ (bound_var_fundefs (B <[ e ]>))
            (bound_var_fundefs (B <[ e' ]>)).
Proof.
  apply bound_var_comp_mut.
Qed.

Lemma bound_var_ctx_app_Ecase_cons_mut :
  (forall C x c e P,
     Same_set _ (bound_var (C |[ Ecase x ((c, e) :: P) ]|))
              (Union _ (bound_var e) (bound_var (C |[ Ecase x P ]|)))) /\
  (forall Cf x c e P,
     Same_set _ (bound_var_fundefs (Cf <[ Ecase x ((c, e) :: P) ]>))
              (Union _ (bound_var e) (bound_var_fundefs (Cf <[ Ecase x P ]>)))).
Proof. 
  exp_fundefs_ctx_induction IHe IHB; intros;
  simpl; repeat normalize_bound_var;
  try now (try rewrite IHe; try rewrite IHB; eauto 6 with Ensembles_DB).
Qed.

Corollary bound_var_ctx_app_Ecase_cons C x c e P :
  Same_set _ (bound_var (C |[ Ecase x ((c, e) :: P) ]|))
           (Union _ (bound_var e) (bound_var (C |[ Ecase x P ]|))).
Proof.     
  now apply bound_var_ctx_app_Ecase_cons_mut.
Qed.

Corollary bound_var_fundefs_ctx_app_Ecase_cons Cf x c e P :
  Same_set _ (bound_var_fundefs (Cf <[ Ecase x ((c, e) :: P) ]>))
           (Union _ (bound_var e) (bound_var_fundefs (Cf <[ Ecase x P ]>))).
Proof.     
  now apply bound_var_ctx_app_Ecase_cons_mut.
Qed.

(** ** Lemmas about the union of free and bound variables *)

Lemma bound_var_occurs_free_Econstr_Included x t ys e :
  Included _ (Union _ (bound_var e) (occurs_free e))
           (Union _ (bound_var (Econstr x t ys e))
                  (occurs_free (Econstr x t ys e))).
Proof with eauto with Ensembles_DB.
  repeat normalize_bound_var. repeat normalize_occurs_free.
  rewrite <- Union_assoc.
  apply Included_Union_compat...
  eapply Included_trans. now apply occurs_free_Econstr_Included with (t := t).
  normalize_occurs_free...
Qed.

Lemma bound_var_occurs_free_Ecase_Included c e x P:
  List.In (c, e) P ->
  Included _ (Union _ (bound_var e) (occurs_free e))
           (Union _ (bound_var (Ecase x P))
                  (occurs_free (Ecase x P))).
Proof.
  intros Hin x' Hin'. inv Hin'.
  now left; eauto.
  right. eapply occurs_free_Ecase_Included; now eauto.
Qed.

Lemma bound_var_occurs_free_Ecase_cons_Included c e x P:
  Included _ (Union _ (bound_var (Ecase x P))
                    (occurs_free (Ecase x P)))
           (Union _ (bound_var (Ecase x ((c, e) :: P)))
                  (occurs_free (Ecase x ((c, e) :: P)))).
Proof with eauto with Ensembles_DB.
  repeat normalize_occurs_free. repeat normalize_bound_var...
Qed.

Lemma bound_var_occurs_free_Eproj_Included x tau N y e :
  Included _ (Union _ (bound_var e) (occurs_free e))
           (Union _ (bound_var (Eproj x tau N y e))
                  (occurs_free (Eproj x tau N y e))).
Proof with eauto with Ensembles_DB.
  repeat normalize_occurs_free. repeat normalize_bound_var.
  rewrite <- Union_assoc.
  apply Included_Union_compat...
  eapply Included_trans.
  now apply occurs_free_Eproj_Included with (tau := tau) (t := N).
  normalize_occurs_free...
Qed.

Lemma bound_var_occurs_free_Efun_Included B e :
  Included _ (Union _ (bound_var e) (occurs_free e))
           (Union _ (bound_var (Efun B e))
                  (occurs_free (Efun B e))).
Proof with eauto with Ensembles_DB.
  repeat normalize_occurs_free. repeat normalize_bound_var.
  rewrite (Union_commut _ (bound_var e)), <- Union_assoc.
  apply Included_Union_compat. now apply Included_refl. 
  eapply Included_trans. now apply occurs_free_Efun_Included.
  rewrite Union_commut. apply Included_Union_compat.
  now apply name_in_fundefs_bound_var_fundefs.
  normalize_occurs_free...
Qed.

Lemma bound_var_occurs_free_fundefs_Efun_Included B e :
  Included _ (Union _ (bound_var_fundefs B) (occurs_free_fundefs B))
           (Union _ (bound_var (Efun B e))
                  (occurs_free (Efun B e))).
Proof with eauto with Ensembles_DB.
  repeat normalize_occurs_free. repeat normalize_bound_var...
Qed.

Lemma bound_var_occurs_free_Eprim_Included x f ys e :
  Included _ (Union _ (bound_var e) (occurs_free e))
           (Union _ (bound_var (Eprim x f ys e))
                  (occurs_free (Eprim x f ys e))).
Proof with eauto with Ensembles_DB.
  repeat normalize_occurs_free. repeat normalize_bound_var.
  rewrite <- Union_assoc.
  apply Included_Union_compat...
  eapply Included_trans.
  now apply occurs_free_Eprim_Included with (f := f).
  normalize_occurs_free...
Qed.

Lemma bound_var_occurs_free_Fcons_Included v t l e B :
  Included var (Union var (bound_var e) (occurs_free e))
           (Union var (bound_var_fundefs (Fcons v t l e B))
                  (occurs_free_fundefs (Fcons v t l e B))).
Proof.
  rewrite bound_var_fundefs_Fcons.
  rewrite !Union_assoc,
  Union_commut with (s2 := FromList l), Union_commut with (s2 := bound_var e), <- !Union_assoc.
  apply Included_Union_compat. now apply Included_refl.
  eapply Included_trans. eapply occurs_free_in_fun with (B := Fcons v t l e B).
  econstructor. now eauto. apply Included_Union_compat. now apply Included_refl. 
  simpl. rewrite <- Union_assoc. apply Included_Union_compat. now apply Included_refl. 
  apply Included_Union_compat; [| now apply Included_refl ].
  now eapply name_in_fundefs_bound_var_fundefs.
Qed.

Lemma bound_var_occurs_free_fundefs_Fcons_Included v t l e B :
  Included var (Union var (bound_var_fundefs B) (occurs_free_fundefs B))
           (Union var (bound_var_fundefs (Fcons v t l e B))
                  (occurs_free_fundefs (Fcons v t l e B))).
Proof.
  normalize_bound_var. normalize_occurs_free.
  rewrite !Union_assoc, Union_commut with (s2 := bound_var_fundefs B), <- !Union_assoc. 
  apply Included_Union_compat. now apply Included_refl.
  rewrite Union_commut with (s1 := Singleton _ _) , <- !Union_assoc.
  rewrite <- Union_Setminus; eauto with Ensembles_DB typeclass_instances.
Qed.  

(** Unique bindings - alternative definition without lists *)
Inductive unique_bindings : exp -> Prop :=
| UBound_Econstr :
    forall x t ys e,
      ~ (bound_var e) x ->
      unique_bindings e ->
      unique_bindings (Econstr x t ys e)
| UBound_Eproj :
    forall x tau n y e,
      ~ (bound_var e) x ->
      unique_bindings e ->
      unique_bindings (Eproj x tau n y e)
| UBound_Ecase1 :
    forall x,
      unique_bindings (Ecase x [])
| UBound_Ecase2 :
    forall x c e P,
      unique_bindings (Ecase x P) ->
      unique_bindings e ->
      Disjoint var (bound_var e) (bound_var (Ecase x P)) ->
      unique_bindings (Ecase x ((c, e) :: P))
| UBound_Efun :
    forall defs e,
      unique_bindings e ->
      unique_bindings_fundefs defs ->
      Disjoint var (bound_var e) (bound_var_fundefs defs) ->
      unique_bindings (Efun defs e)
| UBound_Eapp :
    forall f t xs,
      unique_bindings (Eapp f t xs)
| UBound_Eprim :
    forall x p ys e,
      ~ (bound_var e) x ->
      unique_bindings e ->
      unique_bindings (Eprim x p ys e)
| UBound_Ehalt :
    forall x, unique_bindings (Ehalt x)
with unique_bindings_fundefs : fundefs -> Prop :=
| UBound_Fcons :
    forall f tau ys e defs,
      ~ (bound_var e) f ->
      ~ (bound_var_fundefs defs) f ->
      Disjoint var (bound_var e) (FromList ys) ->
      Disjoint var (bound_var_fundefs defs) (FromList ys) ->
      Disjoint var (bound_var e) (bound_var_fundefs defs) ->
      ~ FromList ys f ->
      NoDup ys ->
      unique_bindings e ->
      unique_bindings_fundefs defs ->
      unique_bindings_fundefs (Fcons f tau ys e defs)
| UBound_Fnil :
    unique_bindings_fundefs Fnil.

(** Uniqueness of names in a block of functions *)
Inductive unique_functions : fundefs -> Prop :=
| Fnil_un :
    unique_functions Fnil
| Fcons_un :
    forall f tau xs e B,
      unique_functions B ->
      ~ Ensembles.In _ (name_in_fundefs B) f ->
      unique_functions (Fcons f tau xs e B).

Definition fundefs_names_unique (e : exp) : Prop :=
  forall B, funs_in_exp B e -> unique_functions B.

Definition fundefs_names_unique_fundefs (B : fundefs) : Prop :=
  forall B', funs_in_fundef B' B \/ B' = B -> unique_functions B'.

Lemma unique_bindings_fundefs_unique_functions B :
  unique_bindings_fundefs B ->
  unique_functions B.
Proof.
  intros H; induction H; constructor; eauto.
  intros Hin. eapply H0. now apply name_in_fundefs_bound_var_fundefs.
Qed.

Lemma unique_bindings_Ecase_l x P1 c e P2 :
  unique_bindings (Ecase x (P1 ++ ((c, e) :: P2))) ->
  unique_bindings e /\
  unique_bindings (Ecase x P1) /\  unique_bindings (Ecase x P2) /\
  Disjoint var (bound_var (Ecase x P1)) (bound_var e) /\
  Disjoint var (bound_var (Ecase x P2)) (bound_var e) /\
  Disjoint var (bound_var (Ecase x P1)) (bound_var (Ecase x P2)).
Proof with eauto with Ensembles_DB.
  intros H. induction P1.
  - inv H. split; [ assumption |].
    split; [now constructor |]. split; [assumption |].
    split.
    + normalize_bound_var...
    + split... normalize_bound_var...
  - inv H. destruct (IHP1 H3) as [H1' [H2' [H3' [H4' [H5' H6']]]]].
    split; [ assumption |].
    split.
    + constructor; [ assumption | assumption |].
      repeat normalize_bound_var_in_ctx...
    + split; [ assumption |]. split.
      * repeat normalize_bound_var_in_ctx.
        normalize_bound_var...
      * split; [ assumption |].
        repeat normalize_bound_var_in_ctx.
        normalize_bound_var...
Qed.

Lemma unique_bindings_Ecase_r x P1 c e P2 :
  unique_bindings e ->
  unique_bindings (Ecase x P1) ->
  unique_bindings (Ecase x P2) ->
  Disjoint var (bound_var (Ecase x P1)) (bound_var e) ->
  Disjoint var (bound_var (Ecase x P2)) (bound_var e) ->
  Disjoint var (bound_var (Ecase x P1)) (bound_var (Ecase x P2)) ->
  unique_bindings (Ecase x (P1 ++ ((c, e) :: P2))).
Proof with eauto with Ensembles_DB.
  intros H1 H2 H3 H4 H5 H6. induction P1 as [| [c' e'] P1 IHP1].
  - constructor; [assumption | assumption |]...
  - inv H2. repeat normalize_bound_var_in_ctx.
    simpl. clear H5. constructor; [| eassumption |].
    * now eauto with Ensembles_DB.
    * repeat normalize_bound_var... 
Qed.

Lemma unique_bindings_ctx_app_Ecase_cons_mut :
  (forall C x c e P
     (Hun1 : unique_bindings e)
     (Hun2 : unique_bindings (C |[ Ecase x P ]|))
     (Hd : Disjoint _ (bound_var e) (bound_var (C |[ Ecase x P ]|))),
     unique_bindings (C |[ Ecase x ((c, e) :: P) ]|)) /\
  (forall Cf x c e P
     (Hun1 : unique_bindings e)
     (Hun2 : unique_bindings_fundefs (Cf <[ Ecase x P ]>))
     (Hd : Disjoint _ (bound_var e) (bound_var_fundefs (Cf <[ Ecase x P ]>))),
     unique_bindings_fundefs (Cf <[ Ecase x ((c, e) :: P) ]>)).
Proof with now eauto with Ensembles_DB. 
  exp_fundefs_ctx_induction IHe IHB; intros; simpl in *;
  try now (inv Hun2; repeat normalize_bound_var_in_ctx;
           constructor; [| now eauto with Ensembles_DB ];
           intros Hc; eapply bound_var_ctx_app_Ecase_cons in Hc;
           (inv Hc; [ | now  eauto ]); eapply Hd; eauto).
  - constructor; eassumption.
  - eapply unique_bindings_Ecase_l in Hun2.
    repeat normalize_bound_var_in_ctx.      
    destruct Hun2 as [Hun1' [Hun2' [Hun3' [Hd1 [Hd2 Hd3]]]]].
    eapply unique_bindings_Ecase_r; try eassumption.
    eapply IHe; eauto with Ensembles_DB.
    rewrite bound_var_ctx_app_Ecase_cons...
    rewrite bound_var_ctx_app_Ecase_cons...
  - inv Hun2; repeat normalize_bound_var_in_ctx.
    constructor. now eauto with Ensembles_DB.
    eassumption. rewrite bound_var_ctx_app_Ecase_cons...
  - inv Hun2; repeat normalize_bound_var_in_ctx.
    constructor. eassumption.
    now eauto with Ensembles_DB.
    rewrite bound_var_fundefs_ctx_app_Ecase_cons...
  - inv Hun2; repeat normalize_bound_var_in_ctx.
    constructor;
      try rewrite bound_var_ctx_app_Ecase_cons; try now eauto with Ensembles_DB.
    intros Hc. eapply bound_var_ctx_app_Ecase_cons in Hc.
    inv Hc; [ | now  eauto ]; eapply Hd; eauto.
  - inv Hun2; repeat normalize_bound_var_in_ctx.
    constructor;
      try rewrite bound_var_fundefs_ctx_app_Ecase_cons; try now eauto with Ensembles_DB.
    intros Hc. eapply bound_var_fundefs_ctx_app_Ecase_cons in Hc.
    inv Hc; [ | now  eauto ]; eapply Hd; eauto.
Qed.


Lemma unique_bindings_ctx_app_Ecase_cons :
  (forall C x c e P
     (Hun1 : unique_bindings e)
     (Hun2 : unique_bindings (C |[ Ecase x P ]|))
     (Hd : Disjoint _ (bound_var e) (bound_var (C |[ Ecase x P ]|))),
     unique_bindings (C |[ Ecase x ((c, e) :: P) ]|)).
Proof.
  now apply unique_bindings_ctx_app_Ecase_cons_mut.
Qed.


Lemma split_fds_unique_bindings_fundefs_l B1 B2 B3 :
  unique_bindings_fundefs B3 ->
  split_fds B1 B2 B3 ->
  unique_bindings_fundefs B1 /\ unique_bindings_fundefs B2 /\
  Disjoint var (bound_var_fundefs B1) (bound_var_fundefs B2).
Proof with eauto with Ensembles_DB.
  intros Hun Hspl. induction Hspl; simpl.
  - inv Hun. edestruct IHHspl as [H1 [H2 H3]]; eauto.
    erewrite (split_fds_bound_vars _ _ lrfds) in H8, H7; eauto.
    split; [| split; [ eassumption |] ].
    + constructor...
      intros Hc. apply H5. eapply split_fds_bound_vars; eauto.
    + normalize_bound_var.
      apply Union_Disjoint_l.
      eapply Disjoint_Singleton_l. intros Hc. eapply H5.
      now eapply split_fds_bound_vars; eauto.
      now eauto with Ensembles_DB.
  - inv Hun. edestruct IHHspl as [H1 [H2 H3]]; eauto.
    erewrite (split_fds_bound_vars _ _ lrfds) in H8, H7; eauto.
    split; [ eassumption | split; [ | ] ].
    + constructor...
      intros Hc. apply H5. eapply split_fds_bound_vars; eauto.
    + normalize_bound_var.
      apply Union_Disjoint_r.
      eapply Disjoint_Singleton_r. intros Hc. eapply H5.
      now eapply split_fds_bound_vars; eauto.
      now eauto with Ensembles_DB.
  - split. eassumption. split. eassumption.
    rewrite bound_var_fundefs_Fnil at 1...
Qed.

Lemma split_fds_unique_bindings_fundefs_r B1 B2 B3 :
  unique_bindings_fundefs B1 -> unique_bindings_fundefs B2 ->
  Disjoint var (bound_var_fundefs B1) (bound_var_fundefs B2) ->
  split_fds B1 B2 B3 ->
  unique_bindings_fundefs B3.
Proof with eauto with Ensembles_DB.
  intros Hun1 Hun2 HD Hspl. induction Hspl; simpl; repeat normalize_bound_var_in_ctx.
  - inv Hun1. constructor; eauto.
    + intros Hc. apply H5. 
      eapply (split_fds_bound_vars) in Hc; eauto. inv Hc; eauto.
      inv HD. exfalso. eapply H0. now eauto.
    + rewrite split_fds_bound_vars; [| eassumption ]...
    + rewrite split_fds_bound_vars; [| eassumption ]...
    + eapply IHHspl...
  - inv Hun2. constructor; eauto.
    + intros Hc. apply H5. 
      eapply (split_fds_bound_vars) in Hc; eauto. inv Hc; eauto.
      inv HD. exfalso. eapply H0. now eauto.
    + rewrite split_fds_bound_vars; [| eassumption ]...
    + rewrite split_fds_bound_vars; [| eassumption ]...
    + eapply IHHspl...
  - constructor.
Qed.

Lemma fundefs_append_unique_bindings_l B1 B2 B3 :
  unique_bindings_fundefs B3 ->
  fundefs_append B1 B2 = B3 ->
  unique_bindings_fundefs B1 /\
  unique_bindings_fundefs B2 /\
  Disjoint var (bound_var_fundefs B1) (bound_var_fundefs B2).
Proof.
  intros. edestruct split_fds_unique_bindings_fundefs_l; eauto.
  apply fundefs_append_split_fds; eauto.
Qed.

Lemma fundefs_append_unique_bindings_r B1 B2 B3 :
  fundefs_append B1 B2 = B3 ->
  unique_bindings_fundefs B1 ->
  unique_bindings_fundefs B2 ->
  Disjoint var (bound_var_fundefs B1) (bound_var_fundefs B2) ->
  unique_bindings_fundefs B3.
Proof.
  intros.
  eapply split_fds_unique_bindings_fundefs_r;
    [ apply H0 | | | ]; eauto.
  apply fundefs_append_split_fds; eauto.
Qed.

Lemma unique_bindings_funs_in_exp_mut :
  (forall e B, unique_bindings e ->
          funs_in_exp B e ->
          unique_bindings_fundefs B) /\
  (forall B B', unique_bindings_fundefs B ->
           funs_in_fundef B' B ->
           unique_bindings_fundefs B').
Proof.
  exp_defs_induction IHe IHl IHb; intros B Hun Hin; inv Hun; inv Hin; eauto.
  - inv H3. 
  - inv H6. inv H. now eauto.
    now eauto.
Qed.

Corollary unique_bindings_funs_in_exp e B :
  unique_bindings e ->
  funs_in_exp B e ->
  unique_bindings_fundefs B.
Proof.
  now eapply unique_bindings_funs_in_exp_mut.
Qed.

Corollary unique_bindings_fundefs_funs_in_fundefs B B':
  unique_bindings_fundefs B ->
  funs_in_fundef B' B ->
  unique_bindings_fundefs B'.
Proof.
  now apply unique_bindings_funs_in_exp_mut.
Qed.

Lemma fun_in_fundefs_Fcons_Disjoint f tau xs e B :
  unique_bindings_fundefs (Fcons f tau xs e B) ->
  ~ (name_in_fundefs B f).
Proof.
  intros Hun Hc. inv Hun.
  apply H5. now eapply name_in_fundefs_bound_var_fundefs.
Qed.

                    
Lemma fun_in_fundefs_unique_bindings_split f tau xs e B :
  fun_in_fundefs B (f, tau, xs, e) ->
  unique_bindings_fundefs B ->
  exists B1 B2,
    B = fundefs_append B1 (Fcons f tau xs e B2) /\
    ~ name_in_fundefs B1 f /\
    Same_set _ (Union _ (fun_in_fundefs B1) (fun_in_fundefs B2))
             (Setminus _ (fun_in_fundefs B) (Singleton _ (f, tau, xs, e))) /\
    unique_bindings_fundefs (fundefs_append B1 B2).
Proof with eauto with Ensembles_DB.
  intros H Hun. induction B.
  - simpl in H.
    destruct (var_dec v f); subst.
    + inv H. inv H0.
      * exists Fnil. eexists. split; simpl; eauto.
        split; try (now intros Hc; inv Hc). split; try (now inv Hun; eauto).
        rewrite Union_Empty_set_neut_l, Setminus_Union_distr,
        Setminus_Same_set_Empty_set, Union_Empty_set_neut_l.
        symmetry. eapply Setminus_Disjoint.
        apply Disjoint_Singleton_r. intros Hc.
        apply fun_in_fundefs_name_in_fundefs in Hc.
        eapply fun_in_fundefs_Fcons_Disjoint; eauto.
      * exfalso. inv Hun. apply H6. eapply name_in_fundefs_bound_var_fundefs.
        eapply fun_in_fundefs_name_in_fundefs; eauto.
    + inv H. inv H0. congruence. inv Hun; eauto.
      edestruct IHB as [B1 [B2 [Heq [Hn [Hs Hun']]]]]; eauto.
      edestruct fundefs_append_unique_bindings_l as [H1 [H2 H3]];
        [ apply H13 | | ]; eauto.
      exists (Fcons v f0 l e0 B1), B2. rewrite Heq. split; eauto.
      split; [| split ].
      * intros H. apply Hn. inv H; eauto. inv H4. congruence.
      * simpl. rewrite Setminus_Union_distr, <- Union_assoc.
        apply Same_set_Union_compat.
        apply Same_set_sym. eapply Setminus_Disjoint.
        apply Disjoint_Singleton_r. intros Hc. inv Hc. congruence.
        apply Same_set_sym. 
        rewrite fundefs_append_fun_in_fundefs; eauto. simpl.
        rewrite !Setminus_Union_distr, Setminus_Same_set_Empty_set,
        Union_Empty_set_neut_l, <- Setminus_Union_distr.
        eapply Setminus_Disjoint. apply Union_Disjoint_l.
        eapply Disjoint_Singleton_r. intros Hc. eapply H3.
        constructor. eapply name_in_fundefs_bound_var_fundefs.
        eapply fun_in_fundefs_name_in_fundefs; eauto.
        rewrite bound_var_fundefs_Fcons; left. eauto.
        eapply Disjoint_Singleton_r. intros Hc. inv H2. eapply H18.
        eapply name_in_fundefs_bound_var_fundefs.
        eapply fun_in_fundefs_name_in_fundefs; eauto.
      * simpl. constructor; eauto.
        intros H. apply H6. eapply fundefs_append_bound_vars; eauto.
        eapply fundefs_append_bound_vars in H; [| eauto ].
        rewrite bound_var_fundefs_Fcons. inv H; eauto.
        constructor. intros x Hc. eapply H8. inv Hc.
        constructor; eauto.
        rewrite fundefs_append_bound_vars in H; [| eauto ].
        eapply fundefs_append_bound_vars; eauto.
        rewrite bound_var_fundefs_Fcons. inv H; eauto.
        eapply Disjoint_Included_r; eauto.
        rewrite Heq, fundefs_append_bound_vars; eauto.
        rewrite (fundefs_append_bound_vars
                   B1 (Fcons f tau xs e B2)
                   (fundefs_append B1 (Fcons f tau xs e B2))); eauto.
        apply Included_Union_compat...
        normalize_bound_var...
  - inv H.
Qed.

Lemma find_def_Included_fun_in_fundefs f B B' :
  unique_bindings_fundefs B ->
  unique_bindings_fundefs B' ->
  Included _ (fun_in_fundefs B) (fun_in_fundefs B') ->
  name_in_fundefs B f ->
  find_def f B = find_def f B'.
Proof with eauto with Ensembles_DB.
  revert B'. induction B; simpl; intros B' Hun Hun' H Hn.
  - edestruct fun_in_fundefs_unique_bindings_split
      as [B1 [B1' [Heq [Hn' [HS' Hun1]]]]]; eauto.
    eapply H. left. eauto.
    rewrite Heq. destruct (M.elt_eq f v); subst.
    + erewrite find_def_fundefs_append_r.
      simpl; destruct (M.elt_eq v v); try congruence.
      simpl; destruct (M.elt_eq v v); try congruence. eauto.
      apply name_not_in_fundefs_find_def_None.
      intros Hc. apply Hn'; eauto.
    + rewrite find_def_fundefs_append_Fcons_neq; eauto. eapply IHB; eauto.
      inv Hun; eauto.
      rewrite (fundefs_append_fun_in_fundefs B1 B1' (fundefs_append B1 B1')); eauto.
      eapply Included_trans; [| inv HS'; eauto].
      rewrite <- (Setminus_Disjoint (fun_in_fundefs B) (Singleton _ (v, f0, l, e))).
      eapply Included_Setminus_compat...
      eapply Included_trans; [| eassumption ]...
      eapply Disjoint_Singleton_r. inv Hun; eauto. intros Hc. apply H6.
      apply name_in_fundefs_bound_var_fundefs.
      now eapply fun_in_fundefs_name_in_fundefs; eauto.
      inv Hn. inv H0; try congruence. eauto.
  - destruct B'; eauto. inv Hn.
Qed.

Lemma find_def_Same_set_fun_in_fundefs f B B' :
  unique_bindings_fundefs B ->
  unique_bindings_fundefs B' ->
  Same_set _ (fun_in_fundefs B) (fun_in_fundefs B') ->
  find_def f B = find_def f B'.
Proof.
  intros Hun1 Hun2 HS.
  destruct (@Dec _ _ (Decidable_name_in_fundefs B) f).
  - inv HS. eapply find_def_Included_fun_in_fundefs; eauto.
  - rewrite !name_not_in_fundefs_find_def_None; eauto.
    intros Hn. apply H.
    apply name_in_fundefs_big_cup_fun_in_fundefs in Hn.
    destruct Hn as [[[[f' t] xs] e] [H1 H2]]. inv H2.
    eapply fun_in_fundefs_name_in_fundefs. now eapply HS; eauto.
Qed.
  
Lemma unique_bindings_hoist B1 B2 B3 f tau xs e B B' :
  split_fds B1 (Fcons f tau xs (Efun B3 e) Fnil) B ->
  split_fds B1 (Fcons f tau xs e Fnil) B2 ->
  split_fds B3 B2 B' ->
  unique_bindings_fundefs B ->
  unique_bindings_fundefs B'.
Proof with now eauto with Ensembles_DB.
  intros Hsp1 Hsp2 Hsp3 Hun.
  edestruct split_fds_unique_bindings_fundefs_l as [H1 [H2 H3]]; eauto.
  assert (Hun2 : unique_bindings_fundefs B2).
  { eapply split_fds_unique_bindings_fundefs_r; [ | | | now apply Hsp2 ];
    eauto; repeat normalize_bound_var_in_ctx.
    - inv H2. inv H14. clear H10. repeat normalize_bound_var_in_ctx.
      constructor; eauto; repeat normalize_bound_var...
    - repeat normalize_bound_var... }
  edestruct split_fds_unique_bindings_fundefs_l as [H1' [H2' H3']]; eauto.
  eapply split_fds_unique_bindings_fundefs_r; [ | | | eauto]; eauto.
  inv H2. inv H14; eauto.
  rewrite (split_fds_bound_vars B1 (Fcons f tau xs e Fnil) B2); eauto.
  inv H2. inv H14. 
  repeat normalize_bound_var_in_ctx. repeat normalize_bound_var.
  clear H3' H11 H10.
  apply Union_Disjoint_r. eapply Disjoint_Included_l_sym; [| eassumption ]...
  apply Union_Disjoint_r...
Qed.

Lemma unique_bindings_split_fds_Fcons_fundefs_append B1 B2 B3 B f tau xs e  :
  split_fds B1 (Fcons f tau xs e Fnil) B3 ->
  split_fds B2 B3 B ->
  unique_bindings_fundefs B ->
  unique_bindings_fundefs (fundefs_append (Fcons f tau xs e B1) B2).
Proof with eauto with Ensembles_DB.
  intros H1 H2 Hun.
  edestruct split_fds_unique_bindings_fundefs_l as [H1' [H2' H3']];
  [| apply H2 |]; eauto.
  edestruct split_fds_unique_bindings_fundefs_l as [H4' [H5' H6']];
    [| apply H1 |]; eauto.
  eapply fundefs_append_unique_bindings_r; eauto.
  eapply fundefs_append_unique_bindings_r
  with (B1 := Fcons f tau xs e Fnil) (B2 := B1); eauto.
  inv H5'; eauto...
  rewrite bound_var_fundefs_Fcons.
  rewrite (split_fds_bound_vars B1 (Fcons f tau xs e Fnil) B3) in H3'; eauto.
  repeat normalize_bound_var_in_ctx.
  apply Union_Disjoint_l...
  apply Union_Disjoint_l...
  apply Union_Disjoint_l...  
Qed.

Lemma unique_bindings_split_fds_fundfes_append B1 B2 B3 :
  split_fds B1 B2 B3 ->
  unique_bindings_fundefs B3 ->
  unique_bindings_fundefs (fundefs_append B1 B2).
Proof.
  intros Hspl Hun.
  edestruct split_fds_unique_bindings_fundefs_l as [H1 [H2 H3]]; eauto.
  eapply fundefs_append_unique_bindings_r; eauto.
Qed.

Lemma split_fds_fundefs_append_fun_in_fundefs B1 B2 B3 B4 B : 
  split_fds B1 B2 B4 ->
  split_fds B3 B4 B ->
  Same_set _ (fun_in_fundefs (fundefs_append (fundefs_append B2 B1) B3))
           (fun_in_fundefs B).
Proof with eauto with Ensembles_DB.
  intros H1 H2.
  rewrite (split_fds_fun_in_fundefs B3 B4 B); eauto;
  rewrite (split_fds_fun_in_fundefs B1 B2 B4); eauto.
  rewrite (fundefs_append_fun_in_fundefs (fundefs_append B2 B1) B3); eauto.
  rewrite (fundefs_append_fun_in_fundefs B2 B1); eauto.
  rewrite <-!Union_assoc...
Qed.

Lemma find_def_split_fds f B1 B2 B3 B3' :
  split_fds B1 B2 B3 ->
  split_fds B1 B2 B3' ->
  unique_bindings_fundefs B3 ->
  find_def f B3 = find_def f B3'.
Proof.
  intros Hspl1 Hspl2 Hun.
  edestruct split_fds_unique_bindings_fundefs_l as [H1 [H2 H3]]; eauto.
  specialize (split_fds_unique_bindings_fundefs_r _ _ _ H1 H2 H3 Hspl2).
  clear H1 H2 H3.
  revert B3' Hspl2. induction Hspl1; intros B3' Hspl2 Hun'.
  - simpl. destruct (M.elt_eq f v); subst.
    + edestruct split_fds_cons_l_append_fundefs as [B1' [B2' [Heq Hspl3]]]; eauto.
      erewrite Heq, find_def_fundefs_append_r;
        try (now simpl; destruct (M.elt_eq v v); try congruence; eauto).
      eapply name_not_in_fundefs_find_def_None. intros Hc.
      symmetry in Heq. apply fundefs_append_split_fds in Heq.
      edestruct split_fds_unique_bindings_fundefs_l as [H1 [H2 H3]]; eauto.
      eapply H3. constructor; eauto. apply name_in_fundefs_bound_var_fundefs; now eauto.
    + edestruct split_fds_cons_l_append_fundefs as [B1' [B2' [Heq Hspl3]]]; eauto.
      erewrite Heq. rewrite find_def_fundefs_append_Fcons_neq; eauto.
      inv Hun. apply IHHspl1; eauto.
      edestruct split_fds_unique_bindings_fundefs_l as [H1 [H2 H3]];
        [| apply Hspl1 |]; eauto.
      now specialize (split_fds_unique_bindings_fundefs_r _ _ _ H1 H2 H3 Hspl3).
  - simpl. destruct (M.elt_eq f v); subst.
    + edestruct split_fds_cons_r_append_fundefs as [B1' [B2' [Heq Hspl3]]]; eauto.
      erewrite Heq, find_def_fundefs_append_r;
        try (now simpl; destruct (M.elt_eq v v); try congruence; eauto).
      eapply name_not_in_fundefs_find_def_None. intros Hc.
      symmetry in Heq. apply fundefs_append_split_fds in Heq.
      edestruct split_fds_unique_bindings_fundefs_l as [H1 [H2 H3]]; eauto.
      eapply H3. constructor; eauto. apply name_in_fundefs_bound_var_fundefs; eauto.
    + edestruct split_fds_cons_r_append_fundefs as [B1' [B2' [Heq Hspl3]]]; eauto.
      erewrite Heq. rewrite find_def_fundefs_append_Fcons_neq; eauto.
      inv Hun. apply IHHspl1; eauto.
      edestruct split_fds_unique_bindings_fundefs_l as [H1 [H2 H3]];
        [| apply Hspl1 |]; eauto.
      now specialize (split_fds_unique_bindings_fundefs_r _ _ _ H1 H2 H3 Hspl3).
  - inv Hspl2; eauto.
Qed.

Lemma unique_bindings_ctx_mut :
  (forall c e e', unique_bindings (c |[ e ]|) -> unique_bindings e' ->
                  Same_set _ (bound_var e) (bound_var e') ->
                  unique_bindings (c |[ e' ]|)) /\
  (forall B e e', unique_bindings_fundefs (B <[ e ]>) -> unique_bindings e' ->
                  Same_set _ (bound_var e) (bound_var e') ->
                  unique_bindings_fundefs (B <[ e' ]>)).
Proof with eauto with Ensembles_DB.
  exp_fundefs_ctx_induction IHc IHf; eauto; simpl; eauto;
  try (intros e1 e2 Hun Hun' HS;
       inv Hun; constructor; [| now eauto ];
       intros Hc; apply H1;
       eapply bound_var_comp; eassumption).
  - intros l' e1 e2 Hun Hun' HS.
    edestruct unique_bindings_Ecase_l as [H1' [H2' [H3' [H4' [H5' H6']]]]].
    eassumption.
    eapply unique_bindings_Ecase_r; try eassumption.
    + eapply IHc; eassumption.
    + rewrite bound_var_comp. eassumption. now symmetry.
    + rewrite bound_var_comp. eassumption. now symmetry.
  - intros e1 e2 Hun Hun' HS.
    inv Hun. constructor; [| eassumption |].
    eapply IHc; eassumption.
    rewrite bound_var_comp. eassumption. now symmetry.
  - intros e1 e2 Hun Hun' HS.
    inv Hun. constructor; [eassumption | |].
    eapply IHf; eassumption.
    rewrite bound_var_fundefs_comp. eassumption. now symmetry.
  - intros e1 e2 Hun Hun' HS.
    inv Hun. constructor; try eassumption.
    + intros Hc. apply H4.
      eapply bound_var_comp; eassumption.
    + rewrite bound_var_comp. eassumption. now symmetry.
    + rewrite bound_var_comp. eassumption. now symmetry.
    + eapply IHc; eassumption.
  - intros e1 e2 Hun Hun' HS.
    inv Hun. constructor; try eassumption.
    + intros Hc. apply H5.
      eapply bound_var_fundefs_comp; eassumption.
    + rewrite bound_var_fundefs_comp. eassumption. now symmetry.
    + rewrite bound_var_fundefs_comp. eassumption. now symmetry.
    + eapply IHf; eassumption.
Qed.

Lemma unique_bindings_ctx c e e':
  unique_bindings (c |[ e ]|) -> unique_bindings e' ->
  Same_set _ (bound_var e) (bound_var e') ->
  unique_bindings (c |[ e' ]|).
Proof.
  eapply unique_bindings_ctx_mut.
Qed.

Lemma unique_bindings_fundefs_ctx B e e':
  unique_bindings_fundefs (B <[ e ]>) -> unique_bindings e' ->
  Same_set _ (bound_var e) (bound_var e') ->
  unique_bindings_fundefs (B <[ e' ]>).
Proof.
  eapply unique_bindings_ctx_mut.
Qed.


(** * Free variables, computational definitions *)

(** The set of names of the functions in the same fix definition,
  * computational definition *)
Fixpoint fundefs_names (defs : fundefs) : FVSet :=
  match defs with
    | Fcons f _ _ _ defs' => add f (fundefs_names defs') 
    | Fnil => empty
  end.

(** The set of free variables of an [exp], computational definition *)
Fixpoint exp_fv (e : exp) : FVSet :=
  match e with
    | Econstr x c ys e =>
      let set := remove x (exp_fv e) in
      union_list set ys
    | Ecase x pats =>
      fold_left (fun s p => union (exp_fv (snd p)) s) pats (singleton x)
    | Eproj x tau n y e =>
      let set := remove x (exp_fv e) in
      add y set
    | Efun defs e =>
      let names := fundefs_names defs in
      union (fundefs_fv defs names)
            (diff (exp_fv e) names)
    | Eapp x ft xs =>
      union_list (singleton x) xs
    | Eprim x prim ys e =>
      let set := remove x (exp_fv e) in
      union_list set ys
    | Ehalt x =>
      (singleton x)
  end
with fundefs_fv (defs : fundefs) (names : FVSet) : FVSet :=
       match defs with
         | Fcons f t ys e defs' =>
           let fv_e := diff_list (diff (exp_fv e) names) ys in
           union fv_e (fundefs_fv defs' names)
         | Fnil => empty
       end.

(** * * Equivalence of computational and inductive FV definitions *)

(** fundefs_names is correct w.r.t name_in_fundefs *)
Lemma fundefs_names_correct (defs : fundefs) :
  forall f, In f (fundefs_names defs) <-> name_in_fundefs defs f.
Proof.
  induction defs; simpl; intros f0; split; intros H; try now inv H.
  - apply add_spec in H. inv H; eauto. left; eauto.
    right. eapply IHdefs; eauto.
  - apply add_spec. inv H; eauto. inv H0; eauto.
    right. eapply IHdefs; eauto.
Qed.


Lemma fundefs_fv_add defs :
  forall s x,
    Equal (fundefs_fv defs (add x s))
          (remove x (fundefs_fv defs s)).
Proof.
  induction defs; intros s x x'; simpl; split; intros HIn.
  - repeat apply_set_specs_ctx.
    + repeat apply_set_specs;
      (try left; repeat apply_set_specs; auto);
      intros Hc; apply H2; apply_set_specs; eauto.
    + repeat apply_set_specs;
      try right; eapply IHdefs in H; repeat apply_set_specs_ctx; auto.
  - repeat apply_set_specs_ctx.
    + repeat apply_set_specs.
      left. repeat apply_set_specs; auto. 
      intros Hc; apply H3. apply_set_specs_ctx; eauto.
      congruence.
    + repeat apply_set_specs. right.
      eapply IHdefs. apply_set_specs; auto.
  - inv HIn.
  - apply_set_specs_ctx; eauto.
Qed.

Lemma In_fold_left_l {A} (f : A -> FVSet) (l : list A)
      (si : FVSet) x:
  In x (fold_left (fun s e => union (f e) s) l si) ->
  In x si \/ List.Exists (fun e => In x (f e)) l.
Proof.
  revert si; induction l; intros si H; simpl in H; eauto.
  eapply IHl in H. inv H.
  - repeat apply_set_specs_ctx.
    + right. constructor; eauto.
    + left; eauto. 
  - right. constructor 2; eauto.
Qed.

Lemma In_fold_left_r {A} (f : A -> FVSet) (l : list A)
      (si : FVSet) x:
  In x si \/ List.Exists (fun e => In x (f e)) l ->
  In x (fold_left (fun s e => union (f e) s) l si).
Proof.
  revert si; induction l; intros si H; simpl in H; eauto.
  - simpl. inv H; eauto. inv H0.
  - inv H; simpl; eapply IHl.
    + left. apply_set_specs; eauto.
    + inv H0; eauto. left.  apply_set_specs; eauto.
Qed.

Lemma In_fold_left_weaken {A} f (l : list A)
      (si si' : FVSet) x:
  Subset si si' ->
  In x (fold_left (fun s e => union (f e) s) l si) ->
  In x (fold_left (fun s e => union (f e) s) l si').
Proof.
  revert si si'; induction l; intros si si' H Hin; simpl in H; eauto.
  simpl in *. eapply IHl; eauto.
  eapply Subset_union_l; eauto.
Qed.

Lemma In_fold_left {A} f (l : list A)
      (si : FVSet) x:
  In x si ->
  In x (fold_left (fun s e => union (f e) s) l si).
Proof.
  revert si; induction l; intros si H; simpl; eauto.
  eapply In_fold_left_weaken; eauto.
  apply Subset_union_mon_r. eapply Subset_refl.
Qed.


Lemma Equal_fold_left {A} f (l : list A) (si si' : FVSet): 
  Equal si si' ->
  Equal (fold_left (fun s e => union (f e) s) l si)
        (fold_left (fun s e => union (f e) s) l si').
Proof.
  revert si si'; induction l; intros si si' H; eauto.
  simpl. eapply IHl. apply Subset_Equal; eauto.
  eapply Subset_union_l; eauto. apply Equal_Subset_l; eauto.
  eapply Subset_union_l; eauto. apply Equal_Subset_r; eauto.
Qed.

Lemma In_fold_left_strengthen {A} f (l : list A)
      (si si' : FVSet) x:
  In x (fold_left (fun s e => union (f e) s) l (union si si')) ->
  In x (fold_left (fun s e => union (f e) s) l si') \/ In x si.
Proof.
  revert si si'; induction l; intros si si' H; simpl in H; eauto; simpl in *.
  - apply_set_specs_ctx; eauto.
  - rewrite Equal_fold_left in H. Focus 2.
    rewrite union_sym. rewrite union_assoc. rewrite (union_sym si' (f a)). reflexivity.
    eapply IHl in H. inv H; eauto.
Qed.

(** correctness of exp_fv and fundefs_fv w.r.t occurs_free and
    occurs_free_fundefs *)
Lemma exp_fv_fundefs_fv_correct :
  (forall e x, In x (exp_fv e) <-> occurs_free e x) /\
  (forall defs x,
     In x (fundefs_fv defs (fundefs_names defs)) <->
     occurs_free_fundefs defs x).
Proof.
  exp_defs_induction IHe IHl IHdefs; simpl; intros x; split; intros H.
  - repeat apply_set_specs_ctx.
    + constructor 2; eauto. eapply IHe; eauto.
    + constructor; eauto.
  - inv H; repeat apply_set_specs; eauto.
    left. apply_set_specs; eauto.
    apply IHe; eauto.
  - repeat apply_set_specs_ctx; constructor.
  - inv H. apply_set_specs; eauto.
  - eapply In_fold_left_strengthen in H. inv H.
    + apply Free_Ecase3. apply IHl; eauto.
    + constructor. eapply IHe; eauto. 
  - inv H.
    + eapply In_fold_left. apply_set_specs. right; constructor; eauto.
    + apply In_fold_left. apply_set_specs; left. apply IHe; eauto.
    + apply IHl in H5. simpl in H5.
      eapply In_fold_left_weaken; eauto.
      apply Subset_union_mon_r. apply Subset_refl.
  - repeat apply_set_specs_ctx.
    + constructor; eauto.
    + constructor; eauto. eapply IHe; eauto.
  - inv H; repeat apply_set_specs; eauto.
    right. apply_set_specs; eauto. apply IHe; eauto.
  - repeat apply_set_specs_ctx.
    + eapply Free_Efun2. eapply IHdefs; eauto.
    + econstructor. intros Hc; apply H1; apply fundefs_names_correct; eauto.
      eapply IHe; eauto.
  - inv H; repeat apply_set_specs; eauto.
    + right. apply_set_specs; eauto. apply IHe; eauto.
      intros Hc; apply H2; apply fundefs_names_correct; eauto.
    + left. eapply IHdefs; eauto.
  - repeat apply_set_specs_ctx; constructor; eauto.
  - inv H; apply_set_specs; eauto. left. apply_set_specs; eauto.
  - repeat apply_set_specs_ctx.
    + eapply Free_Eprim2; eauto. eapply IHe; eauto.
    + constructor; eauto.
  - inv H; apply_set_specs; eauto. left.
    apply_set_specs; eauto; apply IHe; eauto.
  - repeat apply_set_specs_ctx. constructor.
  - inv H; apply_set_specs. reflexivity.
  - repeat apply_set_specs_ctx.
    + constructor; eauto.
      intros Hc; apply H2; apply_set_specs; eauto.
      intros Hc. apply H2. apply_set_specs; eauto;
      right. apply fundefs_names_correct; eauto. 
      apply IHe; eauto.
    + apply fundefs_fv_add in H0. apply_set_specs_ctx.
      constructor 2; eauto. apply IHdefs; eauto.
  - inv H; repeat apply_set_specs.
    + left; repeat apply_set_specs; eauto.
      apply IHe; eauto.
      intros Hc. apply H8. repeat apply_set_specs_ctx.
      congruence. apply fundefs_names_correct; auto.
    + right. apply fundefs_fv_add. repeat apply_set_specs; auto.
      apply IHdefs. eauto.
  - inv H.
  - inv H.
Qed.

Corollary fundefs_fv_correct B :
  Same_set var (occurs_free_fundefs B)
           (FromList (PS.elements (fundefs_fv B (fundefs_names B)))).
Proof.
  split; intros x H.
  eapply exp_fv_fundefs_fv_correct in H. eapply PS.elements_spec1 in H.
  eapply InA_alt in H. edestruct H as [y [Heq Hin]]. subst. eauto. 
  eapply exp_fv_fundefs_fv_correct. eapply PS.elements_spec1.
  eapply In_InA. now eapply PS.E.eq_equiv. eassumption.
Qed.

(** * Compute the maximum identifier (free or bound) that occurs in an expression *)

Fixpoint max_var e z :=
  match e with
    | Econstr x _ ys e => max_var e (max_list (x::ys) z) 
    | Ecase x P =>
      (fix aux P z :=
         match P with
           | (_, e) :: P => aux P (max_var e z)
           | [] => (Pos.max z x)
         end) P z
    | Eproj x _ _ y e => max_var e (max_list (x::y::nil) z)
    | Efun defs e =>
      let z' := max_var_fundefs defs z in
      max_var e z'
    | Eapp f _ xs => max_list (f::xs) z
    | Eprim x _ ys e => max_var e (max_list (x::ys) z)
    | Ehalt x => Pos.max z x
  end
with max_var_fundefs defs z :=
       match defs with
         | Fcons f _ ys e defs =>
           let z' := max_var e z in
           max_var_fundefs defs (max_list (f::ys) z')
         | Fnil => z
       end.

Lemma acc_leq_max_var_mut :
  (forall e y,
     (y <= max_var e y)%positive) /\
  (forall B y,
     (y <= max_var_fundefs B y)%positive).
Proof.
  exp_defs_induction IHe IHl IHb; intros y;
  try now (eapply Pos.le_trans; [| now eapply IHe ];
           eapply Pos.le_trans; [| now eapply max_list_spec1 ];
           zify; omega).
  - simpl; zify; omega.
  - simpl. eapply Pos.le_trans. now apply IHe. 
    now apply IHl.
  - simpl. eapply Pos.le_trans. now apply IHb.
    now apply IHe.
  - simpl. eapply Pos.le_trans; [| eapply max_list_spec1 ].
    zify; omega.
  - simpl. zify; omega.
  - simpl. eapply Pos.le_trans. now apply IHe.
    eapply Pos.le_trans. now apply max_list_spec1.
    eapply Pos.le_trans; [| now apply IHb ].
    eapply max_list_acc_mon. zify; omega. 
  - simpl. zify; omega. 
Qed.

Corollary acc_leq_max_var e y :
  (y <= max_var e y)%positive.
Proof.
  now apply acc_leq_max_var_mut. 
Qed.

Corollary acc_leq_max_var_fundefs B y :
  (y <= max_var_fundefs B y)%positive.
Proof.
  now apply acc_leq_max_var_mut. 
Qed.

Lemma bound_var_leq_max_var_mut :
  (forall e x y,
     Ensembles.In _ (bound_var e) x ->
     (x <= max_var e y)%positive) /\
  (forall B x y,
     Ensembles.In _ (bound_var_fundefs B) x ->
     (x <= max_var_fundefs B y)%positive).
Proof.
  exp_defs_induction IHe IHl IHb; intros x y HIn;
  try (simpl; inv HIn; [| now eauto ];
       (eapply Pos.le_trans; [| now eapply acc_leq_max_var ];
        eapply Pos.le_trans; [| now eapply max_list_spec1 ];
        zify; omega)).
  - inv HIn. inv H3.
  - inv HIn. inv H3; [| now  eauto]. inv H.
    eapply Pos.le_trans; [| eapply acc_leq_max_var with (e := Ecase v l) ].
    now eauto.
  - simpl. inv HIn; [| now eauto ].
    eapply Pos.le_trans; [| now eapply acc_leq_max_var ].
    zify; omega.
  - inv HIn; [| now eauto ].
    simpl. eapply Pos.le_trans; [| now eapply acc_leq_max_var ].
    now eauto.
  - inv HIn.
  - inv HIn.
  - simpl; inv HIn; [| now eauto |].
    + inv H5.
      * inv H.
        eapply Pos.le_trans; [| now eapply acc_leq_max_var_fundefs ].
        eapply Pos.le_trans; [| now eapply max_list_spec1 ].
        zify; omega.
      * eapply Pos.le_trans; [| now eapply acc_leq_max_var_fundefs ].
        now eapply max_list_spec2.
    + eapply Pos.le_trans; [| now eapply acc_leq_max_var_fundefs ].
      eapply Pos.le_trans; [| now eapply max_list_spec1 ].
      eapply Pos.le_trans. now apply IHe with (y := y); eauto.
      zify; omega.
  - inv HIn.
Qed.

Corollary bound_var_leq_max_var e x y :
  Ensembles.In _ (bound_var e) x ->
  (x <= max_var e y)%positive.
Proof.
  now apply bound_var_leq_max_var_mut.
Qed.

Corollary bound_var_leq_max_fundefs B x y :
  Ensembles.In _ (bound_var_fundefs B) x ->
  (x <= max_var_fundefs B y)%positive.
Proof.
  now apply bound_var_leq_max_var_mut.
Qed.

Lemma occurs_free_leq_max_var_mut :
  (forall e x y,
     Ensembles.In _ (occurs_free e) x ->
     (x <= max_var e y)%positive) /\
  (forall B x y,
     Ensembles.In _ (occurs_free_fundefs B) x ->
     (x <= max_var_fundefs B y)%positive).
Proof.
  exp_defs_induction IHe IHl IHb; intros x y HIn.
  try (inv HIn; [| now eauto ];
       simpl; eapply Pos.le_trans; [| now eapply acc_leq_max_var ];
       now eapply max_list_spec2).
  - inv HIn. simpl; zify; omega.
  - inv HIn; [ now eauto | | now eauto ].
    simpl. eapply Pos.le_trans; [| eapply acc_leq_max_var with (e := Ecase v l) ].
    now eauto.
  - simpl. inv HIn; [| now eauto ].
    eapply Pos.le_trans; [| now eapply acc_leq_max_var ].
    zify; omega.
  - inv HIn; [ now eauto |].
    simpl. eapply Pos.le_trans; [| now eapply acc_leq_max_var ].
    now eauto.
  - inv HIn; simpl.
    eapply Pos.le_trans; [| now eapply max_list_spec1 ]. zify; omega.
    now eapply max_list_spec2.
  - simpl; inv HIn; [| now eauto ].
    eapply Pos.le_trans; [| now eapply acc_leq_max_var ].
    now apply max_list_spec2.
  - inv HIn. simpl. zify; omega.
  - inv HIn; [| now eauto ].
    simpl. eapply Pos.le_trans. eapply IHe with (y := y). eassumption.
    eapply Pos.le_trans; [| now eapply acc_leq_max_var_fundefs ].
    eapply Pos.le_trans; [| now eapply max_list_spec1 ]. zify; omega.
  - inv HIn. 
Qed. 

Corollary occurs_free_leq_max_var e x y :
  Ensembles.In _ (occurs_free e) x ->
  (x <= max_var e y)%positive.
Proof.
  now apply occurs_free_leq_max_var_mut.
Qed.

Corollary occurs_free_leq_max_fundefs B x y :
  Ensembles.In _ (occurs_free_fundefs B) x ->
  (x <= max_var_fundefs B y)%positive.
Proof.
  now apply occurs_free_leq_max_var_mut.
Qed.

(** * A set that contains all the identifiers above a certain value *)

(** All the variables that are greater or equal to x are in S (i.e. the "fresh" set) *)
Definition fresh (S : Ensemble var) (x : var) :=
  forall y, (x <= y)%positive -> Ensembles.In _ S y.

Lemma fresh_monotonic S S' x :
  Included _ S S' ->
  fresh S x ->
  fresh S' x.
Proof.
  intros Hinc Hf x' Hleq. eapply Hinc. eapply Hf. eassumption.
Qed.

Lemma fresh_Instersection S1 S2 x :
  fresh S1 x ->
  fresh S2 x ->
  fresh (Intersection _ S1 S2) x.
Proof.
  intros Hf1 Hf2 x' Hleq. eauto.
Qed.

Lemma fresh_Setminus S1 S2 S3 x :
  fresh (Setminus _ S1 S2) x ->
  fresh (Setminus _ S1 S3) x ->
  fresh (Setminus _ S1 (Union _ S2 S3)) x.
Proof.
  intros Hf1 Hf2 x' Hleq. constructor.
  now eapply Hf1. intros Hc. inv Hc. eapply Hf1 in H; eauto.
  eapply Hf2 in H; eauto.
Qed.

Instance fresh_Proper : Proper (Same_set _ ==> Logic.eq ==> iff) fresh.
Proof.
  intros s1 s2 Hseq x1 x2 Heq; subst; split; intros x H.
  now rewrite <- Hseq; eauto.
  now rewrite Hseq; eauto.
Qed.

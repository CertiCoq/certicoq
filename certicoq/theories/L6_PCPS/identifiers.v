Require Import List BinNat Coq.MSets.MSetRBT List Ensembles.
Require Import cps cps_util ctx set_util Ensembles_util.
Import ListNotations.

Import PS.

Open Scope ctx_scope.

Definition FVSet := PS.t.

(** $\{x\}$ is decidable *)
Instance DecidableSingleton_var x : Decidable (Singleton var x).
Proof.
  constructor. intros x'.
  destruct (var_dec x x'); subst. left; constructor.
  right. intros Hc. inv Hc; eauto.
Qed.

(** * Function definitions *) 

(** [name_in_fundefs B] is the set of the names of the functions in [B] *)
Fixpoint name_in_fundefs (B : fundefs) : Ensemble var :=
  match B with
    | Fnil => Empty_set var
    | Fcons f' _ _ _ B =>
      Union var (Singleton var f') (name_in_fundefs B)
  end.

(** [fun_in_fundefs B] is the set of functions defined in [B] *)
Fixpoint fun_in_fundefs  (B : fundefs) : Ensemble (var * type * list var * exp) :=
  match B with
    | Fnil => Empty_set _
    | Fcons f tau xs e B =>
      Union _ (Singleton _ (f, tau, xs, e))
            (fun_in_fundefs B)
  end.

Instance Decidable_name_in_fundefs (B : fundefs) :
  Decidable (name_in_fundefs B).
Proof.
  constructor.
  induction B; intros x.
  - destruct (Coqlib.peq x v); subst.
    left. left. eauto.
    destruct (IHB x). left. right; eauto.
    right. intros Hc. inv Hc. inv H0; congruence. 
    exfalso. eauto.
  - right. intros Hc; inv Hc.
Qed.

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

Lemma split_fds_name_in_fundefs B1 B2 B3 :
  split_fds B1 B2 B3 ->
  Same_set var (name_in_fundefs B3)
           (Union var (name_in_fundefs B1) (name_in_fundefs B2)).
Proof.
  intros Hspl. induction Hspl; simpl.
  - rewrite IHHspl. repeat rewrite <- Union_assoc. apply Same_set_refl.
  - rewrite IHHspl. simpl. 
    rewrite (Union_sym _ (Union var (Singleton var v) _)).
    repeat rewrite <- Union_assoc. rewrite (Union_sym (name_in_fundefs lfds)).
    apply Same_set_refl.
  - split; intros x H; inv H; inv H0.
Qed.

Lemma fundefs_append_name_in_fundefs B1 B2 B3 :
  fundefs_append B1 B2 = B3 ->
  Same_set var (name_in_fundefs B3)
           (Union var (name_in_fundefs B1) (name_in_fundefs B2)).
Proof.
  revert B3. induction B1; intros B3 Heq; simpl.
  - destruct B3. simpl in Heq. inv Heq. simpl. 
    rewrite IHB1; eauto. rewrite Union_assoc. apply Same_set_refl.
    inv Heq.
  - inv Heq. simpl. rewrite Union_Empty_set_r.
    apply Same_set_refl.
Qed.

Lemma name_in_fundefs_ctx B e1 e2 :
  Same_set _ (name_in_fundefs (B <[ e1 ]>)) (name_in_fundefs (B <[ e2 ]>)).
Proof.
  induction B; simpl;
  (apply Same_set_Union_compat; [ now apply Same_set_refl |]).
  now apply Same_set_refl.
  eassumption.
Qed.

Lemma split_fds_fun_in_fundefs B1 B2 B3 :
  split_fds B1 B2 B3 ->
  Same_set _ (fun_in_fundefs B3)
           (Union _ (fun_in_fundefs B1) (fun_in_fundefs B2)).
Proof.
  intros Hspl1. induction Hspl1; simpl.
  - rewrite IHHspl1. rewrite Union_assoc. apply Same_set_refl.
  - rewrite IHHspl1. rewrite (Union_sym (fun_in_fundefs lfds) (Union _ _ _)).
    rewrite (Union_sym (fun_in_fundefs lfds)). rewrite Union_assoc.
    apply Same_set_refl.
  - rewrite Union_Empty_set_l. apply Same_set_refl.
Qed.

Lemma fundefs_append_fun_in_fundefs B1 B2 B3 :
  fundefs_append B1 B2 = B3 ->
  Same_set _ (fun_in_fundefs B3)
           (Union _ (fun_in_fundefs B1) (fun_in_fundefs B2)).
Proof.
  intros H. eapply split_fds_fun_in_fundefs.
  eapply fundefs_append_split_fds; eauto.
Qed.

(** names(B) = $\{ f ~|~ \exists ~xs ~tau ~e,~(f, ~xs, ~tau, ~e) \in B \}$ *)
Lemma name_in_fundefs_big_cup_fun_in_fundefs B :
  Same_set var (name_in_fundefs B) (big_cup (fun_in_fundefs B)
                                            (fun p =>
                                               let '(x, _, _, _) := p in
                                               Singleton var x)).
Proof.
  induction B; simpl in *.
  - rewrite Union_big_cup, big_cup_Singleton, IHB.
    apply Same_set_Union_compat; eauto using Same_set_refl.
  - rewrite big_cup_Empty_set. apply Same_set_refl.
Qed.

Lemma fun_in_fundefs_name_in_fundefs f tau xs e B :
    fun_in_fundefs B (f, tau, xs, e) ->
    name_in_fundefs B f.
Proof.
  intros H. eapply name_in_fundefs_big_cup_fun_in_fundefs.
  repeat eexists; eauto. constructor.
Qed.

(** ** Lemmas about [find_def] and [def_funs] *)

(** [find_def] is correct w.r.t. [fun_in_fundefs] *)
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
  - simpl in Hget. rewrite M.gsspec in Hget. destruct (Coqlib.peq x v0).
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
  - simpl. rewrite M.gsspec. destruct (Coqlib.peq x v); subst; eauto.
Qed.

Lemma def_funs_neq x B B' rho rho' :
  ~ name_in_fundefs B x ->
  M.get x (def_funs B' B rho rho') = M.get x rho'.
Proof.
  induction B; intros Hin; simpl; eauto.
  rewrite M.gsspec. destruct (Coqlib.peq x v); subst; eauto.
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

(** * Free variables, inductive definitions *)

(** [occurs_free e] is the set of free variables of [e] *)
Inductive occurs_free : exp -> Ensemble var :=
| Free_Econstr1 :
    forall y x tau t ys e,
      List.In y ys ->
      occurs_free (Econstr x tau t ys e) y
| Free_Econstr2 :
    forall y x tau t ys e,
      ~ x = y ->
      occurs_free e y ->
      occurs_free (Econstr x tau t ys e) y
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
    forall x ys,
      occurs_free (Eapp x ys) x
| Free_Eapp2 :
    forall y x ys,
      List.In y ys ->
      occurs_free (Eapp x ys) y
| Free_Eprim1 :
    forall y x tau p ys e,
      List.In y ys ->
      occurs_free (Eprim x tau p ys e) y
| Free_Eprim2 :
    forall y x tau p ys e,
      x <> y ->
      occurs_free e y ->
      occurs_free (Eprim x tau p ys e) y
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

(** sanity check : The names of the functions cannot appear 
  * free in a fundefs block *)
Lemma fun_names_not_free_in_fundefs f defs :
  name_in_fundefs defs f ->
  ~ occurs_free_fundefs defs f.
Proof.
  intros Hname Hfree. 
  induction Hfree; inversion Hname; eauto.
  inv H3. eauto. inv H0; eauto.
Qed.

Lemma occurs_free_Econstr x tau t ys e :
  Same_set var (occurs_free (Econstr x tau t ys e))
           (Union _ (FromList ys) (Setminus var (occurs_free e) (Singleton var x))).
Proof.
  split; intros x' H; inv H; eauto.
  right. constructor; eauto. intros H. inv H; eauto.
  inv H0. constructor 2; eauto. intros Hc. subst. eauto.
Qed.

Lemma occurs_free_Eprim x tau f ys e :
  Same_set var (occurs_free (Eprim x tau f ys e))
           (Union _ (FromList ys) (Setminus var (occurs_free e) (Singleton var x))).
Proof.
  split; intros x' H; inv H; eauto.
  right. constructor; eauto. intros H. inv H; eauto.
  inv H0. eapply Free_Eprim2; eauto. intros Hc. subst. eauto.
Qed.

Lemma occurs_free_Eproj x tau t y e :
  Same_set var (occurs_free (Eproj x tau t y e))
           (Union _ (Singleton var y) (Setminus var (occurs_free e) (Singleton var x))).
Proof.
  split; intros x' H; inv H; eauto. 
  right. constructor; eauto. intros H. inv H; eauto.
  inv H0. eauto.
  inv H0. constructor; eauto.
  intros Hc. subst. eauto.
Qed.

Lemma occurs_free_Eapp f ys :
  Same_set var (occurs_free (Eapp f ys))
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
           (Union _ (occurs_free e)
                  (Union _ (Singleton _ x)
                         (occurs_free (Ecase x P)))).
Proof.
  split; intros x' H; inv H; eauto.
  inv H0; eauto. inv H; eauto.
Qed.
  
Lemma occurs_free_Ecase_app x c e P P' :
  Same_set var (occurs_free (Ecase x (P' ++ ((c, e) :: P))))
           (Union _ (occurs_free e)
                  (Union _ (Singleton _ x)
                         (Union _ (occurs_free (Ecase x P'))
                                (occurs_free (Ecase x P))))).
Proof.
  induction P' as [| [c' e'] P' IHP']; simpl.
  - rewrite occurs_free_Ecase_nil.
    rewrite (Union_assoc (Singleton var x)), Union_idempotent.
    now apply occurs_free_Ecase_cons.
  - rewrite !occurs_free_Ecase_cons. rewrite IHP'.
    rewrite  !Union_assoc. rewrite (Union_sym _ (occurs_free e)).
    rewrite <- Union_assoc. rewrite (Union_sym (occurs_free e')).
    rewrite  !Union_assoc. apply Same_set_refl.
Qed.

Lemma occurs_free_fundefs_Fcons f t xs e B :
  Same_set var (occurs_free_fundefs (Fcons f t xs e B))
           (Union var (Setminus var (occurs_free e)
                                (Union var (Singleton var f)
                                       (Union var (FromList xs)
                                              (name_in_fundefs B))))
                  (Setminus var (occurs_free_fundefs B) (Singleton var f))).
Proof.
  split; intros x H; inv H; eauto.
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

Lemma occurs_free_fundefs_Fcons_Included f tau xs e B :
  Included var (occurs_free_fundefs B)
           (Union _ (occurs_free_fundefs (Fcons f tau xs e B)) (Singleton var f)).
Proof.
  intros x H. destruct (var_dec f x); subst; now eauto.
Qed.

Lemma occurs_free_Econstr_Included x tau t ys e :
  Included var (occurs_free e)
           (Union var (occurs_free (Econstr x tau t ys e)) (Singleton var x)).
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

Lemma occurs_free_Eprim_Included x tau f ys e :
  Included var (occurs_free e)
           (Union var (occurs_free (Eprim x tau f ys e)) (Singleton var x)).
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
Proof.
  induction B; intros H; inv H.
  - inv H0. intros x H.
    destruct (Coqlib.peq x f); simpl; subst; eauto.
    destruct (in_dec var_dec x xs); eauto; subst.
    destruct (@Dec _ _ (Decidable_name_in_fundefs B) x); eauto.
  - intros x H. destruct (Coqlib.peq x v); subst.
    + right; left. left; eauto.
    + edestruct (IHB H0 x) as [H'| H']; eauto.
      inv H1; eauto. right. left. right; eauto.
Qed.

(** FV(B) = $\bigcup_{(f, xs e) \in B}(FV(e) \setminus xs \setminus names(B))$ *)
Lemma occurs_free_fundefs_big_cup B :
  Same_set _ (occurs_free_fundefs B)
           (big_cup (fun_in_fundefs B)
                    (fun p =>
                       (Setminus _ (let '(f, _, xs, e) := p in
                                    (Setminus _ (occurs_free e) (FromList xs)))
                                 (name_in_fundefs B)))).
Proof.
  induction B; simpl.
  - rewrite occurs_free_fundefs_Fcons. rewrite IHB.
    rewrite Union_big_cup, big_cup_Singleton.
    rewrite Setminus_Union. apply Same_set_Union_compat.
    rewrite (Union_assoc (FromList l)), (Union_sym _ (Singleton var v)),
            <- Union_assoc. apply Same_set_refl.
    rewrite <- Setminus_big_cup.
    apply Same_Set_big_cup_r. intros [[[f tau] xs] e'].
    rewrite Setminus_Union, (Union_sym (Singleton var v)).
    apply Same_set_refl.
  - rewrite occurs_free_fundefs_Fnil, big_cup_Empty_set. apply Same_set_refl.
Qed.

Lemma split_fds_occurs_free_fundefs B1 B2 B3 :
  split_fds B1 B2 B3 ->
  Same_set var (occurs_free_fundefs B3)
           (Union _ (Setminus _ (occurs_free_fundefs B1) (name_in_fundefs B2))
                  (Setminus _ (occurs_free_fundefs B2) (name_in_fundefs B1))).
Proof.
  intros H1.
  rewrite !occurs_free_fundefs_big_cup.
  rewrite <- !Setminus_big_cup.
  eapply Same_set_trans with
  (s2 := Union var
               (big_cup (fun_in_fundefs B1) _)
               (big_cup (fun_in_fundefs B2) _)).
  rewrite <- Union_big_cup.
  eapply Same_Set_big_cup_l. rewrite split_fds_fun_in_fundefs; eauto.
  now apply Same_set_refl.
  eapply Same_set_Union_compat; eapply Same_Set_big_cup_r.
  intros [[[f tau] xs] e]. rewrite !Setminus_Union.
  rewrite split_fds_name_in_fundefs; eauto. now apply Same_set_refl.
  intros [[[f tau] xs] e]. rewrite !Setminus_Union.
  rewrite split_fds_name_in_fundefs; eauto.
  rewrite (Union_sym (name_in_fundefs B2) (name_in_fundefs B1)).
  now apply Same_set_refl.
Qed.

Lemma Same_set_fun_in_fundefs_Same_set_occurs_free_fundefs B1 B2 :
  Same_set _ (fun_in_fundefs B1) (fun_in_fundefs B2) ->
  Same_set _ (occurs_free_fundefs B1) (occurs_free_fundefs B2).
Proof.
  rewrite !occurs_free_fundefs_big_cup. intros H.
  apply Same_Set_big_cup; eauto.
  intros [[[f tau] xs] e']. apply Same_set_Setminus_compat.
  now apply Same_set_refl.
  rewrite !name_in_fundefs_big_cup_fun_in_fundefs.
  apply Same_Set_big_cup_l; eauto.
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
      

Lemma same_split_fds_occurs_free_fundefs B1 B2 B3 B3' :
  split_fds B1 B2 B3 ->
  split_fds B1 B2 B3' ->
  Same_set _ (occurs_free_fundefs B3) (occurs_free_fundefs B3').
Proof.
  intros Hspl1 Hspl2. rewrite !occurs_free_fundefs_big_cup.
  apply Same_Set_big_cup.
  - intros [[[f tau] xs] e']. apply Same_set_Setminus_compat.
    now apply Same_set_refl. rewrite !name_in_fundefs_big_cup_fun_in_fundefs.
    apply Same_Set_big_cup_l; eauto. rewrite split_fds_fun_in_fundefs; eauto.
    rewrite (split_fds_fun_in_fundefs B1 B2 B3'); eauto. now apply Same_set_refl.
  - rewrite split_fds_fun_in_fundefs; eauto.
    rewrite (split_fds_fun_in_fundefs B1 B2 B3'); eauto. apply Same_set_refl.
Qed.

Lemma occurs_free_comp_mut :
  (forall c e e', Same_set _ (occurs_free e) (occurs_free e') ->
                  Same_set _ (occurs_free (c |[ e ]|))
                           (occurs_free (c |[ e' ]|))) /\
  (forall B e e', Same_set _ (occurs_free e) (occurs_free e') ->
                  Same_set _ (occurs_free_fundefs (B <[ e ]>))
                           (occurs_free_fundefs (B <[ e' ]>))).
Proof.
  exp_fundefs_ctx_induction IHc IHf; eauto; simpl.
  - intros e1 e2 H. rewrite !occurs_free_Econstr, IHc; [| eassumption ].
    apply Same_set_refl.
  - intros e1 e2 H. rewrite !occurs_free_Eproj, IHc; [| eassumption ].
    apply Same_set_refl.
  - intros e1 e2 H. rewrite !occurs_free_Eprim, IHc; [| eassumption ].
    apply Same_set_refl.
  - intros l' e1 e2 H. rewrite !occurs_free_Ecase_app, IHc; [| eassumption ].
    apply Same_set_refl.
  - intros e1 e2 H. rewrite !occurs_free_Efun, IHc; [| eassumption ].
    apply Same_set_refl.
  - intros e1 e2 H. rewrite !occurs_free_Efun, IHf; [| eassumption ].
    rewrite name_in_fundefs_ctx. apply Same_set_refl.
  - intros e1 e2 H. rewrite !occurs_free_fundefs_Fcons, IHc; [| eassumption ].
    apply Same_set_refl.
  - intros e1 e2 H. rewrite !occurs_free_fundefs_Fcons, IHf; [| eassumption ].
    rewrite name_in_fundefs_ctx. apply Same_set_refl.
Qed.

Corollary occurs_free_comp :
  forall c e e', Same_set _ (occurs_free e) (occurs_free e') ->
                 Same_set _ (occurs_free (c |[ e ]|))
                          (occurs_free (c |[ e' ]|)).
Proof.
  apply occurs_free_comp_mut.
Qed.

Corollary occurs_free_fundefs_comp :
  forall B e e', Same_set _ (occurs_free e) (occurs_free e') ->
                 Same_set _ (occurs_free_fundefs (B <[ e ]>))
                          (occurs_free_fundefs (B <[ e' ]>)).
Proof.
  apply occurs_free_comp_mut.
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
  rewrite same_split_fds_occurs_free_fundefs; eauto.
Qed.

Lemma split_fds_closed_fundefs B1 B2 B3 :
  split_fds B1 B2 B3 ->
  closed_fundefs B1 ->
  closed_fundefs B2 ->
  closed_fundefs B3.
Proof.
  intros H1 H2 H3. unfold closed_fundefs in *.
  rewrite split_fds_occurs_free_fundefs; eauto.
  rewrite H2, H3. rewrite !Setminus_Included_Empty_set.
  rewrite Union_Empty_set_r. apply Same_set_refl.
  intros x Hc; inv Hc. intros x Hc; inv Hc.
Qed.

(** * Function blocks in expressions and function blocks *)

(** [funs_in_exp B e] iff [B] is a block of functions in [e] *)
Inductive funs_in_exp : fundefs -> exp -> Prop :=
| In_Econstr :
    forall fs e x tau t ys,
      funs_in_exp fs e ->
      funs_in_exp fs (Econstr x tau t ys e)
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
    forall fs e x tau p ys,
      funs_in_exp fs e ->
      funs_in_exp fs (Eprim x tau p ys e)
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

(** bound variables - alternative definition without lists or 
  * number of occurences *)
Inductive bound_var : exp -> Ensemble var :=
| Bound_Econstr1 :
    forall x tau t ys e,
      bound_var (Econstr x tau t ys e) x
| Bound_Econstr2 :
    forall y x tau t ys e,
      bound_var e y ->
      bound_var (Econstr x tau t ys e) y
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
    forall x tau p ys e,
      bound_var (Eprim x tau p ys e) x
| Bound_Eprim2 :
    forall y x tau p ys e,
      bound_var e y ->
      bound_var (Eprim x tau p ys e) y
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

Lemma bound_var_Econstr x tau t ys e :
  Same_set _ (bound_var (Econstr x tau t ys e))
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

Lemma bound_var_Eprim x tau f y e :
  Same_set _ (bound_var (Eprim x tau f y e))
           (Union var (bound_var e) (Singleton _ x)).
Proof.
  split; intros x' H; inv H; eauto. inv H0; eauto.
Qed.

Lemma bound_var_Eapp f ys :
  Same_set _ (bound_var (Eapp f ys))
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

Lemma bound_var_Ecase_append x P1 P2 :
  Same_set _ (bound_var (Ecase x (P1 ++ P2)))
           (Union var (bound_var (Ecase x P1)) (bound_var (Ecase x P2))).
Proof.
  induction P1 as [ | [c e] P1 IHP1]; simpl; eauto.
  - rewrite bound_var_Ecase_nil, Union_Empty_set_r.
    eapply Same_set_refl.
  - simpl. rewrite !bound_var_Ecase_cons, IHP1, Union_assoc.
    eapply Same_set_refl.
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
Proof.
  split; intros x H; inv H; eauto.
  - inv H6; eauto.
  - inv H0. now eauto.
    inv H; now eauto.
Qed.

Lemma bound_var_fundefs_Fnil  :
  Same_set var (bound_var_fundefs Fnil) (Empty_set var).
Proof.
  split; intros x H; inv H; eauto.
Qed.

Lemma name_in_fundefs_bound_var_fundefs B :
  Included var (name_in_fundefs B) (bound_var_fundefs B).
Proof.
  induction B; simpl.
  - intros x H. inv H.
    constructor. eauto. constructor 2. apply IHB; eauto.
  - apply Included_Empty_set.
Qed.

Lemma name_in_fundefs_bound_var_Efun B2 e :
  Included var (name_in_fundefs B2) (bound_var (Efun B2 e)).
Proof.
  intros x H. constructor. eapply name_in_fundefs_bound_var_fundefs. eauto.
Qed.

Lemma split_fds_bound_vars B1 B2 B3 :
  split_fds B1 B2 B3 ->
  Same_set var (bound_var_fundefs B3)
           (Union var (bound_var_fundefs B1) (bound_var_fundefs B2)).
Proof.
  intros Hspl. induction Hspl; simpl.
  - rewrite !bound_var_fundefs_Fcons; rewrite IHHspl.
    repeat rewrite <- (Union_assoc _ _ (bound_var_fundefs rfds)). apply Same_set_refl.
  - rewrite !bound_var_fundefs_Fcons. rewrite IHHspl.
    rewrite (Union_sym _ (Union var (Singleton var v) _)).
    repeat rewrite <- Union_assoc. rewrite (Union_sym (bound_var_fundefs lfds)).
    apply Same_set_refl.
  - split; intros x H; inv H; inv H0.
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
  exp_fundefs_ctx_induction IHc IHf; eauto; simpl.
  - intros e1 e2 H.
    rewrite !bound_var_Econstr, IHc; [| eassumption ].
    apply Same_set_refl.
  - intros e1 e2 H.
    rewrite !bound_var_Eproj, IHc; [| eassumption ].
    apply Same_set_refl.
  - intros e1 e2 H.
    rewrite !bound_var_Eprim, IHc; [| eassumption ].
    apply Same_set_refl.
  - intros l' e1 e2 H.
    rewrite !bound_var_Ecase_append, !bound_var_Ecase_cons, IHc; [| eassumption ].
    apply Same_set_refl.
  - intros e1 e2 H.
    rewrite !bound_var_Efun, IHc; [| eassumption ].
    apply Same_set_refl.
  - intros e1 e2 H.
    rewrite !bound_var_Efun, IHf; [| eassumption ].
    apply Same_set_refl.
  - intros e1 e2 H.
    rewrite !bound_var_fundefs_Fcons, IHc; [| eassumption ].
    apply Same_set_refl.
  - intros e1 e2 H.
    rewrite !bound_var_fundefs_Fcons, IHf; [| eassumption ].
    apply Same_set_refl.
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

(** unique bindings - alternative definition without lists *)
Inductive unique_bindings : exp -> Prop :=
| UBound_Econstr :
    forall x tau t ys e,
      ~ (bound_var e) x ->
      unique_bindings e ->
      unique_bindings (Econstr x tau t ys e)
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
| UBound_Eprim :
    forall x tau p ys e,
      ~ (bound_var e) x ->
      unique_bindings e ->
      unique_bindings (Eprim x tau p ys e)
with unique_bindings_fundefs : fundefs -> Prop :=
| UBound_Fcons :
    forall f tau ys e defs,
      ~ (bound_var e) f ->
      ~ (bound_var_fundefs defs) f ->
      Disjoint var (bound_var e) (FromList ys) ->
      Disjoint var (bound_var_fundefs defs) (FromList ys) ->
      Disjoint var (bound_var e) (bound_var_fundefs defs) ->
      ~ FromList ys f ->
      unique_bindings e ->
      unique_bindings_fundefs defs ->
      unique_bindings_fundefs (Fcons f tau ys e defs)
| UBound_Fnil :
    unique_bindings_fundefs Fnil.

Lemma unique_bindings_Ecase_l x P1 c e P2 :
  unique_bindings (Ecase x (P1 ++ ((c, e) :: P2))) ->
  unique_bindings e /\
  unique_bindings (Ecase x P1) /\  unique_bindings (Ecase x P2) /\
  Disjoint var (bound_var (Ecase x P1)) (bound_var e) /\
  Disjoint var (bound_var (Ecase x P2)) (bound_var e) /\
  Disjoint var (bound_var (Ecase x P1)) (bound_var (Ecase x P2)).
Proof.
  intros H. induction P1.
  - inv H. split; [ assumption |].
    split; [now constructor |]. split; [assumption |].
    split.
    + rewrite bound_var_Ecase_nil. now apply Disjoint_Empty_set_l.
    + split.
      * now apply Disjoint_sym.
      * rewrite bound_var_Ecase_nil. now apply Disjoint_Empty_set_l.
  - inv H. destruct (IHP1 H3) as [H1' [H2' [H3' [H4' [H5' H6']]]]].
    split; [ assumption |].
    split.
    + constructor; [ assumption | assumption |].
      rewrite !bound_var_Ecase_append, !bound_var_Ecase_cons in *.
      eapply Disjoint_sym. eapply Disjoint_Union_l.
      eapply Disjoint_sym. eassumption.
    + split; [ assumption |]. split.
      * rewrite !bound_var_Ecase_append, !bound_var_Ecase_cons in *.
        eapply Disjoint_Union; [| assumption ].
        eapply Disjoint_Included_r; [| eassumption ].
        eapply Included_Union_mon_r.
        eapply Included_Union_l.
      * split; [ assumption |].
        rewrite !bound_var_Ecase_append, !bound_var_Ecase_cons in *.
        eapply Disjoint_Union; [| assumption ].
        eapply Disjoint_Included_r; [| eassumption ].
        do 2eapply Included_Union_mon_r. apply Included_refl.
Qed.

Lemma unique_bindings_Ecase_r x P1 c e P2 :
  unique_bindings e ->
  unique_bindings (Ecase x P1) ->
  unique_bindings (Ecase x P2) ->
  Disjoint var (bound_var (Ecase x P1)) (bound_var e) ->
  Disjoint var (bound_var (Ecase x P2)) (bound_var e) ->
  Disjoint var (bound_var (Ecase x P1)) (bound_var (Ecase x P2)) ->
  unique_bindings (Ecase x (P1 ++ ((c, e) :: P2))).
Proof.
  intros H1 H2 H3 H4 H5 H6. induction P1 as [| [c' e'] P1 IHP1].
  - constructor; [assumption | assumption |].
    now apply Disjoint_sym.
  - inv H2. 
    simpl. rewrite !bound_var_Ecase_cons in *. constructor; [| eassumption |].
    * eapply IHP1; [ assumption | |].
      eapply Disjoint_Union_r. eassumption.
      eapply Disjoint_Union_r. eassumption.
    * rewrite !bound_var_Ecase_append in *.
      eapply Disjoint_sym.
      eapply Disjoint_Union; [ eapply Disjoint_sym; eassumption |].
      rewrite bound_var_Ecase_cons. 
      eapply Disjoint_Union; eapply Disjoint_sym;
      now eapply Disjoint_Union_l; eauto.
Qed.

Lemma split_fds_unique_bindings_fundefs_l B1 B2 B3 :
  unique_bindings_fundefs B3 ->
  split_fds B1 B2 B3 ->
  unique_bindings_fundefs B1 /\ unique_bindings_fundefs B2 /\
  Disjoint var (bound_var_fundefs B1) (bound_var_fundefs B2).
Proof.
  intros Hun Hspl. induction Hspl; simpl.
  - inv Hun. edestruct IHHspl as [H1 [H2 H3]]; eauto.
    erewrite (split_fds_bound_vars _ _ lrfds) in H8, H7; eauto.
    repeat split; eauto. constructor; eauto.
    intros Hc. apply H5. eapply split_fds_bound_vars; eauto.
    apply Disjoint_sym in H8. eapply Disjoint_Union_l; eauto.
    apply Disjoint_sym in H8. eapply Disjoint_sym.
    eapply Disjoint_Union_l; eauto.
    intros x Hin. inv Hin. rewrite bound_var_fundefs_Fcons in H.
    inv H. inv H12. eapply H5. eapply split_fds_bound_vars; eauto.
    inv H12. eapply H7. constructor; eauto.
    inv H. eapply H8; constructor; eauto.
    eapply H3; constructor; eauto.
  - inv Hun. edestruct IHHspl as [H1 [H2 H3]]; eauto.
    erewrite (split_fds_bound_vars _ _ lrfds) in H8, H7; eauto.
    repeat split; eauto. constructor; eauto.
    intros Hc. apply H5. eapply split_fds_bound_vars; eauto.
    apply Disjoint_sym in H8. eapply Disjoint_Union_r; eauto.
    apply Disjoint_sym in H8. eapply Disjoint_sym.
    eapply Disjoint_Union_r; eauto.
    intros x Hin. inv Hin. rewrite bound_var_fundefs_Fcons in H0.
    inv H0. inv H12. eapply H5. eapply split_fds_bound_vars; eauto.
    inv H12. eapply H7. constructor; eauto.
    inv H0. eapply H8; constructor; eauto.
    eapply H3; constructor; eauto.
  - split; try constructor; eauto. rewrite bound_var_fundefs_Fnil at 1.
    apply Disjoint_Empty_set_l.
Qed.

Lemma split_fds_unique_bindings_fundefs_r B1 B2 B3 :
  unique_bindings_fundefs B1 -> unique_bindings_fundefs B2 ->
  Disjoint var (bound_var_fundefs B1) (bound_var_fundefs B2) ->
  split_fds B1 B2 B3 ->
  unique_bindings_fundefs B3.
Proof.
  intros Hun1 Hun2 HD Hspl. induction Hspl; simpl.
  - inv Hun1. constructor; eauto.
    + intros Hc. apply H5. 
      eapply (split_fds_bound_vars) in Hc; eauto. inv Hc; eauto.
      inv HD. exfalso. eapply H0. now eauto.
    + rewrite split_fds_bound_vars; eauto.
      constructor. intros x H. inv H. inv H0; eauto.
      eapply H7. now eauto.
      eapply HD. now eauto.
    + rewrite split_fds_bound_vars; eauto.
      constructor. intros x H. inv H. inv H1; eauto.
      eapply H8. now eauto.
      eapply HD; now eauto.
    + eapply IHHspl; eauto. rewrite bound_var_fundefs_Fcons in HD.
      repeat apply Disjoint_Union_r in HD; eauto.
  - inv Hun2. constructor; eauto.
    + intros Hc. apply H5. 
      eapply (split_fds_bound_vars) in Hc; eauto. inv Hc; eauto.
      inv HD. exfalso. eapply H0. now eauto.
    + rewrite split_fds_bound_vars; eauto.
      constructor. intros x H. inv H. inv H0; eauto.
      eapply HD; now eauto.
      eapply H7. now eauto.
    + rewrite split_fds_bound_vars; eauto.
      constructor. intros x H. inv H. inv H1; eauto.
      eapply HD; now eauto.
      eapply H8. now eauto.
    + eapply IHHspl; eauto. rewrite bound_var_fundefs_Fcons in HD.
      apply Disjoint_sym in HD. repeat apply Disjoint_Union_r in HD; eauto.
      apply Disjoint_sym; eauto.
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
Proof.
  intros H Hun. induction B.
  - simpl in H.
    destruct (var_dec v f); subst.
    + inv H. inv H0.
      * exists Fnil. eexists. split; simpl; eauto.
        split; try (now intros Hc; inv Hc). split; try (now inv Hun; eauto).
        rewrite Union_Empty_set_r, Setminus_Union_distr, Setminus_Empty_set,
        Union_Empty_set_r. apply Same_set_sym. eapply Setminus_Disjoint.
        apply Disjoint_Singleton. intros Hc.
        apply fun_in_fundefs_name_in_fundefs in Hc.
        eapply fun_in_fundefs_Fcons_Disjoint; eauto.
      * exfalso. inv Hun. apply H6. eapply name_in_fundefs_bound_var_fundefs.
        eapply fun_in_fundefs_name_in_fundefs; eauto.
    + inv H. inv H0. congruence. inv Hun; eauto.
      edestruct IHB as [B1 [B2 [Heq [Hn [Hs Hun']]]]]; eauto.
      edestruct fundefs_append_unique_bindings_l as [H1 [H2 H3]];
        [ apply H12 | | ]; eauto.
      exists (Fcons v t0 l e0 B1), B2. rewrite Heq. split; eauto.
      split; [| split ].
      * intros H. apply Hn. inv H; eauto. inv H4. congruence.
      * simpl. rewrite Setminus_Union_distr, <- Union_assoc.
        apply Same_set_Union_compat.
        apply Same_set_sym. eapply Setminus_Disjoint.
        apply Disjoint_Singleton. intros Hc. inv Hc. congruence.
        apply Same_set_sym. 
        rewrite fundefs_append_fun_in_fundefs; eauto. simpl.
        rewrite !Setminus_Union_distr, Setminus_Empty_set, Union_Empty_set_r,
        <- Setminus_Union_distr.
        eapply Setminus_Disjoint. apply Disjoint_Union.
        eapply Disjoint_Singleton. intros Hc. eapply H3.
        constructor. eapply name_in_fundefs_bound_var_fundefs.
        eapply fun_in_fundefs_name_in_fundefs; eauto.
        rewrite bound_var_fundefs_Fcons; left. eauto.
        eapply Disjoint_Singleton. intros Hc. inv H2. eapply H17.
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
        apply Included_Union_compat; eauto using Included_refl.
        rewrite bound_var_fundefs_Fcons.
        rewrite !Union_assoc, Union_sym. apply Included_Union_l.
  - inv H.
Qed.

Lemma find_def_Included_fun_in_fundefs f B B' :
  unique_bindings_fundefs B ->
  unique_bindings_fundefs B' ->
  Included _ (fun_in_fundefs B) (fun_in_fundefs B') ->
  name_in_fundefs B f ->
  find_def f B = find_def f B'.
Proof.
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
      rewrite <- (Setminus_Disjoint (fun_in_fundefs B) (Singleton _ (v, t0, l, e))).
      rewrite <- Setminus_Union_Inlcluded; eauto using Included_refl.
      eapply Included_Setminus_compat; eauto using Included_refl.
      now rewrite Union_sym.  
      eapply Disjoint_Singleton. inv Hun; eauto. intros Hc. apply H6.
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
Proof.
  intros Hsp1 Hsp2 Hsp3 Hun.
  edestruct split_fds_unique_bindings_fundefs_l as [H1 [H2 H3]]; eauto.
  assert (Hun2 : unique_bindings_fundefs B2).
  { eapply split_fds_unique_bindings_fundefs_r; [ | | | now apply Hsp2 ]; eauto.
    - inv H2. rewrite bound_var_Efun in *. constructor; eauto.
      now eapply Disjoint_Union_r; eauto.
      now eapply Disjoint_Union_r; eauto.
      now inv H13; eauto.
    - rewrite bound_var_fundefs_Fcons in *.
      eapply Disjoint_Included_r; eauto.
      repeat apply Included_Union_compat; eauto using Included_refl.
      rewrite bound_var_Efun. apply Included_Union_r. }
  edestruct split_fds_unique_bindings_fundefs_l as [H1' [H2' H3']]; eauto.
  eapply split_fds_unique_bindings_fundefs_r; [ | | | eauto]; eauto.
  inv H2. inv H13; eauto. inv H2.
  rewrite (split_fds_bound_vars B1 (Fcons f tau xs e Fnil) B2); eauto.
  rewrite bound_var_fundefs_Fcons in *. rewrite bound_var_Efun in *.
  apply Disjoint_sym. apply Disjoint_Union.
  eapply Disjoint_Included_r; [| eapply H3 ].
  rewrite Union_assoc, Union_sym, <- !Union_assoc.
  apply Included_Union_l.
  apply Disjoint_Union. eapply Disjoint_sym. eapply Disjoint_Singleton.
  intros Hc. apply H7. eapply Bound_Efun1; eauto.
  apply Disjoint_Union. eapply Disjoint_sym.
  eapply Disjoint_Included_l; [| eapply H9 ].
  apply Included_Union_l.
  rewrite bound_var_fundefs_Fnil, Union_Empty_set_l.
  now inv H13.
Qed.

Lemma unique_bindings_split_fds_Fcons_fundefs_append B1 B2 B3 B f tau xs e  :
  split_fds B1 (Fcons f tau xs e Fnil) B3 ->
  split_fds B2 B3 B ->
  unique_bindings_fundefs B ->
  unique_bindings_fundefs (fundefs_append (Fcons f tau xs e B1) B2).
Proof.
  intros H1 H2 Hun.
  edestruct split_fds_unique_bindings_fundefs_l as [H1' [H2' H3']];
  [| apply H2 |]; eauto.
  edestruct split_fds_unique_bindings_fundefs_l as [H4' [H5' H6']];
    [| apply H1 |]; eauto.
  eapply fundefs_append_unique_bindings_r; eauto.
  eapply fundefs_append_unique_bindings_r
  with (B1 := Fcons f tau xs e Fnil) (B2 := B1); eauto.
  inv H5'; eauto. now apply Disjoint_sym.
  rewrite bound_var_fundefs_Fcons.
  rewrite (split_fds_bound_vars B1 (Fcons f tau xs e Fnil) B3) in H3'; eauto.
  rewrite bound_var_fundefs_Fcons, bound_var_fundefs_Fnil,
  Union_Empty_set_l in H3'.
  rewrite !Union_assoc, Union_sym, <- !Union_assoc. now apply Disjoint_sym.
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
Proof.
  intros H1 H2.
  rewrite (split_fds_fun_in_fundefs B3 B4 B); eauto;
  rewrite (split_fds_fun_in_fundefs B1 B2 B4); eauto.
  rewrite (fundefs_append_fun_in_fundefs (fundefs_append B2 B1) B3); eauto.
  rewrite (fundefs_append_fun_in_fundefs B2 B1); eauto.
  rewrite (Union_sym (Union _ _ _) _),
  (Union_sym (fun_in_fundefs B2) (fun_in_fundefs B1)).
  apply Same_set_refl.
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
Proof.
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
    + rewrite bound_var_comp. eassumption. now apply Same_set_sym.
    + rewrite bound_var_comp. eassumption. now apply Same_set_sym.
  - intros e1 e2 Hun Hun' HS.
    inv Hun. constructor; [| eassumption |].
    eapply IHc; eassumption.
    rewrite bound_var_comp. eassumption. now apply Same_set_sym.
  - intros e1 e2 Hun Hun' HS.
    inv Hun. constructor; [eassumption | |].
    eapply IHf; eassumption.
    rewrite bound_var_fundefs_comp. eassumption. now apply Same_set_sym.
  - intros e1 e2 Hun Hun' HS.
    inv Hun. constructor; try eassumption.
    + intros Hc. apply H4.
      eapply bound_var_comp; eassumption.
    + rewrite bound_var_comp. eassumption. now apply Same_set_sym.
    + rewrite bound_var_comp. eassumption. now apply Same_set_sym.
    + eapply IHc; eassumption.
  - intros e1 e2 Hun Hun' HS.
    inv Hun. constructor; try eassumption.
    + intros Hc. apply H5.
      eapply bound_var_fundefs_comp; eassumption.
    + rewrite bound_var_fundefs_comp. eassumption. now apply Same_set_sym.
    + rewrite bound_var_fundefs_comp. eassumption. now apply Same_set_sym.
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
    | Econstr x tau c ys e =>
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
    | Eapp x xs =>
      union_list (singleton x) xs
    | Eprim x tau prim ys e =>
      let set := remove x (exp_fv e) in
      union_list set ys
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
  induction defs; simpl; intros f; split; intros H; try now inv H.
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
  * occurs_free_fundefs *)
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
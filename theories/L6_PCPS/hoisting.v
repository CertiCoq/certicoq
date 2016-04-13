Require Import cps cps_util identifiers eval env ctx.
Require Import List BinNat Relations.

Import ListNotations.

(* TODO : move dependencies from shrink_cps to common file *)

Fixpoint exp_hoist (e : exp) (defs : fundefs)
         (f : exp * fundefs -> exp * fundefs) {struct e} : exp * fundefs :=
  match e with
    | Econstr x typ tag ys e' =>
      exp_hoist e' defs (fun p => let (e, defs) := p in
                                  f (Econstr x typ tag ys e, defs))
    | Ecase x tes =>
      fold_left
        (fun (f : exp * fundefs -> exp * fundefs) (te : tag * exp) =>
           fun p =>
             let (c, e) := te in
             let (e1, defs1) := p in
             exp_hoist e defs1
                       (fun p2 =>
                          let (e2, defs2) := p2 in
                          match e1 with
                            | Ecase x' tes' =>
                              f (Ecase x' ((c, e2) :: tes), defs2)
                            | _ => (* This should never match *)
                              f (Ecase x [(c, e2)], defs2)
                          end)) tes f (Ecase x tes, defs)
    | Eproj x typ n y e' =>
      exp_hoist e' defs (fun p =>
                           let (e, defs) := p in
                           f (Eproj x typ n y e, defs))
    | Efun fdefs e' =>
      exp_hoist e' defs (fun p =>
                           let (e'', defs'') := p in
                           fundefs_hoist fdefs e'' defs'' f)
    | Eapp g xs =>
      f (Eapp g xs, defs)
    | Eprim x typ prim ys e' =>
      exp_hoist e' defs (fun p =>
                           let (e', defs') := p in
                           f (Eprim x typ prim ys e', defs'))
  end
with fundefs_hoist (defs : fundefs) (e : exp) (hdefs : fundefs)
                   (f : exp * fundefs -> exp * fundefs) {struct defs}
     : exp * fundefs :=
       match defs with 
         | Fcons g t xs e defs =>
           fundefs_hoist defs e hdefs
                         (fun p1 =>
                            let (e1, defs1) := p1 in
                            exp_hoist e defs1
                                      (fun p2 =>
                                         let (e2, defs2) := p1 in
                                         (e1, Fcons g t xs e2 defs2)))
         | Fnil => f (e, hdefs)
  end.



(** expressions without function definitions *)
Inductive no_fun : exp -> Prop  :=
| Econstr_no_fun :
    forall x tau t xs e,
      no_fun e ->
      no_fun (Econstr x tau t xs e)
| Ecase_no_fun :
    forall x txs, no_fun (Ecase x txs)
| Eproj_no_fun :
    forall x tau n y e,
      no_fun e ->
      no_fun (Eproj x tau n y e)
| Eapp_no_fun :
    forall x ys, no_fun (Eapp x ys)
| Eprim_no_fun :
    forall x tau p xs e,
      no_fun e ->

      no_fun (Eprim x tau p xs e).

(** function definitions without nested function definitions *)
Inductive no_fun_defs : fundefs -> Prop  :=
| Fcons_no_fun :
    forall f tau xs e defs,
      no_fun e ->
      no_fun_defs defs ->
      no_fun_defs (Fcons f tau xs e defs)
| Fnil_no_fun :
    no_fun_defs Fnil.

Hint Constructors no_fun no_fun_defs.

(** hoisting as a rewrite relation *)
Inductive hoist_rw : relation exp :=
| hoist1 :
    forall e1 e2 defs defs' defs'' e c,
      split_fds defs defs' defs'' ->
      no_fun_defs defs' ->
      app_ctx (Efun1_c defs c) (Efun defs' e) e1 ->
      app_ctx (Efun1_c defs'' c) e e2 ->
      hoist_rw e1 e2.

(** reflexive transitive closure, parametrized by the 
    number of steps for induction *)
Inductive hoist_star_n : nat -> relation exp :=
| hoistn_step :
    forall e1 e2 e3 n, hoist_rw e1 e2 ->
                  hoist_star_n n e2 e3 ->
                  hoist_star_n (S n) e1 e3
| hoistn_refl :
    forall e, hoist_star_n 0 e e.

Definition hoist_star (e1 e2: exp) : Prop :=
  exists n, hoist_star_n n e1 e2.

(** Hoisting normal form *)
Definition hoist_nf (e : exp) :=
  ~ exists e', hoist_rw e e'.


Definition injective {A B} (f : A -> B) :=
  forall x y, f x = f y -> x = y.

Lemma injective_comp {A B C} (f : A -> B) (g : B -> C) :
  injective f -> injective g ->
  injective (fun x => g (f x)).
Proof.
  unfold injective; eauto.
Qed.

(* The following need to be updated.

Lemma exp_fundefs_hoist_no_fun:
  (forall e,
   exists g e',
     (forall defs f,
        exp_hoist e defs f = Efun (g defs) (f e')) /\
     injective g /\
     (forall defs, no_fun_defs defs -> no_fun_defs (g defs)) /\
     no_fun e') /\
  (forall defs,
   exists g,
     (forall hdefs f,
        fundefs_hoist defs hdefs f = f (g hdefs)) /\
     injective g /\
     forall defs, no_fun_defs defs -> no_fun_defs (g defs)).
Proof.
  exp_defs_induction IHe IHl IHf;
  intros; try edestruct IHe as [g1 [? [H1 [H2 [H3 H4]]]]];
  try edestruct IHf as [g2 [H5 [H6 H7]]];
  try (now do 2 eexists; 
       simpl; split; [ intros defs f; rewrite H1; eauto | split; eauto ]);
  try (now exists id; repeat eexists; intros; unfold injective; eauto).
  simpl. exists (fun x => g1 (g2 x)); eexists.
  split; intros. rewrite H1, H5; eauto.
  split; eauto using injective_comp.
  simpl. exists (fun d => Fcons v t l x (g2 (g1 d))). split.
  intros; simpl. rewrite H1, H5; eauto. 
  split; eauto using injective_comp. 
  eapply injective_comp; eauto using injective_comp.
  intros x1 x2 Heq; inv Heq; eauto.
Qed.

Corollary exp_hoist_head_no_fun e :
  exists e' g,
    (forall defs f, exp_hoist e defs f = Efun (g defs) (f e')) /\
    no_fun e'.
Proof.
  destruct exp_fundefs_hoist_no_fun as [H1 _].
  destruct (H1 e) as [? [? H2]]. do 2 eexists.
  split; eapply H2; eauto.
Qed.

Corollary exp_hoist_head e :
  exists e' g,
    forall defs f, exp_hoist e defs f = Efun (g defs) (f e').
Proof.
  destruct exp_fundefs_hoist_no_fun as [H1 _].
  destruct (H1 e) as [? [? H2]]. do 2 eexists. 
  intros; eapply H2; eauto.
Qed.

Lemma exp_hoist_f_comp :
  forall e e' defs hdefs f1 f2,
    exp_hoist e defs f1 = Efun hdefs (f1 e') ->
    exp_hoist e defs (fun x => f2 (f1 x)) = Efun hdefs (f2 (f1 e')).
Proof.
  intros e e' defs defs' g g' H.
  destruct (exp_hoist_head e) as [e'' [g'' H']].
  rewrite H' in H. inv H.
  rewrite H'. eauto.
Qed.



Lemma hoist_star_0 :
  forall e e', hoist_star_n 0 e e' -> e = e'.
Proof.
  assert (H : 0%nat = 0%nat) by reflexivity.
  revert H. generalize 0%nat at 1 3.
  intros n  Heq e e' H. induction H; eauto; subst. congruence.
Qed.

Lemma hoist_star_n_trans n m e1 e2 e3:
  hoist_star_n n e1 e2 ->
  hoist_star_n m e2 e3 ->
  hoist_star_n (n+m) e1 e3.
Proof.
  intros H1 H2. induction H1; eauto.
  econstructor 1; eauto.
Qed.

Lemma hoist_star_trans e1 e2 e3:
  hoist_star e1 e2 ->
  hoist_star e2 e3 ->
  hoist_star e1 e3.
Proof.
  intros [n H1] [m H2].
  assert (H := hoist_star_n_trans n m e1 e2 e3 H1 H2).
  eexists; eauto.
Qed.

Definition is_exp_ctx_f (f : exp -> exp) :=
  exists c, forall e, app_ctx_f c e = f e.

Definition is_def_ctx_f (h : exp -> fundefs) :=
  exists c, forall e, app_f_ctx_f c e = h e.

Definition is_def_ctx_defs (f : fundefs -> fundefs) := 
  forall h, is_def_ctx_f h -> is_def_ctx_f (fun e => f (h e)).

Lemma is_exp_ctx_f_comp (f1 f2 : exp -> exp) :
  is_exp_ctx_f f1 -> is_exp_ctx_f f2 ->
  is_exp_ctx_f (fun x => f1 (f2 x)).
Proof.
  intros [c1 H1] [c2 H2].
  eexists (comp_ctx_f c1 c2). intros e.
  rewrite <- app_ctx_f_fuse. rewrite H1. f_equal; eauto.
Qed.

Lemma is_def_ctx_f_comp f1 f2 :
  is_def_ctx_defs f1 -> is_def_ctx_f f2 ->
  is_def_ctx_f (fun x => f1 (f2 x)).
Proof.
  eauto.
Qed.

Lemma is_exp_ctx_f_defs f e :
  is_def_ctx_f f -> 
  is_exp_ctx_f (fun x : exp => Efun (f x) e).
Proof.
  intros [c1 H1].
  eexists (Efun2_c c1 e). intros e1. simpl.
  f_equal; eauto.
Qed.

(** hoisting is in the reflexive transitive closure of the rewrite relation *)
Lemma exp_fundefs_hoist_in_hoist_star :
  (forall e defs f,
     is_exp_ctx_f f -> 
     hoist_star (Efun defs (f e)) (exp_hoist e defs f)) /\
  (forall defs e hdefs f g,
     (forall d, no_fun_defs d -> no_fun_defs (f d)) ->
     is_exp_ctx_f g ->
     is_def_ctx_defs f ->
     (forall d1 d2 d,
        split_fds d1 d2 d ->
        split_fds d1 (f d2) (f d)) ->
     hoist_star (Efun hdefs (g (Efun (f defs) e)))
                (Efun (fundefs_hoist defs hdefs f) (g e))).
Proof.
  apply exp_def_mutual_ind;
  [intros x typ tag ys e IHe  fdefs f Hctx | intros x fdefs f Hctx
   | intros x tes c e IHe IHl fdefs f Hctx
   | intros x typ n y e IHe fdefs f Hctx | intros defs IHdefs e IHe fdefs f Hctx
   | intros g xs fdefs f Hctx
   | intros x  typ pr ys e IHe fdefs f Hctx
   | intros g typ xs e IHe defs IHdefs e' hdefs f h Hnf Hctx Hctx' Hsp
   | intros e' hdefs f h Hnf Hctx Hctx' Hsp].
  - simpl.
    specialize (IHe fdefs (fun e => f (Econstr x typ tag ys e))).
    apply IHe.
    destruct Hctx as [c Hctx].
    eexists (comp_ctx_f c (Econstr_c x typ tag ys Hole_c)).
    intros e'. rewrite <- Hctx. now rewrite <- app_ctx_f_fuse. 
  - eexists. apply hoistn_refl.
  -  

    - simpl. specialize (IHe fdefs (fun e => f (Eproj x typ n y e))).
    apply IHe.
    destruct Hctx as [c Hctx].
    eexists (comp_ctx_f c (Eproj_c x typ n y Hole_c)).
    intros e'. rewrite <- Hctx. now rewrite <- app_ctx_f_fuse.
  - simpl. specialize (IHe (fundefs_hoist defs fdefs id) f).
    eapply hoist_star_trans; eauto. 
    specialize (IHdefs e fdefs id f). eapply IHdefs; eauto.
    unfold is_def_ctx_defs; eauto.
  - eexists. apply hoistn_refl.
  - simpl. specialize (IHe fdefs (fun e => f (Eprim x typ pr ys e))).
    apply IHe.
    destruct Hctx as [c Hctx].
    eexists (comp_ctx_f c (Eprim_c x typ pr ys Hole_c)).
    intros e'. rewrite <- Hctx. now rewrite <- app_ctx_f_fuse.
  - simpl. destruct (exp_hoist_head_no_fun e) as [e1 [g' [H1 H2]]]. rewrite H1.
    specialize (IHe hdefs (fun e => h (Efun (f (Fcons g typ xs e defs)) e'))).
    rewrite H1 in IHe; simpl in *.     
    specialize
      (IHdefs e' (g' hdefs) (fun defs => f (Fcons g typ xs e1 defs)) h).
    simpl in *.
    eapply hoist_star_trans; [ eapply IHe | eapply IHdefs ]; eauto.
    apply is_exp_ctx_f_comp; eauto.
    eapply is_exp_ctx_f_defs with (f := fun x => f (Fcons g typ xs x defs)).
    eapply Hctx'. exists (Fcons1_c g typ xs Hole_c defs).
    intros; eauto. intros. 
    intros g1 [c Hg1]. eapply is_def_ctx_f_comp; eauto.
    exists (Fcons2_c g typ xs e1 c). intros; simpl; f_equal; eauto.
    intros d1 d2 d Hds. eapply Hsp. constructor; eauto.
  - simpl. eexists. econstructor 1; [| econstructor 2].
    destruct Hctx as [c Hctx].
    eapply hoist1 with (defs := hdefs) (defs' := f Fnil); eauto.
    eapply Hsp. apply split_fds_nil_l.
    apply app_ctx_f_correct. simpl. f_equal; eauto.
    apply app_ctx_f_correct. simpl. f_equal; eauto.
Qed.

Open Scope ctx_scope.
Open Scope env_scope.

Lemma preord_env_permut k x y v1 v2 rho1 rho2 :
  x <> y ->
  preord_env k (M.set x v1 (M.set y v2 rho1)) (M.set x v1 (M.set y v2 rho2)) ->
  preord_env k (M.set x v1 (M.set y v2 rho1)) (M.set y v2 (M.set x v1 rho2)).
Proof.
  intros Hneq Hpre x' v1' Hget.
  rewrite M.gsspec in Hget.
  destruct (Coqlib.peq x' x). inv Hget. 
  - edestruct (Hpre x) as [v1'' [Hget'' Hpre'']]. rewrite M.gss; eauto.
    rewrite M.gss in Hget''; inv Hget''.
    eexists. rewrite M.gso; eauto. rewrite M.gss; eauto.
  - edestruct (Hpre x') as [v1'' [Hget'' Hpre'']].
    rewrite M.gso; eauto. rewrite M.gsspec in Hget.
    destruct (Coqlib.peq x' y). inv Hget.
    + eexists. rewrite M.gss; eauto. split; eauto.
      eapply preord_val_refl.
    + do 2 (rewrite M.gso in Hget''; eauto).
      eexists. split; eauto.
      do 2 (rewrite M.gso; eauto).
Qed.

Lemma def_funs_spec x v defs rho rho' :
  M.get x (def_funs defs defs rho rho') = Some v ->
  (name_in_fundefs x defs /\ v = cps.Vfun rho defs x) \/
  (~ name_in_fundefs x defs /\ M.get x rho' = Some v).
Proof.
  generalize defs at 1 4. induction defs; intros defs' Hget.
  - simpl in Hget. rewrite M.gsspec in Hget. destruct (Coqlib.peq x v0).
    + inv Hget. left. split; eauto. constructor; eauto.
    + edestruct (IHdefs _ Hget) as [[H1 H2] | [H1 H2]]; eauto.
      * left. split; eauto. constructor 2; eauto.
      * right. split; eauto. intros Hc. inv Hc; try congruence.
  - simpl in Hget. right. split; eauto.
Qed.

Lemma def_funs_eq x defs rho rho' :
  name_in_fundefs x defs ->
  M.get x (def_funs defs defs rho rho') = Some (cps.Vfun rho defs x).
Proof.
  generalize defs at 2 4. induction defs; intros defs' Hin; inv Hin.
  - simpl. rewrite M.gss. eauto.
  - simpl. rewrite M.gsspec. destruct (Coqlib.peq x v); subst; eauto.
Qed.

Lemma def_funs_neq x defs rho rho' :
  ~ name_in_fundefs x defs ->
  M.get x (def_funs defs defs rho rho') = M.get x rho'.
Proof.
  generalize defs at 2. induction defs; intros defs' Hin; simpl; eauto.
  rewrite M.gsspec. destruct (Coqlib.peq x v); subst; eauto.
  exfalso. apply Hin. constructor; eauto. eapply IHdefs.
  intros Hc.  eapply Hin. constructor 2; eauto.
Qed.

Require Import Omega.

Lemma preord_env_def_funs_permut (k : nat) (f1 f2 : fundefs)
      (rho1 rho2 : env) :
  preord_env k rho1 rho2 ->
  (forall f, name_in_fundefs f f1 -> ~ name_in_fundefs f f2) ->
  preord_env k (def_funs f1 f1 rho1 (def_funs f2 f2 rho1 rho1))
             (def_funs f2 f2 rho2 (def_funs f1 f1 rho2 rho2)).
Proof.
  intros Henv Hname x v Hget.
  eapply def_funs_spec in Hget. destruct Hget as [[H1 H2] | [H1 H2]].
  - eexists. rewrite def_funs_neq; eauto. rewrite def_funs_eq; eauto.
    split; eauto. inv H2.
    rewrite preord_val_eq. intros vs1 vs2 j t1 xs1 e1 rho1'' Hlen Hdef Heq.
    edestruct (setlist_length (def_funs f1 f1 rho1 rho1)
                              (def_funs f1 f1 rho2 rho2)) as [rho2'' Hset]; eauto.
    do 4 eexists; repeat split; eauto. intros Hlt Hall.
    eapply preord_exp_refl.
    eapply preord_env_setlist_l. eapply preord_env_def_funs.
    eapply preord_env_monotonic; [| eauto]. omega. eauto. eauto. eauto.
  - eapply def_funs_spec in H2.
    destruct H2 as [[H3 H4] | [H3 H4]]; subst.
    + eexists. rewrite def_funs_eq; eauto. split; eauto.
      rewrite preord_val_eq. intros vs1 vs2 j t1 xs1 e1 rho1' Hlen Hdef Heq.
      edestruct (setlist_length (def_funs f2 f2 rho1 rho1)
                                (def_funs f2 f2 rho2 rho2)) as [rho2' Hset]; eauto.
      do 4 eexists; repeat split; eauto. intros Hlt Hall.
      eapply preord_exp_refl.
      eapply preord_env_setlist_l. eapply preord_env_def_funs.
      eapply preord_env_monotonic; [| eauto]. omega. eauto. eauto. eauto.
    + edestruct Henv as [v2 [Hget Hpre]]; eauto.
      eexists. rewrite def_funs_neq; eauto. rewrite def_funs_neq; eauto.
Qed.



Lemma preord_env_def_funs_weaken (k : nat) (f1 f2 : fundefs)
      (rho1 rho2 : env) :
  (forall f, name_in_fundefs f f1 -> ~ name_in_fundefs f f2) ->
  preord_env k (def_funs f1 f1 rho1 (def_funs f2 f2 rho1 rho1))
             (def_funs f2 f2 rho2 (def_funs f1 f1 rho2 rho2)) ->
  preord_env k (def_funs f1 f1 (def_funs f2 f2 rho1 rho1) (def_funs f2 f2 rho1 rho1))
             (def_funs f2 f2 (def_funs f1 f1 rho2 rho2) (def_funs f1 f1 rho2 rho2)).
Proof.
  intros Henv Hname x v Hget. 
  eapply def_funs_spec in Hget. destruct Hget as [[H1 H2] | [H1 H2]].
  - eexists. rewrite def_funs_neq; eauto. rewrite def_funs_eq; eauto.
    split; eauto. inv H2.
    rewrite preord_val_eq. intros vs1 vs2 j t1 xs1 e1 rho1'' Hlen Hdef Heq.
    edestruct (setlist_length (def_funs f1 f1 (def_funs f2 f2 rho1 rho1)
                                        (def_funs f2 f2 rho1 rho1))
                              (def_funs f1 f1 rho2 rho2)) as [rho2'' Hset]; eauto.
    do 4 eexists; repeat split; eauto. intros Hlt Hall. admit.
    (* eapply preord_exp_refl. *)
    (* eapply preord_env_setlist_l. eapply preord_env_def_funs. *)
    (* eapply preord_env_monotonic; [| eauto]. omega. eauto. eauto. eauto. *)
  - eapply def_funs_spec in H2.
    destruct H2 as [[H3 H4] | [H3 H4]]; subst.
    + eexists. rewrite def_funs_eq; eauto. split; eauto.
      rewrite preord_val_eq. intros vs1 vs2 j t1 xs1 e1 rho1' Hlen Hdef Heq.
      edestruct (setlist_length (def_funs f2 f2 rho1 rho1)
                                (def_funs f2 f2 (def_funs f1 f1 rho2 rho2)
                                          (def_funs f1 f1 rho2 rho2))) as [rho2' Hset]; eauto.
      do 4 eexists; repeat split; eauto. intros Hlt Hall.
      eapply preord_exp_refl. 
      eapply preord_env_setlist_l; eauto. eapply preord_env_def_funs.
      eapply preord_env_monotonic; [| eauto]. omega. eauto. eauto. eauto.
    + edestruct Henv as [v2 [Hget Hpre]]; eauto.
      eexists. rewrite def_funs_neq; eauto. rewrite def_funs_neq; eauto.
  Qed.

        
 *)   
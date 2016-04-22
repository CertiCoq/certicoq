Require Import cps cps_util identifiers eval env ctx relations.
Require Import List BinNat Relations Omega.

Import ListNotations.

(** Given an expression [e], [exp_hoist e B f] will return an expression [e']
  * and a block of function definitions [B']. [e'] is the function defintion 
  * erasure of [e] and [B] is exactly the function definitions of [e]. It's 
  * writen in a CPS fashion and [f] is the continuation. [B] is an accumulator
  * of function defitnions. 
  *)
Fixpoint erase_fundefs (e : exp) (defs : fundefs)
         (f : exp * fundefs -> exp * fundefs) {struct e} : exp * fundefs :=
  match e with
    | Econstr x typ tag ys e' =>
      erase_fundefs e' defs (fun p => let (e, defs) := p in
                                      f (Econstr x typ tag ys e, defs))
    | Ecase x tes =>
      fold_left
        (fun (f : exp * fundefs -> exp * fundefs) (te : tag * exp) =>
           fun p =>
             let (c, e) := te in
             let (e1, defs1) := p in
             erase_fundefs e defs1
                       (fun p2 =>
                          let (e2, defs2) := p2 in
                          match e1 with
                            | Ecase x' tes' =>
                              f (Ecase x' ((c, e2) :: tes'), defs2)
                            | _ => (* This should never match *)
                              f (Ecase x [(c, e2)], defs2)
                          end)) tes f (Ecase x [], defs)
    | Eproj x typ n y e' =>
      erase_fundefs e' defs (fun p =>
                           let (e, defs) := p in
                           f (Eproj x typ n y e, defs))
    | Efun fdefs e' =>
      erase_fundefs e' defs (fun p =>
                           let (e'', defs'') := p in
                           erase_nested_fundefs fdefs e'' defs'' f)
    | Eapp g xs =>
      f (Eapp g xs, defs)
    | Eprim x typ prim ys e' =>
      erase_fundefs e' defs (fun p =>
                           let (e', defs') := p in
                           f (Eprim x typ prim ys e', defs'))
  end
with erase_nested_fundefs (defs : fundefs) (e : exp) (hdefs : fundefs)
                          (f : exp * fundefs -> exp * fundefs) {struct defs}
     : exp * fundefs :=
       match defs with 
         | Fcons g t xs e' defs =>
           erase_nested_fundefs defs e hdefs
                                (fun p1 =>
                                   let (e1, defs1) := p1 in
                                   erase_fundefs e' defs1
                                                 (fun p2 =>
                                                    let (e2, defs2) := p2 in
                                                    f (e1, Fcons g t xs e2 defs2)))
         | Fnil => f (e, hdefs)
  end.

(** [exp_hoist e] moves all function definitions of [e] at the outermost level *)
Definition exp_hoist (e : exp) :=
  let (e, defs) := erase_fundefs e Fnil id in
  match defs with
    | Fnil => e
    | _ => Efun defs e
  end.

(** [erase_fundefs e e' B] iff [e'] is [e] after erasing all the function 
  *  defintion blocks and [B] is exactly the function definitions of [e] 
  *) 
Inductive Erase_fundefs : exp -> exp -> fundefs -> Prop :=
| Efun_erase :
    forall e e' defs Be Bdefs Be_defs,
      Erase_fundefs e e' Be ->
      Erase_nested_fundefs defs Bdefs ->
      split_fds Be Bdefs Be_defs ->
      Erase_fundefs (Efun defs e) e' Be_defs
| Econstr_erase :
    forall x tau t ys e e' B,
      Erase_fundefs e e' B ->
      Erase_fundefs (Econstr x tau t ys e)
                  (Econstr x tau t ys e') B
| Ecase_nil_erase :
    forall x,
      Erase_fundefs (Ecase x nil) (Ecase x nil) Fnil
| Ecase_cons_erase :
    forall x c e e' tes tes' B B' B'',
      Erase_fundefs (Ecase x tes) (Ecase x tes') B ->
      Erase_fundefs e e' B' ->
      split_fds B B' B'' ->
      Erase_fundefs (Ecase x ((c, e) :: tes)) (Ecase x ((c, e') :: tes')) B''
| Eproj_erase :
    forall x tau N y e e' B,
      Erase_fundefs e e' B ->
      Erase_fundefs (Eproj x tau N y e)
                    (Eproj x tau N y e') B
| Eapp_erase :
    forall f xs,
      Erase_fundefs (Eapp f xs) (Eapp f xs) Fnil
| Eprim_erase :
    forall x tau f ys e e' B,
      Erase_fundefs e e' B ->
      Erase_fundefs (Eprim x tau f ys e)
                    (Eprim x tau f ys e') B
with Erase_nested_fundefs : fundefs -> fundefs -> Prop :=
| Fcons_erase :
    forall f tau xs e e' defs B B' B'',
      Erase_fundefs e e' B ->
      Erase_nested_fundefs defs B' ->
      split_fds B (Fcons f tau xs e' B') B'' ->
      Erase_nested_fundefs (Fcons f tau xs e defs) B''
| Fnil_erase :
    Erase_nested_fundefs Fnil Fnil.

(** Correspondence between the inductive and the computational defintions
  * of function definition erasure 
  *)
Lemma erase_fundefs_in_Erase_fundefs :
  (forall e B f,
   exists e' B' B'',
     erase_fundefs e B f = f (e', B') /\
     split_fds B B'' B' /\
     Erase_fundefs e e' B'') /\
  (forall defs e B f,
    exists B' B'',
      erase_nested_fundefs defs e B f = f (e, B') /\
      split_fds B B'' B' /\
      Erase_nested_fundefs defs B'').
Proof.
  exp_defs_induction IHe IHl IHf; intros; simpl in *;
  try (now edestruct IHe as [e' [B' [B'' [Heq [Hsplit Her]]]]];
       repeat eexists; eauto; try rewrite Heq; try constructor; auto).
  - repeat eexists; eauto using split_fds_nil_l; repeat econstructor.
  - edestruct IHl as [e1' [B1' [B1'' [Heq1 [Hspl1 Her1]]]]]. 
    edestruct IHe as [e2' [B2' [B2'' [Heq2 [Hspl2 Her2]]]]].
    rewrite Heq1, Heq2. clear Heq1 Heq2.
    edestruct split_fds_trans as [B3 [H1 H2]]; [apply Hspl1 | |]; eauto.
    inv Her1; repeat eexists; eauto; econstructor; eauto; econstructor; eauto.
  - edestruct IHe as [e2 [B2 [B2' [Heq2 [Hspl2 Her2]]]]].
    edestruct IHf as [B1 [B1' [Heq1 [Hspl1 Her1]]]]; subst.
    edestruct split_fds_trans as [B3 [H1 H2]] ; [ | apply Hspl1 |]; eauto.
    repeat eexists. rewrite Heq2, Heq1; eauto. eauto. econstructor; eauto.
  - repeat eexists; eauto using split_fds_nil_l; repeat econstructor.
  - edestruct IHf as [B1 [B1' [Heq1 [Hspl1 Her1]]]]; subst.
    edestruct IHe as [e2 [B2 [B2' [Heq2 [Hspl2 Her2]]]]].
    edestruct split_fds_trans as [B3 [H1 H2]] ; [ apply Hspl1 | |]; eauto.
    repeat eexists. rewrite Heq1, Heq2; eauto.
    constructor; eauto. econstructor; eauto. constructor; eauto.
    apply split_fds_sym; eauto.
  - repeat eexists; eauto using split_fds_nil_l; repeat econstructor.
Qed.

(** Expressions without function definitions *)
Inductive no_fun : exp -> Prop  :=
| Econstr_no_fun :
    forall x tau t xs e,
      no_fun e ->
      no_fun (Econstr x tau t xs e)
| Ecase_nil_no_fun :
    forall x, no_fun (Ecase x [])
| Ecase_no_fun :
    forall x c e tes,
      no_fun (Ecase x tes) ->
      no_fun e ->
      no_fun (Ecase x ((c, e) :: tes))
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

(** Function definitions without nested function definitions *)
Inductive no_fun_defs : fundefs -> Prop  :=
| Fcons_no_fun :
    forall f tau xs e B,
      no_fun e ->
      no_fun_defs B ->
      no_fun_defs (Fcons f tau xs e B)
| Fnil_no_fun :
    no_fun_defs Fnil.

Hint Constructors no_fun no_fun_defs.

Lemma no_fun_split_fds B B' B'' :
  no_fun_defs B -> no_fun_defs B' ->
  split_fds B B' B'' ->
  no_fun_defs B''.
Proof.
  intros Hnf Hnf' Hsp. induction Hsp; eauto.
  - inv Hnf; constructor; eauto.
  - inv Hnf'; constructor; eauto.
Qed.


(** If [Erase_fundefs e e' B] then there are no function defintions 
    in [e'] and [B] *)
Lemma erase_fundefs_no_fun :
  (forall e e' B,
     Erase_fundefs e e' B ->
     no_fun e' /\ no_fun_defs B) /\
  (forall B B',
     Erase_nested_fundefs B B' ->
     no_fun_defs B').
Proof.
  exp_defs_induction IHe IHl IHf; intros; simpl;
  try (now inv H; edestruct IHe; eauto);
  try (now inv H; split; eauto).
  - inv H. edestruct IHe; eauto.
    edestruct IHl; eauto. 
    econstructor. eauto. eapply no_fun_split_fds; [ | | eauto]; eauto.
  - inv H. edestruct IHe; eauto. split. eauto.
    eapply no_fun_split_fds; [ | | eauto]; eauto.
  - inv H. edestruct IHe; eauto. 
    eapply no_fun_split_fds; [ | | eauto]; eauto.
  - inv H; eauto.
Qed.


(** Hoisting as a rewrite relation *)
Inductive hoist_rw : relation exp :=
| EConstr_hoist :
    forall x tau t ys B e,
      hoist_rw (Econstr x tau t ys (Efun B e))
               (Efun B (Econstr x tau t ys e))
| Ecase_hoist :
    forall x tes t e' tes' B,
      hoist_rw (Ecase x (tes ++ ((t, Efun B e') :: tes')))
               (Efun B (Ecase x (tes ++ ((t, e') :: tes'))))
| Eproj_hoist :
    forall x tau N y e B,
      hoist_rw (Eproj x tau N y (Efun B e))
               (Efun B (Eproj x tau N y e))
| Efun_hoist :
    forall B B' B'' e,
      split_fds B B' B'' ->
      hoist_rw (Efun B (Efun B' e)) (Efun B'' e)
| Eprim_hoist :
    forall x tau f ys e B,
      hoist_rw (Eprim x tau f ys (Efun B e))
               (Efun B (Eprim x tau f ys e))
| Fnil_hoist :
    forall e,
      hoist_rw (Efun (Fnil) e) e
| FCons_hoist :
    forall f tau xs e' e B1 B2 B3 B4 B,
      split_fds B1 (Fcons f tau xs (Efun B3 e') Fnil) B2 ->
      split_fds B1 (Fcons f tau xs e' Fnil) B4 ->
      split_fds B3 B4 B ->
      hoist_rw (Efun B2 e) (Efun B e).

Definition hoist_star (e1 e2: exp) : Prop :=
  exists n, refl_trans_closure_n (compat_closure hoist_rw) n e1 e2.

(** Number of function definitions in an expression *)
Fixpoint exp_fun_count (e : exp) : nat :=
  match e with
    | Econstr _ _ _ _ e | Eproj _ _ _ _ e
    | Eprim _ _ _ _ e => exp_fun_count e
    | Ecase _ P =>
      fold_left (fun n p => n + (exp_fun_count (snd p))) P 0
    | Efun B e => exp_fun_count e + fundefs_fun_count B
    | Eapp _ _ => 0
  end
with fundefs_fun_count (B : fundefs) : nat :=
       match B with
         | Fcons _ _ _ e B => 1 + exp_fun_count e + fundefs_fun_count B
         | Fnil => 0
       end.

Lemma split_fds_fundefs_fundefs_count B B' B'' :
  split_fds B B' B'' ->
  fundefs_fun_count B + fundefs_fun_count B' = fundefs_fun_count B''.
Proof.
  intros H. induction H; eauto; simpl; omega.
Qed.

(** The number of functions definitions is invariant w.r.t hoist_rw *)
Lemma exp_fun_count_invariant n :
  invariant hoist_rw (fun e => exp_fun_count e = n).
Proof.
  intros e1 e2 Heq Hrw; inv Hrw; simpl; eauto.
  - rewrite <- !fold_left_rev_right, !rev_app_distr.
    simpl. generalize (rev tes') as l', (rev tes) as l, 0.
    induction l'; intros l n; simpl. omega.
    rewrite <- IHl'. omega.
  - erewrite <- split_fds_fundefs_fundefs_count; eauto. omega.
  - apply split_fds_fundefs_fundefs_count in H.
    apply split_fds_fundefs_fundefs_count in H0.
    apply split_fds_fundefs_fundefs_count in H1. simpl in *.
    omega.
Qed.

Lemma fun_count_ctx_compat :
  (forall c e e', exp_fun_count e = exp_fun_count e' ->
                  exp_fun_count (c |[ e ]|) = exp_fun_count (c |[ e' ]|)) /\
  (forall fc e e', exp_fun_count e = exp_fun_count e' ->
                   fundefs_fun_count (fc <[ e ]>) =
                   fundefs_fun_count (fc <[ e' ]>)).
Proof.
  exp_fundefs_ctx_induction IHc IHfc; try now intros e1 e2 Heq; simpl; eauto.
  simpl. intros l' e1 e2 Heq.
  rewrite <- !fold_left_rev_right, !rev_app_distr.
  simpl. generalize (rev l') as l1, (rev l) as l2, 0.
  induction l1; intros l2 n; simpl.
  now erewrite IHc; eauto.
  rewrite IHl1. omega.
Qed.

(** The number of functions definitions is invariant w.r.t hoist_star *)
(* TODO : refactor this proof so that it uses the generic lemmas in relations.v *)
Lemma exp_fun_cnt_refl_trans_clo_invariant m n :
  invariant (refl_trans_closure_n (compat_closure hoist_rw) m)
            (fun e => exp_fun_count e = n).
Proof.
  intros e1 e2 H1 Hstar.
  revert e1 e2 H1 Hstar. induction m; intros e1 e2 H1 Hstar.
  - inv Hstar. eauto. 
  - inv Hstar. inv H0. eapply IHm; [| eauto ].
    apply fun_count_ctx_compat.
    eapply exp_fun_count_invariant; eauto.
Qed.

Lemma hoist_rw_Ecase_cons x c e tes tes' :
  hoist_rw (Ecase x tes) (Ecase x tes') ->
  hoist_rw (Ecase x ((c, e) :: tes)) (Ecase x ((c, e) :: tes')).
Proof.
  intros Hrw. inv Hrw.
Qed.

Lemma no_fun_Ecase_Efun x tes c B e tes' :
  ~ (no_fun (Ecase x (tes ++ ((c, Efun B e) :: tes')))).
Proof.
  induction tes; simpl; intros Hc; inv Hc; eauto. inv H4.
Qed.
  
Lemma invariant_no_fun :
  invariant hoist_rw no_fun.
Proof.
  intros e1 e2 Hnf Hrw. inv Hnf; inv Hrw; try now inv H.
  - apply app_eq_nil in H1. inv H1. inv H0.
  - destruct tes0; simpl in *. inv H3.
    + inv H0.
    + inv H3. exfalso. eapply no_fun_Ecase_Efun; eauto.
Qed.

Lemma ctx_compat_no_fun :
  ctx_compat no_fun.
Proof.
  split.
  - induction c; simpl; intros e1 e2 Hnf1 Hnf2; inv Hnf1; eauto.
    + symmetry in H1. apply app_eq_nil in H1. inv H1. inv H0.
    + revert c0 e tes l0 H1 H2 H0. induction l; intros c0 e tes l0 H1 H2 H0.
      * simpl in *. inv H0. constructor; eauto.
      * inv H1.
        inv H0. symmetry in H3. apply app_eq_nil in H3. inv H3. inv H0.
        inv H0. simpl. constructor; eauto. 
  - induction c; simpl; intros e1 Hnf; eauto; try inv Hnf; eauto.
    + symmetry in H1. apply app_eq_nil in H1. inv H1. inv H0.
    + revert c0 e tes l0 H1 H2 H0. induction l; intros c0 e tes l0 H1 H2 H0.
      * inv H0; eauto.
      * simpl in H0; inv H0. inv H1.
        symmetry in H3. apply app_eq_nil in H3. inv H3. inv H0.
        eapply IHl; eauto.
Qed.

Ltac exp_to_ctx e c :=
  match e with
    | Econstr ?x ?tau ?t ?ys ?e => constr:(Econstr_c x tau t ys c)
    | Ecase ?x (?tes ++ (?t, ?e) :: ?tes') => constr:(Ecase_c x tes t e c tes')
    | Eproj ?x ?tau ?N ?y ?e => constr:(Eproj_c x tau N y c)
    | Efun ?B ?e => constr:(Efun1_c B c)
    | Eprim ?x ?tau ?f ?ys ?e => constr:(Eprim_c x tau f ys c)
  end.

Fixpoint f c e' e : exp :=
  match e with
    | Econstr x tau t ys e =>
      Econstr x tau t ys (f c e' e)
    | Ecase x l => Ecase x ((c, e') :: l)
    | Eproj x tau t y e =>
      Eproj x tau t y (f c e' e)
    | Efun B e => Efun B (f c e' e)
    | Eapp x x0 => e
    | Eprim x tau f' ys e =>
      Eprim x tau f' ys (f c e' e)
  end.

Inductive g (f' : var) (tau' : type) (xs' : list var) (e' : exp)
: exp -> exp -> Prop :=
| g_constr :
    forall x tau t ys e1 e2,
      g f' tau' xs' e' e1 e2 ->
      g f' tau' xs' e' (Econstr x tau t ys e1) (Econstr x tau t ys e2)
| g_proj :
    forall x tau N y e1 e2,
      g f' tau' xs' e' e1 e2 ->
      g f' tau' xs' e' (Eproj x tau N y e1) (Eproj x tau N y e2)
| g_fun1 :
    forall B e,
      B <> Fnil ->
      g f' tau' xs' e' (Efun B e) (Efun (Fcons f' tau' xs' e' B) e)
| g_fun2 :
    forall B e,
      B <> Fnil ->
      g f' tau' xs' e' (Efun B e) (Efun B e)
| g_fun_Fnil :
    forall e1 e2,
      g f' tau' xs' e' e1 e2 ->
      g f' tau' xs' e' (Efun Fnil e1) (Efun Fnil e2)
| g_prim :
    forall x tau f ys e1 e2,
      g f' tau' xs' e' e1 e2 ->
      g f' tau' xs' e' (Eprim x tau f ys e1) (Eprim x tau f ys e2)
(* | g_relf : *)
(*     forall e, g f' tau' xs' e' e e. *)
| g_app :
    forall f xs,
      g f' tau' xs' e' (Eapp f xs) (Eapp f xs)
 | g_case :
     forall x P,
       g f' tau' xs' e' (Ecase x P) (Ecase x P).


Lemma hoist_star_Ecase_cons_1 x c e tes tes' :
  hoist_star (Ecase x tes) (Ecase x tes') ->
  hoist_star (Ecase x ((c, e) :: tes)) (Ecase x ((c, e) :: tes')).
Proof.
  intros [n Hrwstar]. exists n.
  apply (refl_trans_closure_f_compat (compat_closure hoist_rw) n
                                     (Ecase x tes) (Ecase x tes')
                                     (f c e)); eauto.
  intros e1 e2.
  apply (compat_closure_f_compat hoist_rw e1 e2 (f c e)); eauto.
  - intros e1' e2' Hrw; eauto. inv Hrw; simpl; try now constructor.
    eapply Ecase_hoist with (tes := (c, e) :: tes0).
    econstructor; eauto.
  - intros c'. 
    induction c'; simpl;
    try (now destruct IHc' as [[c1 Heq] | [c1 Heq]]; [left | right];
         match goal with
           | [|- exists c, forall e, ?Ctx (?g (?c' |[ _ ]|))  = _ ]  =>
             let c := (exp_to_ctx (Ctx (c' |[ e1 ]|)) c1)
               in exists c 
                         end; simpl; intros e3; rewrite Heq; eauto).
    + left. exists Hole_c; eauto.
    + right. exists (Ecase_c v ((c, e) :: l) t c' l0); eauto.
    + right. exists (Efun2_c f0 (f c e e0)); eauto.
Qed.


(* This lemma should not be used. Insted we should find a way to use 
 * the more general lemma compat_closure_g_compat in relations.v *)
Lemma compat_closure_g_compat (R : relation exp) e1 e2 e1' x tau xs e' :
  (forall e1 e2 e1', R e1 e2 -> g x tau xs e' e1 e1' ->
                     exists e2', R e1' e2' /\ g x tau xs e' e2 e2') ->
  g x tau xs e' e1 e1' ->
  compat_closure R e1 e2 ->
  exists e2', compat_closure R e1' e2' /\ g x tau xs e' e2 e2'.
Proof.
  intros Hyp Hr' H. inv H.
  revert e e'0 e' e1' Hyp H0 Hr'.
  induction c; intros  e3 e4 e1 e2 Hyp H0 Hr'; simpl in *.
  - edestruct Hyp as [e2'' [Hrw2 Hr2]]; eauto.
    eexists.  split. apply Compat with (c := Hole_c); eauto. eauto.
  - inv Hr'. edestruct IHc as [e2'' [Hrw2 Hr2]]; eauto. 
    eexists; split; eauto.
    eapply compat_closure_compat with (c:= Econstr_c v t t0 l Hole_c). eauto.
    constructor. eauto.
  - inv Hr'. edestruct IHc as [e2'' [Hrw2 Hr2]]; eauto. 
    eexists; split; eauto.
    eapply compat_closure_compat with (c:= Eproj_c v t n v0 Hole_c). eauto.
    constructor. eauto.
  - inv Hr'. edestruct IHc as [e2'' [Hrw2 Hr2]]; eauto. 
    eexists; split; eauto.
    eapply compat_closure_compat with (c:= Eprim_c v t p l Hole_c). eauto.
    constructor. eauto.
  - inv Hr'. eexists.  split; try now constructor.
    apply Compat with (c := Ecase_c v l t c l0); eauto.
  - inv Hr'.
    + eexists. split.
      apply Compat with (c := Efun1_c (Fcons x tau xs e1 f0) c); eauto.
      constructor; eauto.
    + eexists. split.
      apply Compat with (c := Efun1_c f0 c); eauto.
      constructor; eauto.
    + edestruct IHc as [e2'' [Hrw2 Hr2]]; eauto.  
      eexists; split; eauto. 
      eapply compat_closure_compat with (c:= Efun1_c Fnil Hole_c). eauto.
      constructor; eauto.
  -  inv Hr'.
    + eexists. split.
      apply Compat with (c := Efun2_c (Fcons2_c x tau xs e1 f0) e); eauto.
      constructor; eauto. destruct f0; simpl; congruence.
    + eexists. split.
      apply Compat with (c := Efun2_c f0 e); eauto.
      constructor; eauto. destruct f0; simpl; congruence.
    + destruct f0.  inv H. inv H.
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

Lemma hoist_star_Efun_cons
      f tau xs e' f1 tau1 xs1 e1' f2 tau2 xs2 e2' B1 B2 e :
  hoist_star (Efun (Fcons f1 tau1 xs1 e1' B1) e)
             (Efun (Fcons f2 tau2 xs2 e2' B2) e) ->
  hoist_star (Efun (Fcons f tau xs e' (Fcons f1 tau1 xs1 e1' B1)) e)
             (Efun (Fcons f tau xs e' (Fcons f2 tau2 xs2 e2' B2)) e).
Proof.
  intros [n Hrwstar]. exists n.
  edestruct
    (refl_trans_closure_R_compat (compat_closure hoist_rw) n (g f tau xs e')
                                 (Efun (Fcons f1 tau1 xs1 e1' B1) e)
                                 (Efun (Fcons f2 tau2 xs2 e2' B2) e)); simpl; eauto.
  intros e1 e2 e1'' Hr Hrw.
  apply (compat_closure_g_compat hoist_rw e1 e2); eauto.
  - intros e3 e4 e3' Hrw' Hg.
    inv Hrw'; try (now inv Hg; try inv H5;
                   eexists; split; constructor; eauto; try (constructor; eauto)).
    + inv Hg. eexists. split; try now constructor.
      destruct B. constructor; congruence.
      apply g_fun_Fnil. constructor.
    + inv Hg.
      * eexists; split; eauto.
        econstructor; constructor; eauto.
        constructor; eauto using split_fds_Fcons_l.
      * eexists; split. constructor; eauto.
        constructor; eauto using split_fds_Fcons_l.
      * eexists; split. constructor.
        apply split_fds_Fnil_eq_l in H; subst; eauto.
    + inv Hg; try congruence.
      eexists. split; try constructor; eauto.
    + inv Hg. 
      * eexists. split. econstructor.
        econstructor 1. eauto. econstructor 1. eauto.
        econstructor 2. eauto.
        constructor. eapply split_fds_Fcons_r; eauto.
        eapply split_fds_Fcons_r; eauto. congruence.
      * eexists. split. econstructor; eauto. constructor.
        do 2 (eapply split_fds_Fcons_r; eauto). congruence.
      * inv H.
  - constructor. congruence.
  - eauto. inv H.  inv H0. eauto. exfalso.
    eapply exp_fun_cnt_refl_trans_clo_invariant in Hrwstar; eauto.
    eapply exp_fun_cnt_refl_trans_clo_invariant in H1; eauto.
    simpl in *. omega.
Qed.

Lemma hoist_star_Ecase_cons_2 x c e tes tes' B :
  hoist_star (Ecase x tes) (Efun B (Ecase x tes')) ->
  hoist_star (Ecase x ((c, e) :: tes)) (Efun B (Ecase x ((c, e) :: tes'))).
Proof.
  intros [n Hstar]. exists n. 
  apply (refl_trans_closure_f_compat (compat_closure hoist_rw) n
                                     (Ecase x tes) (Efun B (Ecase x tes'))
                                     (f c e)); eauto.
  intros e1 e2; eapply (compat_closure_f_compat hoist_rw e1 e2 (f c e)); eauto.
  - intros e1' e2' Hrw; eauto. inv Hrw; simpl; try now econstructor; eauto.
    eapply Ecase_hoist with (tes := (c, e) :: tes0).
  - intros c'. 
    induction c'; simpl;
    try (now destruct IHc' as [[c1 Heq] | [c1 Heq]]; [left | right];
           match goal with
             | [|- exists c, forall e, ?Ctx (?g (?c' |[ _ ]|))  = _ ]  =>
               let c := (exp_to_ctx (Ctx (c' |[ e1 ]|)) c1)
               in exists c 
           end; simpl; intros e3; rewrite Heq; eauto).
    + left. exists Hole_c; eauto.
    + right. exists (Ecase_c v ((c, e) :: l) t c' l0); eauto.
    + right. exists (Efun2_c f0 (f c e e0)); eauto.
Qed.

Lemma hoist_star_compat e e' c :
  hoist_star e e' ->
  hoist_star (c |[ e ]|) (c |[ e' ]|).
Proof.
  intros [n H]. exists n. induction H.
  - econstructor; eauto. now apply compat_closure_compat.
  - constructor.
Qed.


Lemma hoist_star_trans e1 e2 e3:
  hoist_star e1 e2 ->
  hoist_star e2 e3 ->
  hoist_star e1 e3.
Proof.
  intros [n H1] [m H2].
  assert (H := refl_trans_closure_n_trans
                 (compat_closure hoist_rw) n m e1 e2 e3 H1 H2).
  eexists; eauto.
Qed.

Lemma Erase_fundefs_Fnil_in_hoist_rw :
  (forall e e', Erase_fundefs e e' Fnil ->
                hoist_star e e') /\
  (forall defs e,
     Erase_nested_fundefs defs Fnil ->
     hoist_star (Efun defs e) e).
Proof.
  exp_defs_induction IHe IHl IHdefs; intros e' H; inv H.
  - eapply hoist_star_compat with (c := Econstr_c v t t0 l Hole_c); eauto.
  - exists 0; econstructor; eauto.
  - apply split_fds_Fnil in H8. inv H8.
    specialize (IHl (Ecase v tes') H6). inv IHl; eauto.
    eapply hoist_star_trans.
    eapply hoist_star_compat with (c := Ecase_c v [] c Hole_c l); eauto.
    eapply hoist_star_Ecase_cons_1; try (now eexists; eauto).
  - eapply hoist_star_compat with (c := Eproj_c v t n v0 Hole_c); eauto.
  - apply split_fds_Fnil in H6. inv H6.
    eapply hoist_star_trans.
    eapply hoist_star_compat with (c := Efun1_c f2 Hole_c); eauto.
    apply IHdefs; eauto.
  - exists 0; constructor; eauto.
  - eapply hoist_star_compat with (c := Eprim_c v t p l Hole_c); eauto.
  - inv H8.
  - exists 1. econstructor.
    apply Compat with (c := Hole_c). constructor.
    constructor.
Qed.

Lemma hoist_rw_hoist_star e1 e2 :
  hoist_rw e1 e2 ->
  hoist_star e1 e2.
Proof.
  intros H1. eapply hoist_star_trans; eauto.
  exists 1. econstructor; eauto.
  apply Compat with (c := Hole_c); eauto.
  constructor. exists 0; constructor.
Qed.

Lemma Fnil_eq_dec B :
  B = Fnil \/ B <> Fnil.
Proof.
  destruct B; eauto. right; congruence.
Qed.

Lemma Erase_fundefs_in_hoist_rw :
  (forall e e' B,
     B <> Fnil -> Erase_fundefs e e' B ->
     hoist_star e (Efun B e')) /\
  (forall B B' e,
     B' <> Fnil -> Erase_nested_fundefs B B' ->
     hoist_star (Efun B e) (Efun B' e)).
Proof.
  exp_defs_induction IHe IHl IHdefs;
  [| | | | | | | intros B' e1 Hnil H |intros B' e1 Hnil H ];
  try intros e1 B' Hnil H; inv H.
  - eapply hoist_star_trans.
    eapply hoist_star_compat with (c := Econstr_c v t t0 l Hole_c); eauto.
    apply hoist_rw_hoist_star. constructor.
  - congruence.
  - destruct (Fnil_eq_dec B) as [Heq1 | Heq1];
    destruct (Fnil_eq_dec B'0) as [Heq2 | Heq2]; subst.
    + inv H8. congruence.
    + apply split_fds_Fnil_eq_l in H8; subst.
      specialize (IHe _ _ Heq2 H7).
      apply Erase_fundefs_Fnil_in_hoist_rw in H6.
      eapply hoist_star_trans. 
      eapply hoist_star_compat with (c := Ecase_c v [] c Hole_c l). eauto.
      simpl. eapply hoist_star_trans.
      apply hoist_rw_hoist_star. apply Ecase_hoist with (tes := []).
      simpl. eapply hoist_star_compat with (c := Efun1_c B' Hole_c).
      eapply hoist_star_Ecase_cons_1; eauto.
    + apply split_fds_Fnil_eq_r in H8; subst.
      specialize (IHl _ _ Heq1 H6).
      apply Erase_fundefs_Fnil_in_hoist_rw in H7.
      eapply hoist_star_trans. 
      eapply hoist_star_compat with (c := Ecase_c v [] c Hole_c l); eauto. 
      simpl. eapply hoist_star_Ecase_cons_2; eauto.
    + specialize (IHe _ _ Heq2 H7). specialize (IHl _ _ Heq1 H6).
      simpl. eapply hoist_star_trans.
      eapply hoist_star_compat with (c := Ecase_c v [] c Hole_c l); eauto.
      eapply hoist_star_trans.
      eapply hoist_star_Ecase_cons_2; eauto.
      eapply hoist_star_trans.
      eapply hoist_star_compat with (c := Efun1_c B Hole_c).
      apply hoist_rw_hoist_star. apply Ecase_hoist with (tes := []).
      apply hoist_rw_hoist_star. constructor; eauto.
  - eapply hoist_star_trans.
    eapply hoist_star_compat with (c := Eproj_c v t n v0 Hole_c); eauto.
    apply hoist_rw_hoist_star. constructor.
  - destruct (Fnil_eq_dec Be) as [Heq1 | Heq1];
    destruct (Fnil_eq_dec Bdefs) as [Heq2 | Heq2]; subst.
    + inv H6. congruence.
    + apply split_fds_Fnil_eq_l in H6; subst.
      specialize (IHdefs _ e Heq2 H3).
      eapply hoist_star_trans; eauto.
      eapply hoist_star_compat with (c := Efun1_c B' Hole_c).
      apply Erase_fundefs_Fnil_in_hoist_rw; eauto.
    + apply split_fds_Fnil_eq_r in H6; subst.
      specialize (IHe _ _ Heq1 H2).
      eapply hoist_star_trans; eauto.
      apply Erase_fundefs_Fnil_in_hoist_rw; eauto.
    + specialize (IHe _ _ Heq1 H2). specialize (IHdefs _ e Heq2 H3).
      eapply hoist_star_trans; eauto.
      eapply hoist_star_trans.
      eapply hoist_star_compat with (c := Efun1_c Bdefs Hole_c); eauto.
      apply hoist_rw_hoist_star. constructor; eauto using split_fds_sym.
  - congruence.
  - eapply hoist_star_trans.
    eapply hoist_star_compat with (c := Eprim_c v t p l Hole_c); eauto.
    apply hoist_rw_hoist_star. constructor.
  - destruct (Fnil_eq_dec B'0) as [Heq1 | Heq1]; subst;
    destruct (Fnil_eq_dec B) as [Heq2 | Heq2]; subst.
    + eapply hoist_star_trans.
      eapply hoist_star_compat with (c := Efun2_c (Fcons1_c v t l Hole_c f5) e1); eauto.
      apply Erase_fundefs_Fnil_in_hoist_rw; eauto. simpl. inv H7. inv H1.
      inv H8. inv H7. exists 0; constructor.
    + specialize (IHe _ _ Heq2 H6).
      eapply hoist_star_trans.
      eapply hoist_star_compat with (c := Efun2_c (Fcons1_c v t l Hole_c f5) e1); eauto.
      inv H7. inv H1. simpl.
      apply hoist_rw_hoist_star.
      econstructor; try (now constructor 2; apply split_fds_nil_l); eauto.
    + apply split_fds_Fnil_eq_l in H8; subst.
      eapply Erase_fundefs_Fnil_in_hoist_rw in H6.
      specialize (IHdefs _ e1 Heq1 H7).
      eapply hoist_star_trans.
      eapply hoist_star_compat with (c := Efun2_c (Fcons1_c v t l Hole_c f5) e1); eauto.
      simpl. destruct B'0; try congruence. destruct f5; try (inv H7; congruence).
      apply hoist_star_Efun_cons; eauto. 
    + specialize (IHdefs _ e1 Heq1 H7). specialize (IHe _ _ Heq2 H6).
      eapply hoist_star_trans.
      eapply hoist_star_compat with (c := Efun2_c (Fcons1_c v t l Hole_c f5) e1); eauto.
      simpl. eapply hoist_star_trans with (e2 := Efun (Fcons v t l (Efun B e') B'0) e1).
      destruct B'0; try congruence. destruct f5; try (inv H7; congruence).
      apply hoist_star_Efun_cons; eauto. 
      apply hoist_rw_hoist_star.
      econstructor; try (now constructor 2; apply split_fds_nil_l); eauto.
  - exists 0; constructor.
Qed.

Corollary exp_hoist_in_hoist_star e e' :
  e' = exp_hoist e ->
  hoist_star e e'.
Proof.
  unfold exp_hoist. destruct (erase_fundefs e Fnil) eqn:Heq.
  destruct erase_fundefs_in_Erase_fundefs as [H1 _].
  destruct (H1 e Fnil id)
    as [e'' [B' [B'' [Heq1 [Heq2 Heq3]]]]]. rewrite Heq in Heq1; inv Heq1.
  apply split_fds_Fnil_eq_l in Heq2; subst.
  destruct B'; simpl; intros H; subst.
  - apply Erase_fundefs_in_hoist_rw; eauto. congruence.
  - apply Erase_fundefs_Fnil_in_hoist_rw; eauto.
Qed.

(* Is this the expected behavior?

Inductive one_or_many A : Type :=
| One : A -> one_or_many A
| Many : (one_or_many A * one_or_many A) -> one_or_many A.

Inductive dummy {A : Type} : one_or_many A -> Prop :=
| One_dummy :
    forall a, dummy (One A a) 
| Two_dummy :
    forall (p : one_or_many A * one_or_many A),
      (let '(c, e) := p in dummy e) ->
      dummy (Many A p).

*)


(* TODO : move the following lemmas to the right files *) 

Lemma preord_env_permut k x y v1 v2 rho1 rho2 P :
  x <> y ->
  preord_env_P k P (M.set x v1 (M.set y v2 rho1)) (M.set x v1 (M.set y v2 rho2)) ->
  preord_env_P k P (M.set x v1 (M.set y v2 rho1)) (M.set y v2 (M.set x v1 rho2)).
Proof.
  intros Hneq Hpre x' HP v1' Hget.
  rewrite M.gsspec in Hget.
  destruct (Coqlib.peq x' x). inv Hget. 
  - edestruct (Hpre x) as [v1'' [Hget'' Hpre'']]; eauto. rewrite M.gss; eauto.
    rewrite M.gss in Hget''; inv Hget''.
    eexists. rewrite M.gso; eauto. rewrite M.gss; eauto.
  - edestruct (Hpre x') as [v1'' [Hget'' Hpre'']]; eauto.
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
              

Lemma preord_env_permut_def_funs k x B v1 v2 rho1 rho2 :
  (forall x' : var, bound_var_fundefs x' B -> x <> x') ->
  closed_fundefs B ->
  preord_val k v1 v2 ->
  preord_env k rho1 rho1 ->
  preord_env k (def_funs B B (M.set x v1 rho1) (M.set x v1 rho1))
             (M.set x v1 (def_funs B B rho2 rho2)).
Proof.
  induction k using lt_wf_rec1.
Admitted.
(*   intros Hneq Hclo Hpre Hpreenv x' v1' Hget. *)
(*   apply def_funs_spec in Hget. *)
(*   destruct Hget as [[Hname Heq] | [Hname Heq ]]; subst. *)
(*   - assert (Hadm : bound_var_fundefs x' B) by admit. *)
(*     specialize (Hneq _ Hadm). eexists. *)
(*     rewrite M.gso; eauto. rewrite def_funs_eq; eauto. *)
(*     split; eauto.  *)
(*     rewrite preord_val_eq. *)
(*     intros vs1 vs2 j t xs e1 rho1' Hlen Hdef Heq. *)
(*     edestruct setlist_length as [rho2' Hset]; eauto. *)
(*     do 4 eexists. split; eauto. split; eauto. *)
(*     intros Hlt Hall. *)
(*     assert (Henv : preord_exp j (e1, rho1') (e1, M.set x v2 rho2')). *)
(*     apply preord_exp_refl. admit. *)
(*     eapply preord_exp_strengthen; eauto. *)
(*     intros ? ?; eauto. *)
(* Qed. *)



Lemma preord_env_def_funs_permut (k : nat) (f1 f2 : fundefs)
      (rho1 rho2 : env) :
  preord_env k rho1 rho2 ->
  (forall f, name_in_fundefs f f1 -> ~ name_in_fundefs f f2) ->
  preord_env k (def_funs f1 f1 rho1 (def_funs f2 f2 rho1 rho1))
             (def_funs f2 f2 rho2 (def_funs f1 f1 rho2 rho2)).
Proof.
  intros Henv Hname x _ v Hget.
  eapply def_funs_spec in Hget. destruct Hget as [[H1 H2] | [H1 H2]].
  - eexists. rewrite def_funs_neq; eauto. rewrite def_funs_eq; eauto.
    split; eauto. inv H2.
    rewrite preord_val_eq. intros vs1 vs2 j t1 xs1 e1 rho1'' Hlen Hdef Heq.
    edestruct (setlist_length (def_funs f1 f1 rho1 rho1)
                              (def_funs f1 f1 rho2 rho2)) as [rho2'' Hset]; eauto.
    do 4 eexists; repeat split; eauto. intros Hlt Hall.
    eapply preord_exp_refl.
    eapply preord_env_P_setlist_l. eapply preord_env_def_funs.
    eapply preord_env_monotonic; [| eauto]. omega.
    intros; simpl; eauto. eauto. eauto. eauto.
  - eapply def_funs_spec in H2.
    destruct H2 as [[H3 H4] | [H3 H4]]; subst.
    + eexists. rewrite def_funs_eq; eauto. split; eauto.
      rewrite preord_val_eq. intros vs1 vs2 j t1 xs1 e1 rho1' Hlen Hdef Heq.
      edestruct (setlist_length (def_funs f2 f2 rho1 rho1)
                                (def_funs f2 f2 rho2 rho2)) as [rho2' Hset]; eauto.
      do 4 eexists; repeat split; eauto. intros Hlt Hall.
      eapply preord_exp_refl.
      eapply preord_env_P_setlist_l. eapply preord_env_def_funs.
      eapply preord_env_monotonic; [| eauto]. omega.
      intros; simpl; eauto. eauto. eauto. eauto.
    + edestruct Henv as [v2 [Hget Hpre]]; eauto.
      eexists. rewrite def_funs_neq; eauto. rewrite def_funs_neq; eauto.
Qed.

Lemma hoist_rw_correct e e' rho rho' k :
  closed_fundefs_in_exp e ->
  unique_bindings e ->
  hoist_rw e e' ->
  preord_env k rho rho' ->
  preord_exp k (e, rho) (e', rho').
Proof.
  intros Hclo Hun Hrw Henv; inv Hrw; intros v1 c1 Hleq1 Hstep1.
Abort All.
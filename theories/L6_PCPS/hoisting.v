Require Import cps cps_util identifiers eval env ctx relations Ensembles_util.
Require Import Coq.Lists.List Coq.NArith.BinNat Coq.Relations.Relations Coq.omega.Omega Coq.Sets.Ensembles Coq.Classes.Morphisms.

Import ListNotations.

(** Given an expression [e], [exp_hoist e B f] will return an expression [e']
  * and a block of function definitions [B']. [e'] is the function definition 
  * erasure of [e] and [B] is exactly the function definitions of [e]. It's 
  * written in a CPS fashion and [f] is the continuation. [B] is an accumulator
  * of function definitions. 
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
  *  definition blocks and [B] is exactly the function definitions of [e] 
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

(** Correspondence between the inductive and the computational definitions
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


(** If [Erase_fundefs e e' B] then there are no function definitions 
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

(** The reflexivite transitive closure of the compatible 
  * closure of [hoist_rw] *)
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
Lemma exp_fun_count_Invariant n :
  Invariant hoist_rw (fun e => exp_fun_count e = n).
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
  Invariant (refl_trans_closure_n (compat_closure hoist_rw) m)
            (fun e => exp_fun_count e = n).
Proof.
  intros e1 e2 H1 Hstar.
  revert e1 e2 H1 Hstar. induction m; intros e1 e2 H1 Hstar.
  - inv Hstar. eauto. 
  - inv Hstar. inv H0. eapply IHm; [| eauto ].
    apply fun_count_ctx_compat.
    eapply exp_fun_count_Invariant; eauto.
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
  Invariant hoist_rw no_fun.
Proof.
  intros e1 e2 Hnf Hrw. inv Hnf; inv Hrw; try now inv H.
  - apply app_eq_nil in H1. inv H1. inv H0.
  - destruct tes0; simpl in *. inv H3.
    + inv H0.
    + inv H3. exfalso. eapply no_fun_Ecase_Efun; eauto.
Qed.

Lemma no_fun_SubtermInvariant :
  SubtermInvariant no_fun.
Proof.
  - intros c. induction c; simpl; intros e1 Hnf; eauto; try inv Hnf; eauto.
    + symmetry in H1. apply app_eq_nil in H1. inv H1. inv H0.
    + revert c0 e tes l0 H1 H2 H0. induction l; intros c0 e tes l0 H1 H2 H0.
      * inv H0; eauto.
      * simpl in H0; inv H0. inv H1.
        symmetry in H3. apply app_eq_nil in H3. inv H3. inv H0.
        eapply IHl; eauto.
Qed.

Lemma no_fun_SubtermSubstInvariant :
  SubtermSubstInvariant (fun _ e => no_fun e) no_fun.
Proof.
  intros c. induction c; simpl; intros e1 e2 Hnf1 Hnf2; inv Hnf1; eauto.
  - symmetry in H1. apply app_eq_nil in H1. inv H1. inv H0.
  - revert c0 e tes l0 H1 H2 H0. induction l; intros c0 e tes l0 H1 H2 H0.
    + simpl in *. inv H0. constructor; eauto.
    + inv H1.
      inv H0. symmetry in H3. apply app_eq_nil in H3. inv H3. inv H0.
      inv H0. simpl. constructor; eauto. 
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


(* This lemma should not be used. Instead we should find a way to use 
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

Lemma hoist_star_Efun_cons
      f tau xs e' f1 tau1 xs1 e1' f2 tau2 xs2 e2' B1 B2 e :
  hoist_star (Efun (Fcons f1 tau1 xs1 e1' B1) e)
             (Efun (Fcons f2 tau2 xs2 e2' B2) e) ->
  hoist_star (Efun (Fcons f tau xs e' (Fcons f1 tau1 xs1 e1' B1)) e)
             (Efun (Fcons f tau xs e' (Fcons f2 tau2 xs2 e2' B2)) e).
Proof.
  intros [n Hrwstar]. exists n.
  edestruct
    (refl_trans_closure_commut (compat_closure hoist_rw) n (g f tau xs e')
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
Lemma unique_bindings_SubtermInvariant' :
  SubtermInvariant unique_bindings /\
  (forall f e, unique_bindings_fundefs (f <[ e ]>) -> unique_bindings e).
Proof.
  exp_fundefs_ctx_induction IHe IHf;
  try (now intros e' H; simpl; eauto; inv H; eauto).
  simpl. intros l' e' H. 
  induction l; inv H; eauto.
Qed.

Corollary unique_bindings_SubtermInvariant :
  SubtermInvariant unique_bindings.
Proof.
  eapply unique_bindings_SubtermInvariant'.
Qed.

Lemma unique_bindings_Invariant :
  Invariant hoist_rw (fun e => unique_bindings e).
Proof.
  intros e1 e2 Hun Hrw; inv Hrw; simpl.
  - inv Hun. inv H5. constructor; eauto. constructor; eauto.
    rewrite bound_var_Econstr.  eapply Disjoint_Union; eauto.
    eapply Disjoint_sym. eapply Disjoint_Singleton. intros HB; eauto.
  - inv Hun. exfalso. eapply app_cons_not_nil; eauto.
    destruct tes.
    + inv H0. simpl. inv H2. rewrite bound_var_Efun in H3.
      constructor; eauto. constructor; eauto.
      eapply Disjoint_Union_r; eauto.
      rewrite bound_var_Ecase_cons. eapply Disjoint_Union; eauto.
      eapply Disjoint_sym. eapply Disjoint_Union_l; eauto.
    + inv H0.
      edestruct unique_bindings_Ecase_l as [H1' [H2' [H3' [H4' [H5' H6']]]]]; eauto.
      inv H1'. constructor; eauto. 
      * rewrite !bound_var_Ecase_append, !bound_var_Ecase_cons, !bound_var_Efun in *.
        eapply unique_bindings_Ecase_r; [ assumption | | assumption | | | ].
        constructor. assumption. assumption.
        eapply Disjoint_sym. eapply Disjoint_Union_l.
        eapply Disjoint_sym. eassumption.
        rewrite !bound_var_Ecase_cons. eapply Disjoint_Union.
        eapply Disjoint_Included_r ; [| eassumption ].
        rewrite <- Union_assoc.
        do 2 eapply Included_Union_mon_r. now apply Included_Union_l.
        apply Disjoint_sym. eapply Disjoint_Union_r.
        eapply Disjoint_sym. eassumption.
        apply Disjoint_sym. eapply Disjoint_Union_r.
        eapply Disjoint_sym. eassumption.
        rewrite !bound_var_Ecase_cons. eapply Disjoint_Union.
        eapply Disjoint_Included_r; [| eassumption ].
        do 2 eapply Included_Union_mon_r. now apply Included_refl.
        assumption.
      * rewrite !bound_var_Ecase_append, !bound_var_Ecase_cons, !bound_var_Efun in *.
        eapply Disjoint_Union. eapply Disjoint_Union.
        eapply Disjoint_Included_r; [| now apply H3 ].
        eapply Included_Union_mon_r. eapply Included_Union_mon_l.
        now apply Included_Union_l.
        eapply Disjoint_sym. eapply Disjoint_Union_l.
        eapply Disjoint_sym. eassumption.
        eapply Disjoint_Union. eassumption.
        eapply Disjoint_sym. eapply Disjoint_Union_l.
        eapply Disjoint_sym. eassumption.
  - inv Hun. inv H5. constructor; eauto. constructor; eauto.
    rewrite bound_var_Eproj.  eapply Disjoint_Union; eauto.
    eapply Disjoint_sym. eapply Disjoint_Singleton. intros HB; eauto.
  - inv Hun. inv H2. rewrite bound_var_Efun in H4. constructor; eauto.
    eapply (split_fds_unique_bindings_fundefs_r B B' B''); eauto.
    eapply Disjoint_sym. eapply Disjoint_Union_l; eauto.
    rewrite split_fds_bound_vars; eauto.
    eapply Disjoint_sym. eapply Disjoint_sym in H7.
    eapply Disjoint_Union; eauto.
    eapply Disjoint_sym. eapply Disjoint_Union_r; eauto.
  - inv Hun. inv H5. constructor; eauto. constructor; eauto.
    rewrite bound_var_Eprim. eapply Disjoint_Union; eauto.
    eapply Disjoint_sym. eapply Disjoint_Singleton. intros HB; eauto.
  - inv Hun; eauto.
  - inv Hun. 
    edestruct split_fds_unique_bindings_fundefs_l as [H1' [H2' H3']];
      [| apply H |]; eauto. inv H2'. inv H16.
    rewrite bound_var_Efun in *. rewrite bound_var_fundefs_Fcons in *.
    constructor; eauto.
    + eapply (split_fds_unique_bindings_fundefs_r B3 B4); eauto.
      eapply (split_fds_unique_bindings_fundefs_r B1 (Fcons f0 tau xs e' Fnil)); eauto.
      constructor; eauto. eapply Disjoint_Union_r; eauto.
      eapply Disjoint_Union_r; eauto. rewrite bound_var_fundefs_Fcons.
      eapply Disjoint_Included_r; [| now apply H3' ].
      do 2 (eapply Included_Union_compat; eauto using Included_refl).
      rewrite bound_var_Efun, <- Union_assoc.
      now eapply Included_Union_r.
      rewrite (split_fds_bound_vars B1 (Fcons f0 tau xs e' Fnil) B4); eauto.
      eapply Disjoint_sym. eapply Disjoint_Union.
      eapply Disjoint_Included_r; [| now apply H3' ].
      do 2 eapply Included_Union_mon_r. rewrite bound_var_Efun.
      rewrite <- Union_assoc. eapply Included_Union_l.
      rewrite bound_var_fundefs_Fcons. eapply Disjoint_Union; eauto.
      eapply Disjoint_sym. eapply Disjoint_Singleton; eauto.
      eapply Disjoint_Union; eauto.
      eapply Disjoint_sym. now eapply Disjoint_Union_l; eauto.
      now rewrite bound_var_fundefs_Fnil, Union_Empty_set_l; eauto.
    + rewrite (split_fds_bound_vars B3 B4 B); eauto.
      rewrite (split_fds_bound_vars B1 (Fcons f0 tau xs (Efun B3 e') Fnil) B2)
        in *; eauto.
      rewrite (split_fds_bound_vars B1 (Fcons f0 tau xs e' Fnil) B4); eauto.
      rewrite bound_var_fundefs_Fcons in H6.
      eapply Disjoint_sym. eapply Disjoint_Union.
      eapply Disjoint_sym; eapply Disjoint_Included_r; [| now apply H6 ].
      do 3 eapply Included_Union_mon_r. rewrite bound_var_Efun.
      rewrite <- Union_assoc. eapply Included_Union_l.
      rewrite bound_var_fundefs_Fcons. eapply Disjoint_sym.
      eapply Disjoint_Included_r; [| now apply H6 ].
      do 3 (eapply Included_Union_compat; eauto using Included_refl).
      rewrite bound_var_Efun. rewrite <- Union_assoc. now eapply Included_Union_r.
Qed.

Lemma closed_fundefs_in_exp_SubtermInvariant' :
  SubtermInvariant closed_fundefs_in_exp /\
  (forall f e, closed_fundefs_in_fundefs (f <[ e ]>) ->
               closed_fundefs_in_exp e).
Proof.
  exp_fundefs_ctx_induction IHc IHf; eauto;
  try (now intros e2 H; eapply IHc; intros B H'; eapply H; simpl; constructor).
  - intros l' e' H.
    eapply IHc; intros B H'; eapply H.
    simpl. econstructor; [ eassumption |].
    eapply in_or_app. right. left. reflexivity.
  - intros e2 H.  eapply IHf. 
    intros B H'. eapply H.
    simpl. now eapply In_Fun3.
  - intros e' H. simpl in H.
    eapply IHf. intros B H'. eapply H.
    now constructor 2.
Qed.
  
Lemma closed_fundefs_in_exp_SubtermInvariant :
  SubtermInvariant closed_fundefs_in_exp.
Proof.
  apply closed_fundefs_in_exp_SubtermInvariant'.
Qed.

Lemma split_fds_closed_fundefs_strong B1 B2 B3 :
  split_fds B1 B2 B3 ->
  Included var (occurs_free_fundefs B1) (name_in_fundefs B2) ->
  Included var (occurs_free_fundefs B2) (name_in_fundefs B1) ->
  closed_fundefs B3.
Proof.
  intros Hs HI1 HI2. unfold closed_fundefs.
  rewrite occurs_free_fundefs_big_cup in *.
  rewrite Same_Set_big_cup_l; [| eapply split_fds_fun_in_fundefs; eassumption ].
  rewrite Setminus_big_cup in *. rewrite Setminus_big_cup in HI1, HI2.
  rewrite Union_big_cup.
  rewrite split_fds_name_in_fundefs; [| eassumption ].
  rewrite Setminus_Union_distr.
  rewrite (Union_sym (name_in_fundefs B1) (name_in_fundefs B2)) at 2.
  rewrite <- !Setminus_Union.
  split; [| intros x Hc; now inv Hc ].
  eapply Included_trans.
  eapply Included_Union_compat.
  eapply Included_Setminus_compat. eassumption. now eapply Included_refl.
  eapply Included_Setminus_compat. eassumption. now eapply Included_refl.
  rewrite !Setminus_Empty_set, Union_Empty_set_l. now eapply Included_refl.
Qed.

Lemma closed_fundefs_in_exp_Invariant :
  Invariant hoist_rw closed_fundefs_in_exp.
Proof.
  intros e1 e2 Hun Hrw; inv Hrw; simpl;
  try now intros B' H'; inv H'; [ eapply Hun; eauto | inv H1; eapply Hun; eauto | eapply Hun; eauto ].
  - intros B' H'. inv H'.
    + eapply Hun.
      econstructor; [| apply in_or_app; right; left; reflexivity].
      constructor.
    + inv H1. eapply Hun. eapply in_app_or in H4. inv H4.
      econstructor; [ eassumption |]. now eapply in_or_app; eauto.
      inv H. inv H0.
      econstructor; [ | eapply in_or_app; right; left; reflexivity ].
      now constructor.
      econstructor; [ eassumption |].
      eapply in_or_app; right; right. eassumption.     
    + eapply Hun.
      econstructor; [ | eapply in_or_app; right; left; reflexivity ].
      now constructor.
  - intros B1 H'.
    inv H'. 
    eapply (split_fds_closed_fundefs B B' B''); [eassumption | | ]; now eauto.
    now eauto. eapply funs_in_fundef_split_fds in H2; [| eassumption ].
    inv H2; now eauto.
  - intros B1 H'. eapply Hun. eauto.
  - intros B' H'.
    assert (HB2 : closed_fundefs_in_fundefs B2).
    { intros x' H''. eapply Hun. now constructor. }
    inv H'; [| now eauto |].
    + eapply split_fds_closed_fundefs_strong; [ eassumption | |].
      * eapply Included_trans with (s2 := Empty_set _); [| intros x Hc; now inv Hc].
        eapply Hun. eapply In_Fun3. eapply split_fds_funs_in_fundef_r.
        eassumption. now eauto.
      * eapply same_split_fds_closed_fundefs with (B3' := Fcons f0 tau xs (Efun B3 e') B1) in H.
        unfold closed_fundefs in H. rewrite occurs_free_fundefs_Fcons in H.
        assert (H2 := Union_Same_set_Empty_set_l _ _  H).
        assert (H3 := Union_Same_set_Empty_set_r _ _  H).
        rewrite split_fds_occurs_free_fundefs; [| eassumption ].
        rewrite occurs_free_fundefs_Fcons in *.
        simpl in *. rewrite !Union_Empty_set_l, H3, !Union_Empty_set_r.
        rewrite occurs_free_fundefs_Fnil in *.
        rewrite (Setminus_Included_Empty_set (Empty_set var)), Union_Empty_set_l;
          [| intros c Hc; now inv Hc ]. rewrite Setminus_Union.
        eapply Included_Setminus_l; [| now eapply occurs_free_Efun_Included ].
        rewrite Setminus_Union_distr, <- Union_assoc at 1.
        rewrite H2, Union_Empty_set_r. eapply Subset_Setminus.
        constructor. now apply split_fds_nil_l.
        eapply Hun. now constructor.
    + eapply funs_in_fundef_split_fds in H4; [| eassumption ].
      inv H4.
      * eapply HB2. eapply split_fds_funs_in_fundef_r. eassumption.
        now eauto.
      * eapply funs_in_fundef_split_fds in H2; [| eassumption].
        inv H2.
        eapply HB2. eapply split_fds_funs_in_fundef_l. eassumption. eassumption.
        inv H3. eapply HB2.
        eapply split_fds_funs_in_fundef_r. eassumption. now eauto.
        inv H5.
Qed.


Lemma disjoint_ident_SubtermInvariant' :
  SubtermInvariant (fun e => Disjoint _ (bound_var e) (occurs_free e) /\
                             unique_bindings e) /\
  (forall B e, Disjoint _ (bound_var_fundefs (B <[ e ]>)) (occurs_free_fundefs (B <[ e ]>))
               /\ unique_bindings_fundefs (B <[ e ]>) ->
               Disjoint _ (bound_var e) (occurs_free e) /\ unique_bindings e).
Proof.
  exp_fundefs_ctx_induction IHc IHf; eauto;
  try (intros e' [H1 H2];
       assert (H3 : unique_bindings e')
         by (eapply unique_bindings_SubtermInvariant; eauto);
      split; [| assumption ]); simpl in *.
  - inv H2. apply IHc. split; [| assumption ].
    rewrite bound_var_Econstr, occurs_free_Econstr in *.
    eapply Disjoint_Included;
      [ now apply occurs_free_Econstr_Included with (tau := t) (t := t0)
      | now apply Included_refl |].
    rewrite occurs_free_Econstr.
    eapply Disjoint_sym. eapply Disjoint_Union; eapply Disjoint_sym.
    eapply Disjoint_Union_l. eassumption.
    eapply Disjoint_Singleton; eauto.
  - inv H2. apply IHc; split; [| assumption ].
    rewrite bound_var_Eproj, occurs_free_Eproj in *.
    eapply Disjoint_Included;
      [ now apply occurs_free_Eproj_Included with (tau := t) (t := n)
      | now apply Included_refl |]. 
    rewrite occurs_free_Eproj.
    eapply Disjoint_sym. eapply Disjoint_Union; eapply Disjoint_sym.
    eapply Disjoint_Union_l. eassumption.
    eapply Disjoint_Singleton; eauto.
  - inv H2. apply IHc; split; [| assumption ].
    rewrite bound_var_Eprim, occurs_free_Eprim in *.
    eapply Disjoint_Included;
      [ now apply occurs_free_Eprim_Included with (tau := t) (f := p)
      | now apply Included_refl |]. 
    rewrite occurs_free_Eprim.
    eapply Disjoint_sym. eapply Disjoint_Union; eapply Disjoint_sym.
    eapply Disjoint_Union_l. eassumption.
    eapply Disjoint_Singleton; eauto.
  - intros l' e' [H1 H2].
    assert (H3 : unique_bindings e') 
      by (eapply unique_bindings_SubtermInvariant
          with (c := Ecase_c v l t e l'); eauto).
    split; [| assumption ].
    rewrite occurs_free_Ecase_app, bound_var_Ecase_append,
    bound_var_Ecase_cons in *. 
    edestruct unique_bindings_Ecase_l as [H1' [H2' [H3' [H4' [H5' H6']]]]].
    eassumption. 
    eapply IHc; split; [| eassumption ].
    eapply Disjoint_Included; [| | now eapply H1 ].
    now eapply Included_Union_l.
    eapply Included_Union_mon_r. now eapply Included_Union_l.
  - inv H2. eapply IHc; split; [| eassumption ].
    rewrite bound_var_Efun, occurs_free_Efun in *.
    eapply Disjoint_Included; [| now apply Included_refl |].
    now apply occurs_free_Efun_Included. 
    rewrite occurs_free_Efun.
    eapply Disjoint_sym. eapply Disjoint_Union; eapply Disjoint_sym.
    eapply Disjoint_Union_l. rewrite Union_sym. eassumption.
    eapply Disjoint_Included; [| now apply Included_refl | eassumption].
    eapply name_in_fundefs_bound_var_fundefs.
  - inv H2. eapply IHf. split; [| eassumption ].
    rewrite bound_var_Efun, occurs_free_Efun in *.
    eapply Disjoint_Included; [| | now apply H1 ];
    now eapply Included_Union_l.
  - intros e' [H1 H2].
    assert (H3 : unique_bindings e')
      by (eapply unique_bindings_SubtermInvariant'
          with (f := Fcons1_c v t l e f6); eauto).
    split; [| eassumption ].
    inv H2. eapply IHc; split; [| eassumption ].
    rewrite bound_var_fundefs_Fcons, occurs_free_fundefs_Fcons in *.
    eapply Disjoint_Included; [| now apply Included_refl |].
    eapply occurs_free_in_fun with (B := Fcons v t l (e |[ e' ]|) f6).
    left. now constructor. simpl.
    rewrite occurs_free_fundefs_Fcons.
    eapply Disjoint_sym. eapply Disjoint_Union.
    eapply Disjoint_sym. assumption.
    eapply Disjoint_Union.
    eapply Disjoint_Union. eapply Disjoint_sym.
    eapply Disjoint_Singleton. assumption.
    eapply Disjoint_sym.
    eapply Disjoint_Included; [| eapply Included_refl| eassumption ].
    now eapply name_in_fundefs_bound_var_fundefs.
    eapply Disjoint_Included; [ | eapply Included_refl | eapply Disjoint_sym; eassumption ].
    do 2 eapply Included_Union_mon_r. now apply Included_Union_l.
  - intros e' [H1 H2].
    assert (H3 : unique_bindings e')
      by (eapply unique_bindings_SubtermInvariant'
          with (f := Fcons2_c v t l e f7); eauto).
    split; [| eassumption ].
    inv H2. eapply IHf; split; [| eassumption ].
    rewrite bound_var_fundefs_Fcons, occurs_free_fundefs_Fcons in *. 
    eapply Disjoint_Included; [| now apply Included_refl |].
    eapply (occurs_free_fundefs_Fcons_Included v t l e (f7 <[ e' ]>)).
    rewrite occurs_free_fundefs_Fcons.
    eapply Disjoint_sym. eapply Disjoint_Union.
    eapply Disjoint_sym. eapply Disjoint_Included; [| | now apply H1 ].
    eapply Included_Union_compat; now eapply Included_refl.
    do 3 eapply Included_Union_mon_r. now apply Included_refl.
   eapply Disjoint_sym. now eapply Disjoint_Singleton.
Qed.

Corollary disjoint_ident_SubtermInvariant :
  SubtermInvariant (fun e => Disjoint _ (bound_var e) (occurs_free e) /\
                             unique_bindings e).
Proof.
  apply disjoint_ident_SubtermInvariant'.
Qed.

Lemma disjoint_ident_Invariant :
  Invariant hoist_rw (fun e => Disjoint _ (bound_var e) (occurs_free e) /\
                               closed_fundefs_in_exp e /\
                               unique_bindings e).
Proof.
  intros e1 e2 [HD [Hclo Hun]] Hrw.
  assert (Hun' : unique_bindings e2)
    by (eapply unique_bindings_Invariant; eauto).
  assert (Hclo'' : closed_fundefs_in_exp e2)
    by (eapply closed_fundefs_in_exp_Invariant; eauto).
  split; [| split; eassumption ].
  inv Hrw; simpl; clear Hun Hun'.
  - rewrite !bound_var_Econstr, !occurs_free_Econstr, !bound_var_Efun, !occurs_free_Efun,
    !bound_var_Econstr, !occurs_free_Econstr in *.
    assert (Hclo' : closed_fundefs B) by (eapply Hclo; eauto).
    unfold closed_fundefs in Hclo'. rewrite Hclo', !Union_Empty_set_r in *.
    rewrite Union_assoc.
    eapply Disjoint_Included; [| now apply Included_refl | now apply HD].
    rewrite Setminus_Union_distr.
    apply Included_Union_compat.
    + apply Subset_Setminus.
    + rewrite !Setminus_Union, Union_sym. apply Included_refl.
  - rewrite !bound_var_Ecase_append, !occurs_free_Ecase_app, !bound_var_Efun, !occurs_free_Efun,
    !bound_var_Ecase_append, !occurs_free_Ecase_app, !bound_var_Ecase_cons,
    !bound_var_Efun in *.
    assert (Hclo' : closed_fundefs B) by (eapply Hclo''; eauto).
    unfold closed_fundefs in Hclo'. rewrite Hclo', !Union_Empty_set_r in *.
    rewrite Union_assoc. rewrite (Union_sym (bound_var_fundefs B) (bound_var (Ecase x tes))).
    rewrite <- Union_assoc in HD. rewrite <- !Union_assoc. 
    eapply Disjoint_Included; [| eapply Included_refl | now apply HD].
    rewrite Setminus_Union_distr.
    eapply Included_Union_compat. now apply Included_refl.
    now apply Subset_Setminus.
  - rewrite !bound_var_Eproj, !occurs_free_Eproj, !bound_var_Efun, !occurs_free_Efun,
    !bound_var_Eproj, !occurs_free_Eproj in *.
    assert (Hclo' : closed_fundefs B) by (eapply Hclo; eauto).
    unfold closed_fundefs in Hclo'. rewrite Hclo', !Union_Empty_set_r in *.
    rewrite Union_assoc.
    eapply Disjoint_Included; [| now apply Included_refl | now apply HD].
    rewrite Setminus_Union_distr.
    apply Included_Union_compat.
    + apply Subset_Setminus.
    + rewrite !Setminus_Union, Union_sym. apply Included_refl.
  - rewrite !bound_var_Efun, !occurs_free_Efun in *.
    rewrite split_fds_bound_vars; [| eassumption ].
    rewrite split_fds_name_in_fundefs; [| eassumption ].
    rewrite split_fds_occurs_free_fundefs; [| eassumption ].
    assert (Hclo1 : closed_fundefs B') by (eapply Hclo; eauto).
    assert (Hclo2 : closed_fundefs B) by (eapply Hclo; eauto).
    unfold closed_fundefs in Hclo1, Hclo2.
    rewrite Hclo1, Hclo2.
    rewrite !(Setminus_Included_Empty_set (Empty_set _));
      try (now intros x Hc; inv Hc).
    rewrite !Union_Empty_set_r, <- Union_assoc.
    eapply Disjoint_Included; [| now apply Included_refl  | now apply HD].
    rewrite Setminus_Union_distr.
    do 2 eapply Included_Union_mon_r.
    rewrite Setminus_Union, Union_sym. now apply Included_refl.
  - rewrite !bound_var_Eprim, !occurs_free_Eprim, !bound_var_Efun, !occurs_free_Efun,
    !bound_var_Eprim, !occurs_free_Eprim in *.
    assert (Hclo' : closed_fundefs B) by (eapply Hclo; eauto).
    unfold closed_fundefs in Hclo'. rewrite Hclo', !Union_Empty_set_r in *.
    rewrite Union_assoc.
    eapply Disjoint_Included; [| now apply Included_refl | now apply HD].
    rewrite Setminus_Union_distr.
    apply Included_Union_compat.
    + apply Subset_Setminus.
    + rewrite !Setminus_Union, Union_sym. apply Included_refl.
  - rewrite !bound_var_Efun, !occurs_free_Efun, !bound_var_fundefs_Fnil,
    !occurs_free_fundefs_Fnil, !Union_Empty_set_r in *. simpl in *.
    rewrite Setminus_Empty_set_Same_set in HD. assumption.
  - rewrite !bound_var_Efun, !occurs_free_Efun in *.
    assert (Hclo2 : closed_fundefs B) by (eapply Hclo''; eauto).
    unfold closed_fundefs in Hclo2. rewrite Hclo2, !Union_Empty_set_r in *.
    clear Hclo2.
    rewrite split_fds_bound_vars in *; try eassumption. 
    rewrite (split_fds_bound_vars B1 (Fcons f0 tau xs e' Fnil) B4) in *; try eassumption.
    rewrite split_fds_occurs_free_fundefs in *; try eassumption.
    rewrite split_fds_name_in_fundefs with (B3 := B)  in *; try eassumption.
    rewrite split_fds_name_in_fundefs with (B3 := B2)  in *; try eassumption.
    rewrite split_fds_name_in_fundefs with (B3 := B4) at 1; try eassumption.
    rewrite !bound_var_fundefs_Fcons, !occurs_free_fundefs_Fcons in *.
    simpl in *.
    rewrite !bound_var_fundefs_Fnil, !occurs_free_fundefs_Fnil in *.
    rewrite !(Setminus_Included_Empty_set (Empty_set _)) in HD ;
      try (now intros x Hc; inv Hc).
    (* rewrite !(Setminus_Included_Empty_set (Empty_set _)) ; *)
    (*   try (now intros x Hc; inv Hc). *)
    rewrite !bound_var_Efun, !occurs_free_Efun in *.
    rewrite !Union_Empty_set_l.
    repeat rewrite !Union_Empty_set_l in HD at 1.
    eapply Disjoint_Included; [|  | now apply HD].
    + eapply Included_Union_mon_r. 
      eapply Included_Setminus_compat.
      now apply Included_refl.
      now apply Included_Union_r.
    + rewrite Union_assoc, (Union_sym (bound_var_fundefs B3)).
      rewrite <- (Union_assoc (bound_var_fundefs B1)).
      eapply Included_Union_compat; [| now apply Included_refl ].
      eapply Included_Union_compat; [ now apply Included_refl |].
      rewrite !Union_assoc.
      eapply Included_Union_compat; [| now apply Included_refl ].
      rewrite (Union_sym _ (bound_var_fundefs B3)), <- Union_assoc.
      apply Included_refl.
Qed.


Lemma bound_var_Invariant S :
  Invariant hoist_rw (fun e => Same_set _ (bound_var e) S).
Proof.
  intros e1 e2 HS Hrw; inv Hrw.
  - rewrite !bound_var_Efun, !bound_var_Econstr, !bound_var_Efun in *.
    rewrite <- HS. apply Union_assoc.
  - rewrite !bound_var_Efun, !bound_var_Ecase_append,
    !bound_var_Ecase_cons, !bound_var_Efun in *.
    rewrite <- HS. rewrite Union_assoc, (Union_sym (bound_var_fundefs B)), <- Union_assoc.
    rewrite !Union_assoc. apply Same_set_refl.
  - rewrite !bound_var_Efun, !bound_var_Eproj, !bound_var_Efun in *.
    rewrite <- HS. apply Union_assoc.
  - rewrite !bound_var_Efun in *. rewrite split_fds_bound_vars; [| eassumption ].
    rewrite <- HS. rewrite Union_assoc. apply Same_set_refl.
  - rewrite !bound_var_Efun, !bound_var_Eprim, !bound_var_Efun in *.
    rewrite <- HS. apply Union_assoc.
  - now rewrite bound_var_Efun, bound_var_fundefs_Fnil, Union_Empty_set_r in HS.
  - rewrite bound_var_Efun in *.
    rewrite split_fds_bound_vars; [| eassumption ].
    rewrite (split_fds_bound_vars B1 (Fcons f0 tau xs e' Fnil) B4); [| eassumption ].
    rewrite (split_fds_bound_vars B1 (Fcons f0 tau xs (Efun B3 e') Fnil) B2) in HS
    ; [| eassumption ].
    rewrite <- HS.
    rewrite !bound_var_fundefs_Fcons, !bound_var_Efun.
    do 2 rewrite bound_var_fundefs_Fnil at 1.
    rewrite !Union_Empty_set_l.
    eapply Same_set_Union_compat; [| apply Same_set_refl ].
    rewrite Union_assoc, (Union_sym (bound_var_fundefs B3) (bound_var_fundefs B1)),
    <- Union_assoc.
    eapply Same_set_Union_compat; [ apply Same_set_refl |].
    rewrite Union_assoc, (Union_sym (bound_var_fundefs B3) (Singleton var f0)),
    <- Union_assoc.
    eapply Same_set_Union_compat; [ apply Same_set_refl |].
    rewrite Union_assoc, (Union_sym (bound_var_fundefs B3) (FromList xs)),
    <- Union_assoc. apply Same_set_refl.
Qed.

Lemma occurs_free_disjoint_ident_Invariant S :
  Invariant hoist_rw (fun e => Same_set _(occurs_free e) S /\
                               Disjoint _ (bound_var e) (occurs_free e)  /\
                               closed_fundefs_in_exp e /\
                               unique_bindings e).
Proof.
  intros e1 e2 [HS [HD [Hcl Hun]]] Hrw.
  assert ( H : Disjoint var (bound_var e2) (occurs_free e2) /\
               closed_fundefs_in_exp e2 /\ unique_bindings e2)
    by (eapply disjoint_ident_Invariant; eauto).
  split; [| eassumption ]. destruct H as [HD' [Hcl' _]].
  unfold closed_fundefs_in_exp, closed_fundefs in *.
  rewrite <- HS; clear HS. inv Hrw.
  - inv Hun.
    rewrite !occurs_free_Econstr, !occurs_free_Efun, !occurs_free_Econstr,
    !bound_var_Econstr, !bound_var_Efun in *.
    rewrite !Setminus_Union_distr.
    rewrite (Union_assoc (FromList _) _), (Union_sym (FromList _)), <- Union_assoc.
    apply Same_set_Union_compat; [| apply Same_set_Union_compat ].
    + apply Same_set_sym. apply Setminus_Disjoint. rewrite Hcl.
      now apply Disjoint_Empty_set_l. now constructor.
    + apply Setminus_Disjoint. eapply Disjoint_sym.
      eapply Disjoint_Included; [| | now apply HD ].
      now apply Included_Union_l.
      rewrite <- Union_assoc. apply Included_Union_mon_l.
      now apply name_in_fundefs_bound_var_fundefs.
    + rewrite !Setminus_Union. rewrite Union_sym.
      now apply Same_set_refl.
  - rewrite !bound_var_Ecase_append, !bound_var_Ecase_cons, !bound_var_Efun,
    !occurs_free_Ecase_app, !occurs_free_Efun, !occurs_free_Ecase_app in *.
    rewrite  <- !Union_assoc .
    apply Same_set_Union_compat; [ now apply Same_set_refl |].
    rewrite !Setminus_Union_distr.
    apply Same_set_Union_compat; [ now apply Same_set_refl |].
    apply Same_set_Union_compat; [| apply Same_set_Union_compat ].
    + apply Setminus_Disjoint. eapply Disjoint_sym.
      eapply Disjoint_Included; [| | now apply HD ].
      apply Included_Union_mon_r; now apply Included_Union_l.
      apply Included_Union_mon_r. rewrite <- Union_assoc.
      apply Included_Union_mon_l. now apply name_in_fundefs_bound_var_fundefs.
    + apply Setminus_Disjoint. eapply Disjoint_sym.
      eapply Disjoint_Included; [| | now apply HD ].
      do 2 apply Included_Union_mon_r; now apply Included_Union_l.
      apply Included_Union_mon_r. rewrite <- Union_assoc.
      apply Included_Union_mon_l. now apply name_in_fundefs_bound_var_fundefs.
    + apply Setminus_Disjoint. eapply Disjoint_sym.
      eapply Disjoint_Included; [| | now apply HD ].
      do 3 apply Included_Union_mon_r; now apply Included_refl.
      apply Included_Union_mon_r. rewrite <- Union_assoc.
      apply Included_Union_mon_l. now apply name_in_fundefs_bound_var_fundefs.
  - rewrite !occurs_free_Eproj, !occurs_free_Efun, !occurs_free_Eproj,
    !bound_var_Eproj, !bound_var_Efun in *.
    rewrite !Setminus_Union_distr.
    rewrite (Union_assoc (Singleton _ _) _), (Union_sym (Singleton _ _)), <- Union_assoc.
    apply Same_set_Union_compat; [| apply Same_set_Union_compat ].
    + apply Same_set_sym. apply Setminus_Disjoint. rewrite Hcl.
      now apply Disjoint_Empty_set_l. now constructor.
    + apply Setminus_Disjoint. eapply Disjoint_sym.
      eapply Disjoint_Included; [| | now apply HD ].
      now apply Included_Union_l.
      rewrite <- Union_assoc. apply Included_Union_mon_l.
      now apply name_in_fundefs_bound_var_fundefs.
    + rewrite !Setminus_Union. rewrite Union_sym.
      now apply Same_set_refl.
  - rewrite !bound_var_Efun, !occurs_free_Efun in *.
    rewrite split_fds_occurs_free_fundefs; [| eassumption ].
    rewrite (split_fds_name_in_fundefs B B' B''); [| eassumption ].
    rewrite !Setminus_Union_distr, <- Union_assoc, Setminus_Union,
    (Union_sym (name_in_fundefs B)).
    apply Same_set_Union_compat; try now apply Same_set_Union_compat.
    apply Setminus_Disjoint. eapply Disjoint_sym.
    eapply Disjoint_Included; [| | now apply HD ].
    now apply Included_Union_l.
    apply Included_Union_mon_r. apply Included_Union_mon_l.
    now apply name_in_fundefs_bound_var_fundefs.
  - rewrite !occurs_free_Eprim, !occurs_free_Efun, !occurs_free_Eprim,
    !bound_var_Eprim, !bound_var_Efun in *.
    rewrite !Setminus_Union_distr.
    rewrite (Union_assoc (FromList _) _), (Union_sym (FromList _)), <- Union_assoc.
    apply Same_set_Union_compat; [| apply Same_set_Union_compat ].
    + apply Same_set_sym. apply Setminus_Disjoint. rewrite Hcl.
      now apply Disjoint_Empty_set_l. now constructor.
    + apply Setminus_Disjoint. eapply Disjoint_sym.
      eapply Disjoint_Included; [| | now apply HD ].
      now apply Included_Union_l.
      rewrite <- Union_assoc. apply Included_Union_mon_l.
      now apply name_in_fundefs_bound_var_fundefs.
    + rewrite !Setminus_Union. rewrite Union_sym.
      now apply Same_set_refl.
  - rewrite !occurs_free_Efun, !occurs_free_fundefs_Fnil, !Union_Empty_set_r.
    simpl. rewrite Setminus_Empty_set_Same_set.  apply Same_set_refl.
  - rewrite !bound_var_Efun, !occurs_free_Efun in *.
    rewrite Hcl'; [| now constructor ]. rewrite Hcl; [| now constructor ].
    rewrite !Union_Empty_set_r.  
    rewrite split_fds_name_in_fundefs with (B3 := B)  in *; try eassumption.
    rewrite split_fds_name_in_fundefs with (B3 := B2); try eassumption.
    rewrite split_fds_name_in_fundefs with (B3 := B4) in *; try eassumption.
    simpl in *. do 2 rewrite Union_Empty_set_l at 1. 
    rewrite <- Setminus_Union.
    eapply Same_set_Setminus_compat; [| now apply Same_set_refl ].
    apply Setminus_Disjoint. eapply Disjoint_sym.
    eapply Disjoint_Included;
      [ now eapply occurs_free_Efun_Included with (B := B2)
      |  now apply Included_refl |].
    apply Disjoint_sym. eapply Disjoint_Union.
    + apply Disjoint_sym. eapply Disjoint_Included; [| | now apply HD ].
      * apply occurs_free_Efun.
      * apply Included_Union_mon_l.
        rewrite split_fds_bound_vars with (B3 := B2); try eassumption.
        rewrite bound_var_fundefs_Fcons, bound_var_Efun.
        do 3 apply Included_Union_mon_r.
        do 2 apply Included_Union_mon_l.
        now apply name_in_fundefs_bound_var_fundefs.
    + inv Hun.
      eapply split_fds_unique_bindings_fundefs_l in H5;
        [| eassumption ].
      edestruct H5 as [_ [H1' H2']].
      inv H1'. 
      rewrite split_fds_name_in_fundefs with (B3 := B2); try eassumption.
      simpl. rewrite Union_Empty_set_l. eapply Disjoint_Union.
      eapply Disjoint_Included; [| | now apply H2' ].
      rewrite bound_var_fundefs_Fcons, bound_var_Efun.
      do 2 apply Included_Union_mon_r. do 2 apply Included_Union_mon_l.
      now apply name_in_fundefs_bound_var_fundefs.
      now apply name_in_fundefs_bound_var_fundefs.
      eapply Disjoint_sym. eapply Disjoint_Singleton.
      intros Hc. apply H10. constructor.
      now apply name_in_fundefs_bound_var_fundefs; eauto.
Qed.

 
Lemma closed_fundefs_in_exp_subterm_subst :
  (forall c e e', closed_fundefs_in_exp (c |[ e ]|) ->
                  Same_set _ (occurs_free e) (occurs_free e') ->
                  closed_fundefs_in_exp e' ->
                  closed_fundefs_in_exp (c |[ e' ]|)) /\
  (forall B e e', closed_fundefs_in_fundefs (B <[ e ]>) ->
                  Same_set _ (occurs_free e) (occurs_free e') ->
                  closed_fundefs_in_exp e' ->
                  closed_fundefs_in_fundefs (B <[ e' ]>)).
Proof.
  exp_fundefs_ctx_induction IHc IHf; eauto; simpl. 
  - intros e1 e2 H1 H2 H3.
    intros B HIn. inv HIn.
    eapply IHc ; [ | eassumption | eassumption | eassumption].
    intros B' Hin'. eapply H1. eauto.
  - intros e1 e2 H1 H2 H3.
    intros B HIn. inv HIn.
    eapply IHc ; [ | eassumption | eassumption | eassumption].
    intros B' Hin'. eapply H1. eauto.
  - intros e1 e2 H1 H2 H3.
    intros B HIn. inv HIn.
    eapply IHc ; [ | eassumption | eassumption | eassumption].
    intros B' Hin'. eapply H1. eauto.
  - intros l' e1 e2 H1 H2 H3.
    intros B HIn. inv HIn. eapply in_app_or in H6.
    inv H6.
    + eapply H1. econstructor. eassumption.
      eapply in_or_app. left; eauto.
    + inv H.
      * inv H0. 
        eapply IHc; [| | | eassumption]; [ | eassumption | eassumption ].
        intros B' HIn'. eapply H1.
        econstructor. eassumption.
        eapply in_or_app. right. left. reflexivity.
      * eapply H1. econstructor. eassumption.
        eapply in_or_app. right; right; eauto.
  - intros e1 e2 H1 H2 H3.
    intros B HIn. inv HIn.
    + eapply H1. eauto.
    + eapply IHc ; [ | eassumption | eassumption | eassumption].
      intros B' Hin'. eapply H1. eauto.
    + eapply H1. eauto.
  - intros e1 e2 H1 H2 H3.
    intros B HIn. inv HIn.
    + unfold closed_fundefs. rewrite occurs_free_fundefs_comp.
      eapply H1. now eauto.
      apply Same_set_sym. eassumption.
    + eapply H1. eauto.
    + eapply IHf; [ | eassumption | eassumption | eassumption].
      intros B' HB'. eapply H1. eauto.
  - intros e1 e2 H1 H2 H3.
    intros B HIn. inv HIn.
    + eapply IHc; [ | eassumption | eassumption | eassumption].
      intros B' HB'. eapply H1. eauto.
    + eapply H1. eauto.
  - intros e1 e2 H1 H2 H3.
    intros B HIn. inv HIn.
    + eapply H1. eauto.
    + eapply IHf; [ | eassumption | eassumption | eassumption].
      intros B' HB'. eapply H1. eauto.
Qed.
  
Lemma hoist_correct_pre_compat_closure_Invariant :
  Invariant (compat_closure hoist_rw)
            (fun e => closed_fundefs_in_exp e /\
                      unique_bindings e /\
                      Disjoint _ (bound_var e) (occurs_free e)).
Proof.
  eapply invariant_compat_closure
  with (R' := fun e e' => Same_set _ (bound_var e) (bound_var e') /\
                          Same_set _ (occurs_free e) (occurs_free e')).
  - intros e1 e2 [H1 [H2 H3]] Hrw.
    split; [| split]; try now eapply disjoint_ident_Invariant; eauto.
  - intros e1 e2 [H1 [H2 H3]].
    split; [| split ].
    + eapply closed_fundefs_in_exp_SubtermInvariant; eauto.
    + eapply unique_bindings_SubtermInvariant; eauto.
    + eapply disjoint_ident_SubtermInvariant; eauto .
  - intros c e1 e2 [Hcl [Hun HD]] [[HS1 HS2] [Hcl' [Hun' HD']]].
    split; [| split].
    + eapply closed_fundefs_in_exp_subterm_subst; eassumption.
    + eapply unique_bindings_ctx; eassumption.
    + rewrite occurs_free_comp.
      rewrite bound_var_comp. eassumption.
      apply Same_set_sym. eassumption.
      apply Same_set_sym. eassumption.
  - intros e1 e2 [Hrw [HI1 [HI2 HI3]]]. split.
    + eapply Same_set_sym. eapply bound_var_Invariant; eauto.
      eapply Same_set_refl.
    + eapply Same_set_sym. eapply occurs_free_disjoint_ident_Invariant; eauto.
      split. now eapply Same_set_refl.
      split. eassumption.
      split; now eauto.
Qed.

Lemma hoist_rw_correct e e' rho rho' k :
  closed_fundefs_in_exp e ->
  unique_bindings e ->
  (Disjoint var (bound_var e) (occurs_free e)) ->
  hoist_rw e e' ->
  preord_env_P (occurs_free e) k rho rho' ->
  preord_exp k (e, rho) (e', rho').
Proof.
  intros Hclo Hun HD Hrw Henv; inv Hrw; intros v1 c1 Hleq1 Hstep1.
  { inv Hstep1. inv H9; eauto.
    edestruct preord_env_P_getlist_l as [vs' [Hgetl Hpre]]; eauto.
    rewrite occurs_free_Econstr. now apply Included_Union_l.
    edestruct (preord_exp_refl k e0) as [v2 [c2 [Hstep2 Hpre2]]]; [| eauto | eauto |].
    eapply preord_env_P_antimon.
    eapply preord_env_set_def_funs_permut with (v2 := Vconstr tau t vs'); eauto.
    - inv Hun. intros Hb. eapply H1. constructor; eauto.
    - rewrite preord_val_eq. split; eauto.
    - eapply Included_trans. eapply occurs_free_Efun_Included with (B := B).
      rewrite Union_assoc. apply Included_Union_compat; eauto using Included_refl.
      eapply occurs_free_Econstr_Included.
    - repeat eexists; eauto. constructor. econstructor; eauto.
      eapply getlist_fundefs; eauto. 
      intros y Hin Hc. eapply HD.
      constructor. constructor 2. constructor.
      now apply name_in_fundefs_bound_var_fundefs; eauto.
      now constructor. }
  { inv Hstep1.
    edestruct Henv as [v' [Hget Hpre]]; eauto.
    rewrite preord_val_eq in Hpre.
    destruct v'; try (now simpl in Hpre; contradiction). inv Hpre.
    edestruct (@findtag_append_spec exp) as [H4 | [H4 H5]]; eauto.
    - edestruct (preord_exp_refl k e) as [v2 [c2 [Hstep2 Hpre2]]];
      [| eauto | eauto |].
      + eapply preord_env_P_def_funs_not_in_P_r with (B := B).
        * eapply preord_env_P_antimon; eauto.
          eapply occurs_free_Ecase_Included. eapply findtag_In_patterns; eauto.
        * eapply Disjoint_sym. eapply Disjoint_Included; eauto.
          eapply occurs_free_Ecase_Included. eapply findtag_In_patterns; eauto.
          eapply Included_trans. apply name_in_fundefs_bound_var_fundefs.
          intros x' H'. 
          econstructor; [| eapply in_or_app; right; constructor; eauto ].
          constructor; eauto.
      + repeat eexists; eauto. constructor; eauto. econstructor; eauto.
        rewrite def_funs_neq; eauto. intros Hn.
        eapply HD. econstructor.
        simpl. econstructor; [| eapply in_or_app; right; constructor; eauto ].
        constructor. now apply name_in_fundefs_bound_var_fundefs; eauto.
        constructor.
        erewrite findtag_append_Some; eauto.
    - simpl in H4. destruct (M.elt_eq t t2); subst.
      + inv H4. inv H6.
        edestruct (preord_exp_refl k e'0) as [v2 [c2 [Hstep2 Hpre2]]];
          [| eauto | eauto |]. 
        eapply preord_env_P_def_funs_col; eauto.
        eapply preord_env_P_antimon; eauto.
        eapply Included_trans; 
          [| eapply occurs_free_Ecase_Included; eapply findtag_In_patterns; eauto ].
        intros x' H'. inv H'. inv H. constructor; eauto.
        now eapply Free_Efun2.
        repeat eexists; eauto. constructor; eauto. econstructor; eauto.
        rewrite def_funs_neq; eauto. intros Hn.
        eapply HD. econstructor.
        simpl. econstructor; [| eapply in_or_app; right; constructor; eauto ].
        constructor. now apply name_in_fundefs_bound_var_fundefs; eauto.
        now constructor.
        erewrite findtag_append_not_In; eauto. simpl.
        destruct (M.elt_eq t2 t2); try congruence.
      + edestruct (preord_exp_refl k e) as [v2 [c2 [Hstep2 Hpre2]]];
        [| eauto | eauto |].
        * eapply preord_env_P_def_funs_not_in_P_r with (B := B).
          eapply preord_env_P_antimon; eauto.
          eapply occurs_free_Ecase_Included. eapply findtag_In_patterns; eauto.
          eapply Disjoint_sym. eapply Disjoint_Included; eauto.
          eapply occurs_free_Ecase_Included. eapply findtag_In_patterns; eauto.
          eapply Included_trans. apply name_in_fundefs_bound_var_fundefs.
          intros x' H'. 
          econstructor; [| eapply in_or_app; right; constructor; eauto ].
          constructor; eauto.
        * repeat eexists; eauto. constructor; eauto. econstructor; eauto.
          rewrite def_funs_neq; eauto. intros Hn.
          eapply HD. econstructor.
          simpl. econstructor; [| eapply in_or_app; right; constructor; eauto ].
          constructor. now apply name_in_fundefs_bound_var_fundefs; eauto.
          constructor.
          erewrite findtag_append_not_In; eauto. simpl.
          destruct (M.elt_eq t t2); try congruence. }
  { inv Hstep1. inv H9; eauto.
    edestruct Henv as [vs' [Hgetl Hpre]]; eauto. rewrite preord_val_eq in Hpre.
    destruct vs'; try (simpl in Hpre; contradiction). inv Hpre.
    edestruct (@Forall2_nthN val) as [v' [Hnth Hpre']] ; eauto. 
    edestruct (preord_exp_refl k e0) as [v2 [c2 [Hstep2 Hpre2]]];
      [| eauto | eauto |].
    eapply preord_env_P_antimon.
    eapply preord_env_set_def_funs_permut; eauto.
    - inv Hun. intros Hb. eapply H2. constructor; eauto.
    - eapply Included_trans. eapply occurs_free_Efun_Included with (B := B).
      rewrite Union_assoc. apply Included_Union_compat; eauto using Included_refl.
      eapply occurs_free_Eproj_Included.
    - repeat eexists; eauto. constructor. econstructor; eauto.
      eapply get_fundefs; eauto. 
      intros Hc. eapply HD.
      constructor; [| constructor; now constructor ].
      constructor. constructor.
      now apply name_in_fundefs_bound_var_fundefs. }
  { inv Hstep1. inv H5; eauto.
    edestruct (preord_exp_refl k e0) as [v2 [c2 [Hstep2 Hpre2]]]; [| eauto | eauto |].
    eapply preord_env_P_antimon. 
    - eapply preord_env_P_def_funs_merge with (B := B''); eauto using split_fds_sym.
      inv Hun. inv H2.
      eapply split_fds_unique_bindings_fundefs_r with (B1 := B); eauto.
      constructor. intros x HI. inv HI. eapply H4. split; now eauto.
    - eapply Included_trans. eapply occurs_free_Efun_Included with (B := B').
      rewrite (split_fds_name_in_fundefs B B' B''), Union_assoc; eauto.
      eapply Included_Union_compat; eauto using Included_refl.
      eapply Included_trans. eapply occurs_free_Efun_Included with (B := B).
      apply Included_refl.
    - repeat eexists; eauto. constructor. eauto. }
  { inv Hstep1. inv H11; eauto.
    edestruct preord_env_P_getlist_l as [vs' [Hgetl Hpre]]; eauto.
    rewrite occurs_free_Eprim. now apply Included_Union_l.
    edestruct Prim_axiom as [v' [Heq Hpre']]; eauto.
    edestruct (preord_exp_refl k e0) as [v2 [c2 [Hstep2 Hpre2]]];
      [| eauto | eauto |].
    eapply preord_env_P_antimon.
    eapply preord_env_set_def_funs_permut; eauto.
    - inv Hun. intros Hb. eapply H1. constructor; eauto.
    - eapply Included_trans. eapply occurs_free_Efun_Included with (B := B).
      rewrite Union_assoc. apply Included_Union_compat; eauto using Included_refl.
      eapply occurs_free_Eprim_Included.
    - repeat eexists; eauto. constructor. econstructor; eauto.
      eapply getlist_fundefs; eauto. 
      intros y Hin Hc. eapply HD.
      constructor; [| now constructor; eauto ].
      constructor. constructor.
      now apply name_in_fundefs_bound_var_fundefs. }
  { inv Hstep1. simpl in H4.
    edestruct (preord_exp_refl k e') as [v2 [c2 [Hstep2 Hpre2]]];
      [| eauto | eauto |].
    eapply preord_env_P_antimon; eauto.
    eapply Included_trans. eapply occurs_free_Efun_Included with (B := Fnil).
    simpl. rewrite Union_Empty_set_l. apply Included_refl.
    repeat eexists; eauto. }
  { inv Hun. inv Hstep1. 
    edestruct preord_exp_refl with (e := e0) as [v2 [c2 [Hstep2 Hpre2]]]; eauto;
    [| exists v2, c2; repeat split; try constructor; eauto ].
    specialize (unique_bindings_hoist _ _ _ _ _ _ _ _ _ H H0 H1 H5); intros Hun.
    eapply preord_env_P_trans with (rho2 := def_funs B2 B2 rho' rho').
    + eapply preord_env_P_def_funs_col.
      rewrite occurs_free_Efun in Henv. unfold closed_fundefs_in_exp, closed_fundefs in Hclo.
      now rewrite Union_sym.
    + clear Henv. intros m.
      eapply preord_env_P_trans.
      * eapply preord_env_P_Same_set_fun_in_fundefs
        with (B2 := Fcons f0 tau xs (Efun B3 e'0) B1)
               (B2' := Fcons f0 tau xs (Efun B3 e'0) B1); eauto;
        solve
          [ rewrite split_fds_fun_in_fundefs; eauto;
            simpl; rewrite Union_Empty_set_l, Union_sym; apply Same_set_refl
          | eapply unique_bindings_split_fds_fundfes_append
            with (B1 := (Fcons f0 tau xs (Efun B3 e'0) Fnil));
            eauto using split_fds_sym ].
      * intros m'. eapply preord_env_P_trans.
        { eapply preord_env_P_antimon.
          eapply preord_env_P_def_funs_hoist; eauto.
          specialize (Hclo B2 (In_Fun1 _ _)). 
          eapply same_split_fds_closed_fundefs; [ | | eauto]; eauto.
          constructor. now apply split_fds_nil_l.
          eapply Hclo. apply In_Fun3. now eapply split_fds_funs_in_fundef_r; eauto.
          now eapply unique_bindings_split_fds_fundfes_append
          with (B1 := Fcons f0 tau xs (Efun B3 e'0) Fnil); eauto using split_fds_sym.
          apply Disjoint_sym.
          eapply Disjoint_Included; [ apply Included_refl | | apply HD ].
          eapply Included_trans. now apply name_in_fundefs_bound_var_fundefs.
          rewrite bound_var_Efun,
          (split_fds_bound_vars B1 (Fcons f0 tau xs (Efun B3 e'0) Fnil) B2),
          bound_var_fundefs_Fcons, bound_var_Efun, <- !Union_assoc; eauto.
          do 3 apply Included_Union_mon_r.
          apply Included_Union_mon_l. now apply Included_refl.
        edestruct split_fds_unique_bindings_fundefs_l as [H1' [H2' H3']];
          [| apply H1 |]; eauto.
        rewrite (split_fds_bound_vars B1 (Fcons f0 tau xs e'0 Fnil) B4) in H3' ; eauto.
        rewrite bound_var_fundefs_Fcons in H3'.
        apply Disjoint_sym. eapply Disjoint_Included; [ | | apply H3' ]; eauto.
        simpl. rewrite Union_sym.
        apply Included_Union_compat; eauto using Included_Union_l;
        now apply name_in_fundefs_bound_var_fundefs.
        now apply name_in_fundefs_bound_var_fundefs.
        eapply preord_env_P_refl.
        eapply Included_trans. apply occurs_free_Efun_Included.
        eapply Included_Union_compat. apply Included_refl.
        rewrite split_fds_name_in_fundefs; eauto. simpl. rewrite Union_Empty_set_l.
        eapply Included_Union_compat; apply Included_refl. }
        { intros m''.  
          eapply preord_env_P_Same_set_fun_in_fundefs;
            eauto using unique_bindings_split_fds_Fcons_fundefs_append;
            now (eapply split_fds_fundefs_append_fun_in_fundefs
                 with (B2 := Fcons f0 tau xs e'0 Fnil); eauto). } }
Qed.


Lemma hoist_star_preserves_fv e e' :
  closed_fundefs_in_exp e ->
  unique_bindings e ->
  (Disjoint var (bound_var e) (occurs_free e)) ->
  hoist_star e e' ->
  Same_set _ (occurs_free e) (occurs_free e').
Proof.
  intros Hclo Hun HD [n Hrw].
  eapply (relation_inclusion_refl_trans_strong (compat_closure hoist_rw)) with
  (Pre := fun e => closed_fundefs_in_exp e /\
                   unique_bindings e /\
                   (Disjoint var (bound_var e) (occurs_free e)))
    (R' := fun e e' : exp =>
             Same_set var (occurs_free e) (occurs_free e')); eauto.
  - intros e1 e2 Hpre HR.
    eapply (relation_inclusion_compat_strong hoist_rw) with
    (Pre := fun e => closed_fundefs_in_exp e /\
                     unique_bindings e /\
                     Disjoint var (bound_var e) (occurs_free e))
    (R' := fun e e' : exp =>
             Same_set var (occurs_free e) (occurs_free e')); eauto.
    + intros e1' e2' [H1 [H2 H4]] Hclo'. eapply Same_set_sym.
      eapply occurs_free_disjoint_ident_Invariant; [| eassumption ].
      split. now apply Same_set_refl.
      eauto.
    + intros e1' e2' [H1 [H2 H3]]. split.
      eapply closed_fundefs_in_exp_SubtermInvariant; eauto.
      split; eapply disjoint_ident_SubtermInvariant; eauto.
    + intros e1' e2' c H. eapply occurs_free_comp. eauto.
  - intros e1' e2' [H1 [H2 H3]] Hrw'.
    eapply hoist_correct_pre_compat_closure_Invariant; eauto.
  - intros e1 H. eapply Same_set_refl.
  - intros e1 e2 e3 _ _ HS1 HS2. rewrite HS1. eassumption.
Qed. 

Lemma hoist_star_correct e e' rho rho' k :
  closed_fundefs_in_exp e ->
  unique_bindings e ->
  (Disjoint var (bound_var e) (occurs_free e)) ->
  hoist_star e e' ->
  preord_env_P (occurs_free e) k rho rho' ->
  preord_exp k (e, rho) (e', rho').
Proof.
  intros Hclo Hun HD [n Hrw].
  revert k rho rho'. 
  eapply (relation_inclusion_refl_trans_strong (compat_closure hoist_rw)) with
  (Pre := fun e => closed_fundefs_in_exp e /\
                   unique_bindings e /\
                   (Disjoint var (bound_var e) (occurs_free e)))
    (R' := fun e e' : exp =>
            forall k rho rho',
              preord_env_P (occurs_free e) k rho rho' ->
              preord_exp k (e, rho) (e', rho')); eauto.
  - intros e1 e2 Hpre HR.
    eapply (relation_inclusion_compat_strong hoist_rw) with
    (Pre := fun e => closed_fundefs_in_exp e /\
                     unique_bindings e /\
                     Disjoint var (bound_var e) (occurs_free e))
    (R' := fun e e' : exp =>
             forall k rho rho',
               preord_env_P (occurs_free e) k rho rho' ->
               preord_exp k (e, rho) (e', rho')); eauto.
    + intros e1' e2' [H1 [H2 H4]] Hclo' k rho rho' Hpre'.
      eapply hoist_rw_correct; eauto.
    + intros e1' e2' [H1 [H2 H3]]. split.
      eapply closed_fundefs_in_exp_SubtermInvariant; eauto.
      split; eapply disjoint_ident_SubtermInvariant; eauto.
    + intros e1' e2' c H rho1 rho2 Hpre'. eapply preord_exp_compat. eauto.
  - intros e1' e2' [H1 [H2 H3]] Hrw'. 
    eapply hoist_correct_pre_compat_closure_Invariant; eauto.
  - intros e1 e2 rho1 rho2 H. eapply preord_exp_refl; eauto.
  - intros e1 e2 e3 [H1 [H2 H3]] H4 Ht1 Ht2 k rho1 rho2 Hpre. eapply preord_exp_trans.
    eapply Ht1; eauto. intros m. eapply Ht2; eauto. eapply preord_env_P_refl.
Qed.

Corollary hoist_exp_correct e rho rho' k :
  closed_fundefs_in_exp e ->
  unique_bindings e ->
  (Disjoint var (bound_var e) (occurs_free e)) ->
  preord_env_P (occurs_free e) k rho rho' ->
  preord_exp k (e, rho) (exp_hoist e, rho').
Proof.
  intros.
  eapply hoist_star_correct; try eassumption.
  now eapply exp_hoist_in_hoist_star.
Qed.


(* Computational definition and declarative spec for function hoisting. Part of the CertiCoq project.
 * Author: Zoe Paraskevopoulou, 2016
 *)

Require Import Common.AstCommon Common.compM.
Require Import L6.cps L6.cps_util L6.identifiers L6.eval L6.env L6.ctx L6.size_cps
        L6.logical_relations L6.Ensembles_util L6.List_util L6.map_util L6.tactics
        L6.algebra L6.closure_conversion L6.closure_conversion_util L6.state.
Require Import compcert.lib.Coqlib.
Require Import Coq.Lists.List Coq.NArith.BinNat Coq.Relations.Relations
        Coq.omega.Omega Coq.Sets.Ensembles Coq.Classes.Morphisms.

Import ListNotations.

Close Scope Z_scope.

(** Given an expression [e], [exp_hoist e B f] will return an expression [e']
  * and a block of function definitions [B']. [e'] is the function definition 
  * erasure of [e] and [B] is exactly the function definitions of [e]. It's 
  * written in a CPS fashion and [f] is the continuation. [B] is an accumulator
  * of function definitions. 
  *)
Fixpoint erase_fundefs (e : exp) (defs : fundefs)
         (f : exp * fundefs * nat -> exp * fundefs * nat) {struct e} : exp * fundefs * nat :=
  match e with
    | Econstr x  tag ys e' =>
      erase_fundefs e' defs (fun p => let '(e, defs, n) := p in
                                      f (Econstr x tag ys e, defs, n))
    | Ecase x tes =>
      fold_left
        (fun (f : exp * fundefs * nat -> exp * fundefs * nat) (te : ctor_tag * exp) =>
           fun p =>
             let (c, e) := te in
             let '(e1, defs1, n1) := p in
             erase_fundefs e defs1
                       (fun p2 =>
                          let '(e2, defs2, n2) := p2 in
                          match e1 with
                          | Ecase x' tes' =>
                            f (Ecase x' ((c, e2) :: tes'), defs2, max n1 n2)
                          | _ => (* This should never match *)
                            f (Ecase x [(c, e2)], defs2, max n1 n2)
                          end)) tes f (Ecase x [], defs, 0)
    | Eproj x tag n y e' =>
      erase_fundefs e' defs (fun p =>
                               let '(e, defs, m) := p in
                               f (Eproj x tag n y e, defs, m))
    | Eletapp x g ft ys e' =>
      erase_fundefs e' defs (fun p =>
                               let '(e, defs, n) := p in
                               f (Eletapp x g ft ys e, defs, n))
                    
    | Efun fdefs e' =>
      erase_fundefs e' defs (fun p =>
                               let '(e'', defs'', n) := p in
                               erase_nested_fundefs fdefs e'' defs'' (fun p => let '(e, defs, m) := p in f (e, defs, 1 + max n m)))
    | Eapp g ft xs =>
      f (Eapp g ft xs, defs, 0)
    | Eprim x prim ys e' =>
      erase_fundefs e' defs (fun p =>
                               let '(e', defs', n) := p in
                               f (Eprim x prim ys e', defs', n))
    | Ehalt x => f (Ehalt x, defs, 0) 
  end
with erase_nested_fundefs (defs : fundefs) (e : exp) (hdefs : fundefs)
                          (f : exp * fundefs * nat -> exp * fundefs * nat) {struct defs}
     : exp * fundefs * nat :=
       match defs with 
         | Fcons g t xs e' defs =>
           erase_nested_fundefs defs e hdefs
                                (fun p1 =>
                                   let '(e1, defs1, n1) := p1 in
                                   erase_fundefs e' defs1
                                                 (fun p2 =>
                                                    let '(e2, defs2, n2) := p2 in
                                                    f (e1, Fcons g t xs e2 defs2, max n1 n2)))
         | Fnil => f (e, hdefs, 0)
  end.

(** [exp_hoist e] moves all function definitions of [e] at the outermost level *)
Definition exp_hoist (e : exp) :=
  let '(e, defs, n) := erase_fundefs e Fnil id in
  match defs with
  | Fnil => (e, n)
    | _ => (Efun defs e, n)
  end.


Section CC.
  Context (clo_tag : ctor_tag). (* Tag for closure records *)
  
  Definition closure_conversion_hoist (e : exp) (c: comp_data) : error exp * comp_data :=    
    let '(e'_err, c') := closure_conversion_top clo_tag e c in
    match e'_err with 
    | Ret e' => (Ret (fst (exp_hoist e')), c')
    | Err str => (Err str, c')
    end.

End CC.

(** [erase_fundefs e e' B] iff [e'] is [e] after erasing all the function 
  *  definition blocks and [B] is exactly the function definitions of [e] 
  *) 
Inductive Erase_fundefs : exp -> exp -> fundefs -> nat (* number of hoisting steps *) -> Prop :=
| Efun_erase :
    forall e e' defs Be Bdefs Be_defs n m,
      Erase_fundefs e e' Be n ->
      Erase_nested_fundefs defs Bdefs m ->
      split_fds Be Bdefs Be_defs ->
      Erase_fundefs (Efun defs e) e' Be_defs (1 + max n m)
| Econstr_erase :
    forall x t ys e e' B n,
      Erase_fundefs e e' B n ->
      Erase_fundefs (Econstr x t ys e)
                  (Econstr x  t ys e') B n
| Ecase_nil_erase :
    forall x,
      Erase_fundefs (Ecase x nil) (Ecase x nil) Fnil 0
| Ecase_cons_erase :
    forall x c e e' tes tes' B B' B'' n m,
      Erase_fundefs (Ecase x tes) (Ecase x tes') B n ->
      Erase_fundefs e e' B' m ->
      split_fds B B' B'' ->
      Erase_fundefs (Ecase x ((c, e) :: tes)) (Ecase x ((c, e') :: tes')) B'' (max n m)
| Eproj_erase :
    forall x tau N y e e' B n,
      Erase_fundefs e e' B n ->
      Erase_fundefs (Eproj x tau N y e)
                    (Eproj x tau N y e') B n
| Eletapp_erase :
    forall x f tau ys e e' B n,
      Erase_fundefs e e' B n ->
      Erase_fundefs (Eletapp x f tau ys e)
                    (Eletapp x f tau ys e') B n
| Eapp_erase :
    forall f ft xs,
      Erase_fundefs (Eapp f ft xs) (Eapp f ft xs) Fnil 0
| Eprim_erase n :
    forall x f ys e e' B,
      Erase_fundefs e e' B n ->
      Erase_fundefs (Eprim x f ys e)
                    (Eprim x f ys e') B n
| Ehalt_erase :
    forall x, Erase_fundefs (Ehalt x) (Ehalt x) Fnil 0
with Erase_nested_fundefs : fundefs -> fundefs -> nat -> Prop :=
| Fcons_erase :
    forall f tau xs e e' defs B B' B'' n m,
      Erase_fundefs e e' B n ->
      Erase_nested_fundefs defs B' m ->
      split_fds B (Fcons f tau xs e' B') B'' ->
      Erase_nested_fundefs (Fcons f tau xs e defs) B'' (max n m)
| Fnil_erase :
    Erase_nested_fundefs Fnil Fnil 0.

(** Correspondence between the inductive and the computational definitions of function definition erasure *)
Lemma erase_fundefs_in_Erase_fundefs :
  (forall e B f,
   exists e' B' B'' m,
     erase_fundefs e B f = f (e', B', m) /\
     split_fds B B'' B' /\
     Erase_fundefs e e' B'' m) /\
  (forall defs e B f,
    exists B' B'' m,
      erase_nested_fundefs defs e B f = f (e, B', m) /\
      split_fds B B'' B' /\
      Erase_nested_fundefs defs B'' m).
Proof. 
  exp_defs_induction IHe IHl IHf; intros; simpl in *;
  try (now edestruct IHe as [e' [B' [B'' [m [Heq [Hsplit Her]]]]]];
       repeat eexists; eauto; try rewrite Heq; try constructor; eauto).
  - repeat eexists; eauto using split_fds_nil_l; repeat econstructor.
  - edestruct IHl as [e1' [B1' [B1'' [m [Heq1 [Hspl1 Her1]]]]]]. 
    edestruct IHe as [e2' [B2' [B2'' [n [Heq2 [Hspl2 Her2]]]]]].
    rewrite Heq1, Heq2. clear Heq1 Heq2.
    edestruct split_fds_trans as [B3 [H1 H2]]; [apply Hspl1 | |]; eauto.
    inv Her1; repeat eexists; eauto; econstructor; eauto; econstructor; eauto.
  - edestruct IHe as [e2 [B2 [B2' [m [Heq2 [Hspl2 Her2]]]]]].
    edestruct IHf as [B1 [B1' [n [Heq1 [Hspl1 Her1]]]]]; subst.
    edestruct split_fds_trans as [B3 [H1 H2]] ; [ | apply Hspl1 |]; eauto.
    repeat eexists. rewrite Heq2, Heq1; eauto. eauto.    
    econstructor; eauto.
  - repeat eexists; eauto using split_fds_nil_l; repeat econstructor.
  - repeat eexists; eauto using split_fds_nil_l; econstructor.
  - edestruct IHf as [B1 [B1' [m [Heq1 [Hspl1 Her1]]]]]; subst.
    edestruct IHe as [e2 [B2 [B2' [n [Heq2 [Hspl2 Her2]]]]]].
    edestruct split_fds_trans as [B3 [H1 H2]] ; [ apply Hspl1 | |]; eauto.
    repeat eexists. rewrite Heq1, Heq2; eauto.
    constructor. eassumption. 
    rewrite Max.max_comm. econstructor; eauto. econstructor; eauto.
    apply split_fds_sym; eauto.
  - repeat eexists; eauto using split_fds_nil_l; repeat econstructor.
Qed.

  
(** Expressions without function definitions *)
Inductive no_fun : exp -> Prop  :=
| Econstr_no_fun :
    forall x t xs e,
      no_fun e ->
      no_fun (Econstr x t xs e)
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
| Eletapp_no_fun :
    forall x f tau ys e,
      no_fun e ->
      no_fun (Eletapp x f tau ys e)
| Eapp_no_fun :
    forall x ft ys, no_fun (Eapp x ft ys)
| Eprim_no_fun :
    forall x p xs e,
      no_fun e ->
      no_fun (Eprim x p xs e)
| Ehalt_no_fun :
    forall x, no_fun (Ehalt x).

(** Function definitions without nested function definitions *)
Inductive no_fun_defs : fundefs -> Prop  :=
| Fcons_no_fun :
    forall f tau xs e B,
      no_fun e ->
      no_fun_defs B ->
      no_fun_defs (Fcons f tau xs e B)
| Fnil_no_fun :
    no_fun_defs Fnil.

Hint Constructors no_fun no_fun_defs : core.

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
  (forall e e' B m,
     Erase_fundefs e e' B m ->
     no_fun e' /\ no_fun_defs B) /\
  (forall B B' m,
     Erase_nested_fundefs B B' m ->
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

Definition funs_inv_env B rho :=
  exists rho0,
  forall f,
    f \in name_in_fundefs B ->
    M.get f rho = Some (Vfun rho0 B f).


Lemma funs_inv_env_set B rho x v :
  funs_inv_env B rho ->
  ~ x \in name_in_fundefs B ->
          funs_inv_env B (M.set x v rho).
Proof.
  intros [rhoi Hin] Hnin. eexists. intros f Hfun.
  rewrite M.gso; eauto.
  intros Hc; subst; eauto.
Qed.


Lemma Erase_fundefs_bound_var_mut :
  (forall e e' B m (Herase : Erase_fundefs e e' B m),
      bound_var e <--> bound_var e' :|: bound_var_fundefs B) /\
  (forall B B' m (Herase : Erase_nested_fundefs B B' m),
      bound_var_fundefs B <--> bound_var_fundefs B').
Proof.
  exp_defs_induction IHe IHc IHB;
    try (intros e' B m Hr); try (intros B' m Hr); inv Hr;
      try (now repeat normalize_bound_var; rewrite IHe; [| eassumption ];
           split; xsets).
  - repeat normalize_bound_var. sets.
  - repeat normalize_bound_var.
    rewrite IHe; [| eassumption ].
    rewrite IHc; [| eassumption ].
    erewrite (split_fds_bound_vars B0 B' B); eauto.
    split; xsets.
  - normalize_bound_var.
    rewrite IHe; [| eassumption ].
    rewrite IHB; [| eassumption ].
    erewrite (split_fds_bound_vars Be Bdefs B); eauto.            
    sets.
  - repeat normalize_bound_var. sets.
  - repeat normalize_bound_var. sets.
  - erewrite (split_fds_bound_vars B (Fcons v t l e' B'0) B'); eauto.   
    repeat normalize_bound_var.
    rewrite IHe; [| eassumption ].
    rewrite IHB; [| eassumption ]. xsets.
  - normalize_bound_var. xsets.
Qed. 


Lemma Erase_fundefs_bound_var :
  forall e e' B m (Herase : Erase_fundefs e e' B m),
    bound_var e <--> bound_var e' :|: bound_var_fundefs B.
Proof.
  eapply Erase_fundefs_bound_var_mut.
Qed.

Lemma Erase_nested_fundefs_bound_var :
  forall B B' m (Herase : Erase_nested_fundefs B B' m),
    bound_var_fundefs B <--> bound_var_fundefs B'.
Proof.
  eapply Erase_fundefs_bound_var_mut.
Qed.

Ltac bound_var_heq Hname :=
  match goal with
  | [ H : Erase_fundefs _ _ _ _ |- _ ] =>
    assert (Hname := Erase_fundefs_bound_var _ _ _ _ H)
  end.

Ltac bound_var_fundefs_heq Hname :=
  match goal with
  | [ H : Erase_nested_fundefs _ _ _ |- _ ] =>
    assert (Hname := Erase_nested_fundefs_bound_var _ _ _ H)
  end.


Lemma Erase_fundefs_unique_bindings_mut :
  (forall e e' B m (Herase : Erase_fundefs e e' B m),
      unique_bindings e ->
      unique_bindings e' /\
      unique_bindings_fundefs B /\
      Disjoint _ (bound_var_fundefs B) (bound_var e')) /\
  (forall B B' m (Herase : Erase_nested_fundefs B B' m),
      unique_bindings_fundefs B ->
      unique_bindings_fundefs B').
Proof.
  exp_defs_induction IHe IHc IHB;
    try (intros e' B m Hr Hun); try (intros B' m Hr Hun); inv Hr;
      try (bound_var_heq Hbin); try (bound_var_fundefs_heq Hbin'). 
  - inv Hun. 
    edestruct (IHe _ _ _ H6) as [Hun [Hunf Hdis]]; eauto. 
    split; [| split ].
    + constructor; eauto.
      intros Hc. eapply H1. eapply Erase_fundefs_bound_var_mut.
      eassumption. now left.
    + eassumption.
    + normalize_bound_var.
      eapply Union_Disjoint_r.
      eassumption. eapply Disjoint_Singleton_r.
      intros Hc. eapply H1. eapply Hbin. now right.
  - repeat normalize_bound_var.
    split; [| split ].
    + sets.
    + constructor.
    + sets.
  - normalize_bound_var.
    inv Hun.
    edestruct (IHe _ _ _ H7) as [Hun' [Hunf' Hd']]; eauto. 
    edestruct (IHc _ _ _ H6) as [Hun [Hunf Hd]]; eauto.
    clear H7. bound_var_heq Hbin'.
    split; [| split ].
    + constructor; eauto.  
      eapply Disjoint_Included; [| | eapply H5 ].
      rewrite Hbin'. sets.
      rewrite Hbin. sets.
    + rewrite Hbin', Hbin in *.  
      eapply split_fds_unique_bindings_fundefs_r;
        [| | | eassumption ]; eauto.
      eapply Disjoint_sym.
      eapply Disjoint_Included; [| | eapply H5 ]; sets.
    + rewrite (split_fds_bound_vars B0 B' B); eauto.
      rewrite Hbin, Hbin' in *.
      eapply Union_Disjoint_l; eapply Union_Disjoint_r.
      * eapply Disjoint_sym.
        eapply Disjoint_Included; [| | eapply H5 ]; sets.
      * eassumption.
      * eassumption.
      * eapply Disjoint_Included; [| | eapply H5 ]; sets.
  - inv Hun. 
    edestruct (IHe _ _ _ H7) as [Hun [Hunf Hdis]]; eauto. 
    split; [| split ].
    + constructor; eauto.
      intros Hc. eapply H1. eapply Erase_fundefs_bound_var_mut.
      eassumption. now left.
    + eassumption.
    + normalize_bound_var.
      eapply Union_Disjoint_r.
      eassumption. eapply Disjoint_Singleton_r.
      intros Hc. eapply H1. eapply Hbin. now right.
  - inv Hun.
    edestruct (IHe _ _ _ H7) as [Hun [Hunf Hdis]]; eauto. 
    split; [| split ].
    + constructor; eauto.
      intros Hc. eapply H1. eapply Erase_fundefs_bound_var_mut.
      eassumption. now left.
    + eassumption.
    + normalize_bound_var.
      eapply Union_Disjoint_r.
      eassumption. eapply Disjoint_Singleton_r.
      intros Hc. eapply H1. eapply Hbin. now right.
  - inv Hun.
    edestruct (IHe _ _ _ H1) as [Hun [Hunf Hdis]]; eauto. 
    assert (Hunf' := IHB _ _ H2 H4).
    split; [| split ]; eauto.
    + eapply split_fds_unique_bindings_fundefs_r;
        [ | | | eassumption ]; eauto.
      eapply Disjoint_Included; [| | eapply H5 ]; sets.
      rewrite Hbin'. sets.
      rewrite Hbin. sets.
    + erewrite (split_fds_bound_vars _ _ B); eauto.
      eapply Union_Disjoint_l.
      * eassumption.
      * rewrite <- Hbin'.
        eapply Disjoint_sym.
        eapply Disjoint_Included; [| | eapply H5 ]; sets.
        rewrite Hbin; sets.
  - inv Hun.
    split; [| split ]; eauto.
    + constructor; eauto.
    + constructor.
    + normalize_bound_var. sets.
  - inv Hun. 
    edestruct (IHe _ _ _ H6) as [Hun [Hunf Hdis]]; eauto. 
    split; [| split ].
    + constructor; eauto.
      intros Hc. eapply H1. eapply Erase_fundefs_bound_var_mut.
      eassumption. now left.
    + eassumption.
    + normalize_bound_var.
      eapply Union_Disjoint_r.
      eassumption. eapply Disjoint_Singleton_r.
      intros Hc. eapply H1. eapply Hbin. now right.
  - inv Hun.
    split; [| split ].
    + constructor; eauto.
    + constructor.
    + normalize_bound_var; sets.
  - inv Hun.
    eapply split_fds_unique_bindings_fundefs_r;
      [ | | | eassumption ]; eauto.
    * eapply IHe. eassumption. eassumption.
    * constructor; eauto.
      intros Hc; eapply H4. 
      eapply Hbin. now left.
      intros Hc. eapply H5.
      eapply Hbin'. eassumption.
      eapply Disjoint_Included_l; [| eapply H9 ]; sets.
      rewrite Hbin. sets.
      eapply Disjoint_Included_l; [| eapply H10 ]; sets.
      rewrite Hbin'. sets.
      eapply Disjoint_Included; [| | eapply H11 ]; sets.
      rewrite Hbin'. sets.
      rewrite Hbin. sets.
      eapply IHe. eassumption. eassumption.
    * normalize_bound_var.
      repeat eapply Union_Disjoint_r.
      -- eapply Disjoint_Singleton_r.
         intros Hc; eapply H4. 
         eapply Hbin. now right.
      -- eapply Disjoint_Included_l; [| eapply H9 ]; sets.
         rewrite Hbin. sets.
      -- eapply IHe. eassumption. eassumption.
      -- rewrite <- Hbin'.
         eapply Disjoint_Included; [| | eapply H11 ]; sets.
         rewrite Hbin. sets.
  - constructor.
Qed.

Lemma Erase_nested_fundefs_name_in_fundefs :
  (forall B B' m (Herase : Erase_nested_fundefs B B' m),
      name_in_fundefs B \subset name_in_fundefs B').
Proof.
  intros B B' m Hr. induction Hr; sets.
  rewrite (split_fds_name_in_fundefs _ _ _ H0).
  simpl. sets.
Qed.


Lemma Erase_fundefs_funnames_in_exp : 
      (forall e e' B m (Herase : Erase_fundefs e e' B m),
          funnames_in_exp e \subset name_in_fundefs B) /\
      (forall B B' m (Herase : Erase_nested_fundefs B B' m),
          funnames_in_fundefs B \subset name_in_fundefs B').
Proof.
  exp_defs_induction IHe IHc IHB; intros; simpl; inv Herase;
    try now (intros z Hin; inv Hin; destructAll; inv H; eapply IHe; eauto;
             econstructor; split; eauto).
  - intros x Hin; inv Hin; destructAll. inv H. inv H5.
  - eapply IHc in H6. intros z Hin; inv Hin; destructAll. inv H. inv H5.
    + inv H. eapply IHe in H7. erewrite split_fds_name_in_fundefs; [| eassumption ].
      right; eauto. eapply H7. econstructor. split; eauto.
    + erewrite split_fds_name_in_fundefs; [| eassumption ]. left.
      eapply H6. econstructor. split; [| eassumption ].
      econstructor. eassumption. eassumption.
  - intros z Hin; inv Hin; destructAll. erewrite split_fds_name_in_fundefs; [| eassumption ]. inv H.
    + right. eapply Erase_nested_fundefs_name_in_fundefs. eassumption. eassumption.
    + left. eapply IHe. eassumption. econstructor. split; eauto.
    + right. eapply IHB. eassumption. econstructor. split; eauto.
  - intros z Hin; inv Hin; destructAll. erewrite split_fds_name_in_fundefs; [| eassumption ]. inv H.
    + left. eapply IHe. eassumption. econstructor. split; eauto.
    + right. simpl. right. eapply IHB. eassumption. econstructor. split; eauto.
Qed.


Lemma Erase_fundefs_fun_fv_in e e' B m
      (Herase : Erase_fundefs e e' B m)
      (Hsub : fun_fv_in e (funnames_in_exp e)) :  
      fun_fv_in e (name_in_fundefs B).
Proof.
  intros B' Hin. eapply Hsub in Hin. eapply Included_trans.
  eassumption. eapply Erase_fundefs_funnames_in_exp. eassumption.
Qed.


Lemma Erase_fundefs_occurs_free :
  (forall e e' Ball B Bprev m
          (Herase : Erase_fundefs e e' B m)
          (Hsplit: split_fds Bprev B Ball)
          (Hfv : fun_fv_in e (name_in_fundefs Ball)),
      occurs_free e' \subset (name_in_fundefs Ball) :|: occurs_free e).
Proof.
  induction e using exp_ind'; intros; inv Herase;
  try (now repeat normalize_occurs_free;
       eapply Union_Included; [ now sets | ];
       eapply Included_trans;
       [ eapply Included_Setminus_compat; [ eapply IHe; eauto; intros B1 Hin1; eapply Hfv; eauto | reflexivity ]
       | rewrite Setminus_Union_distr; sets ]).    
  - rewrite !occurs_free_Ecase_nil at 1. sets.
  - rewrite !occurs_free_Ecase_cons at 1.    
    
    eapply Union_Included. now sets.
    eapply Union_Included.    
    + edestruct split_fds_trans. eapply split_fds_sym.
      eapply H8. eapply split_fds_sym. eassumption. destructAll.     
      eapply IHe in H7. 3:{ intros B1 Hin1. eapply Hfv; eauto. econstructor. eassumption. now left. }
      eapply Included_trans. eassumption. now sets.
      eapply split_fds_sym. eassumption.
    + edestruct split_fds_trans. eapply H8. eapply split_fds_sym. eassumption. destructAll.     
      eapply IHe0 in H6.
      eapply Included_trans. eassumption. now sets.
      eapply split_fds_sym. eassumption.
      intros B1 Hin1. eapply Hfv; eauto. inv Hin1. econstructor. eassumption. right. eauto. 
  - edestruct split_fds_trans. eapply H6. eapply split_fds_sym. eassumption. destructAll. 
    eapply IHe in H1. 2:{ eapply split_fds_sym. eassumption. }
    2:{ intros B1 Hin1. eapply Hfv; eauto. }

    repeat normalize_occurs_free. rewrite Union_assoc.
    rewrite Union_Setminus_Included.
    eapply Included_trans. eassumption. now sets. tci. 
    eapply Included_trans. eapply Erase_nested_fundefs_name_in_fundefs. eassumption.

    rewrite split_fds_name_in_fundefs with (B3 := Ball); eauto.
    rewrite split_fds_name_in_fundefs with (B3 := x); eauto. now sets.
  - sets.
  - sets.
Qed.

Lemma Erase_fundefs_occurs_free_fundefs :
  (forall e e' Ball B Bprev m
          (Herase : Erase_fundefs e e' B m)
          (Hsplit: split_fds Bprev B Ball)
          (Hfv : fun_fv_in e (name_in_fundefs Ball)),
      occurs_free_fundefs B \subset name_in_fundefs Ball) /\
  (forall B B' Ball Bprev m
          (Herase : Erase_nested_fundefs B B' m)
          (Hsplit: split_fds Bprev B' Ball)
          (Hfv : fun_fv_in_fundefs B (name_in_fundefs Ball)),
      occurs_free_fundefs B' \subset name_in_fundefs Ball).
Proof.
  exp_defs_induction IHe IHl IHB; intros; inv Herase;
  try (now repeat normalize_occurs_free;
       eapply IHe; [ eassumption | eassumption | intros B1 Hin1; eapply Hfv; eauto ]). 
  - repeat normalize_occurs_free. sets.
  - rewrite split_fds_occurs_free_fundefs; [| eassumption ].
    eapply Union_Included; eapply Setminus_Included_Included_Union.
    + edestruct split_fds_trans. eapply H8. eapply split_fds_sym. eassumption. destructAll.
      eapply Included_trans. eapply IHl. eassumption. eapply split_fds_sym. eassumption.
      intros B1 Hin1. eapply Hfv; eauto. inv Hin1. econstructor. eassumption. right. now eauto.
      now sets.
    + edestruct split_fds_trans. eapply split_fds_sym. eapply H8. eapply split_fds_sym. eassumption. destructAll.
      eapply Included_trans. eapply IHe. eassumption. eapply split_fds_sym. eassumption.
      intros B1 Hin1. eapply Hfv; eauto. econstructor. eassumption. now left.
      now sets.
  - rewrite split_fds_occurs_free_fundefs; [| eassumption ].
    eapply Union_Included; eapply Setminus_Included_Included_Union.
    + edestruct split_fds_trans. eapply H6. eapply split_fds_sym. eassumption. destructAll. 
      eapply IHe in H1. 2:{ eapply split_fds_sym. eassumption. }
      2:{ intros B1 Hin1. eapply Hfv; eauto. }
      eapply Included_trans. eassumption. sets.
    + edestruct split_fds_trans. eapply split_fds_sym. eapply H6. eapply split_fds_sym. eassumption. destructAll.
      eapply Included_trans. eapply IHB. eassumption. eapply split_fds_sym. eassumption.
      { intros B1 Hin1. inv Hin1. eapply Hfv; eauto. eapply Hfv; eauto. }
      now sets.
  - normalize_occurs_free. sets.
  - normalize_occurs_free. sets.
  - rewrite split_fds_occurs_free_fundefs; [| eassumption ].
    eapply Union_Included; eapply Setminus_Included_Included_Union.
    + edestruct split_fds_trans. eapply H8. eapply split_fds_sym. eassumption. destructAll. 
      eapply Included_trans. eapply IHe. eassumption. eapply split_fds_sym. eassumption.
      intros B1 Hin1. eapply Hfv; eauto. now sets.
    +  normalize_occurs_free. eapply Union_Included; eapply Setminus_Included_Included_Union.
      * edestruct split_fds_trans. eapply H8. eapply split_fds_sym. eassumption. destructAll.      
        eapply Included_trans. eapply Erase_fundefs_occurs_free. eassumption. 
        eapply split_fds_sym. eassumption. intros B1 Hin1. eapply Hfv; eauto.
        eapply Union_Included. now sets.
        eapply Included_trans. eapply occurs_free_in_fun with (B := Fcons v t l e f5).
        now left. simpl. rewrite !Union_assoc. eapply Union_Included.
        eapply Union_Included. now sets. eapply Included_trans.
        eapply Erase_nested_fundefs_name_in_fundefs. eassumption. now sets.
        eapply Included_trans. eapply Hfv. now left. now sets.
      * assert (Hs : split_fds B'0 (Fcons v t l e' Fnil) (Fcons v t l e' B'0)).
        constructor. eapply split_fds_nil_l. 
        edestruct split_fds_trans with (B1 := B'0) (B3 := B').
        eassumption. eapply split_fds_sym. eassumption. destructAll.
        
        edestruct split_fds_trans with (B1 := B'0) (B3 := Ball).
        2:{ eapply split_fds_sym. eassumption. } eassumption. destructAll.
        eapply IHB in H7. 2:{ eapply split_fds_sym. eassumption. }
        eapply Included_trans. eassumption. now sets.
        
        intros B1 Hin1. inv Hin1. 2:{ eapply Hfv; eauto. }

        eapply Included_trans. eapply Included_Union_Setminus with (s2 := [set v]). now tci.
        eapply Union_Included.
        -- eapply Included_trans; [| eapply Hfv ]; [| now left ]. normalize_occurs_free. sets.
        -- rewrite split_fds_name_in_fundefs; [| eapply Hsplit ].
           rewrite split_fds_name_in_fundefs with (B3 := B'); [| eapply H8 ].
           now sets.
  - normalize_occurs_free. sets.
Qed.



Lemma Erase_fundefs_occurs_free_fundefs_Empty_set :
  forall e e' B m
         (Herase : Erase_fundefs e e' B m)
         (Hfv : fun_fv_in e (name_in_fundefs B)),
    occurs_free_fundefs B <--> Empty_set _.
Proof.
  intros. split; sets. 
  rewrite <- Setminus_Disjoint with (s2 := name_in_fundefs B).
  2:{ eapply Disjoint_sym. eapply occurs_free_fundefs_name_in_fundefs_Disjoint. }
  eapply Included_trans. eapply Included_Setminus_compat; [| reflexivity ].
  eapply (proj1 Erase_fundefs_occurs_free_fundefs). eassumption.
  eapply split_fds_nil_r. eassumption.
  sets. 
Qed.

Lemma Erase_fundefs_unique_bindings :
  forall e e' B m (Herase : Erase_fundefs e e' B m),
    unique_bindings e ->
    unique_bindings e' /\
    unique_bindings_fundefs B /\
    Disjoint _ (bound_var_fundefs B) (bound_var e').
Proof. eapply Erase_fundefs_unique_bindings_mut. Qed.

Lemma Erase_nested_fundefs_unique_bindings :
  forall B B' m (Herase : Erase_nested_fundefs B B' m),
    unique_bindings_fundefs B ->
    unique_bindings_fundefs B'.
Proof. eapply Erase_fundefs_unique_bindings_mut. Qed.   


Lemma Erase_nested_fundefs_in_name B B_hoist f tau xs e m :
  unique_bindings_fundefs B ->
  f \in name_in_fundefs B ->  
  Erase_nested_fundefs B B_hoist m ->
  find_def f B = Some (tau, xs, e) ->
  exists e' Be Bfuns n,
    find_def f B_hoist = Some (tau, xs, e') /\
    Erase_fundefs e e' Be n /\
    split_fds Be Bfuns B_hoist /\ n <= m.
Proof.
  intros Hun Hin Hhoist Hfind.
  induction Hhoist. 
  - assert (Hunn'' : unique_bindings_fundefs B'').
    { eapply Erase_nested_fundefs_unique_bindings; [| now eapply Hun ].
      eapply Fcons_erase; eassumption. }
    inv Hun.
    destruct (peq f f0).
    * subst. simpl in Hfind. rewrite peq_true in Hfind. inv Hfind.
      do 4 eexists. split; [| split; [| split ]].
      erewrite split_fds_find_def; [ | | eassumption | ].
      simpl. rewrite peq_true. reflexivity.
      eapply unique_bindings_fundefs_unique_functions.
      eassumption. now left. eassumption.
      eassumption. eapply Nat.le_max_l.
    * subst. simpl in Hfind. rewrite peq_false in Hfind; eauto.
      inv Hin. inv H1; congruence. 
      edestruct IHHhoist as [e'' [Be' [Bfuns' [n1 [Hfind' [Hr [Hsplit Hleq]]]]]]];
        eauto.
      assert (Hfind'' : find_def f B'' = Some (tau, xs, e'')).
      { erewrite split_fds_find_def; [ | | eassumption | ].
        simpl. now  rewrite peq_false; eauto.
        eapply unique_bindings_fundefs_unique_functions. eassumption.
        right. eapply Erase_nested_fundefs_name_in_fundefs. eassumption. eassumption. }
      edestruct split_fds_trans as [Bf [Heq1 Heq2]];
        [| eapply split_fds_sym; eapply H0 | ].         
      eapply Right_f; eassumption.
      do 4 eexists. split; [| split; [| split ]].
      -- eassumption.
      -- eassumption.
      -- eassumption.
      -- eapply le_trans. eassumption. eapply Nat.le_max_r. 
  - inv Hfind.
Qed.
  
Lemma funs_in_fundef_fun_in_fundefs B Be xs t e : 
  funs_in_exp Be e ->
  fun_in_fundefs B (xs, t, e) ->
  funs_in_fundef Be B.
Proof.
  intros Hf1 Hf2. induction B.
  - inv Hf2.
    + inv H. constructor. eassumption.
    + constructor 2. eapply IHB. eassumption.
  - inv Hf2.
Qed. 

Lemma Erase_fundefs_Ecase x l1 l2 B n :
  Erase_fundefs (Ecase x l1) (Ecase x l2) B n ->
  Forall2 (fun p1 p2 => fst p1 = fst p2) l1 l2.
Proof.
  revert x l2 B n; induction l1; intros x l2 B n Herase; inv Herase; eauto.
Qed.
  
  
Section Hoisting_correct.
  
  Variable (pr : prims) (cenv : ctor_env) (G : nat). 

  Context {fuel : Type} {Hfuel : @fuel_resource fuel} {trace : Type} {Htrace : @trace_resource trace}.
  
  Context (P1 : nat -> PostT) (* Local *)
          (PG : PostGT) (* Global *)
          (HP : forall n, n <= G -> Post_properties cenv (P1 n) (P1 n) PG)
          (HPmon : forall n m, n <= m -> inclusion _ (P1 n) (P1 m))
          (Hpost_Efun_l : forall n, post_Efun_l (P1 n) (P1 (S n))).


  (** * Correctness of Erase_nested_fundefs *)
  Lemma Erase_nested_fundefs_correct S k B rho rho' B_hoist Bprev Ball n (Hleq : n <= G)
        (* IH for expresssions *)
        (IHe :
           forall m : nat,
             m < k ->
             forall (e e' : exp) (Bprev B Ball : fundefs) n (Hleq : n <= G) (rho rho' : env) (U L : nat),
               unique_bindings_fundefs Ball ->
               unique_bindings e ->
               preord_env_P cenv PG (occurs_free e) m rho rho' ->
               funs_inv_env Ball rho' ->
               split_fds Bprev B Ball ->
               Disjoint var (name_in_fundefs Ball) (bound_var e') ->
               fun_fv_in e (name_in_fundefs Ball) ->
               Erase_fundefs e e' B n -> preord_exp cenv (P1 n) PG m (e, rho) (e', rho')) :
    unique_bindings_fundefs Ball ->
    unique_bindings_fundefs B ->
    occurs_free_fundefs B \subset S ->
    (* initial environments are related *)
    preord_env_P cenv PG (S \\ name_in_fundefs B) k rho rho' ->
    (* assumptions about global funs *)     
    funs_inv_env Ball rho' ->
    split_fds Bprev B_hoist Ball ->
    Disjoint var (name_in_fundefs Ball) (bound_var_fundefs B_hoist \\ name_in_fundefs B_hoist) ->
    fun_fv_in_fundefs B (name_in_fundefs Ball) ->
    (* Erase fundefs *)
    Erase_nested_fundefs B B_hoist n ->
    (* Environments after defining the function bundles *)
    preord_env_P cenv PG (name_in_fundefs B :|: S) k (def_funs B B rho rho) rho'.
  Proof.
    revert S B n Hleq rho rho' B_hoist Bprev Ball IHe.
    induction k as [k IHk] using lt_wf_rec1.
    intros S B n Hleq rho rho' B_hoist Bprev Ball IHe Hun1 Hun2 
           Hsub Henv Hfuns Hsplit Hdis Hfvs Hhoist. assert (Hd' := HP). edestruct (Hd' n). eassumption.
    rewrite <- (Union_Setminus_Included (name_in_fundefs B) S (name_in_fundefs B)) at 1;
      [| tci | reflexivity ]. 
    eapply preord_env_P_union.
    - (* show it for the set of the added functions *)
       
      intros x Hin v Hget. rewrite def_funs_eq in Hget; eauto.
      inv Hget.

      destruct Hfuns as [rhoi Hfuns].

      eexists. split. 
      eapply Hfuns. rewrite split_fds_name_in_fundefs; [| eassumption ]. right.
      eapply Erase_nested_fundefs_name_in_fundefs. eassumption. eassumption.
      
      rewrite preord_val_eq. 
      intros vs1 vs2 j t xs1 e1 rho1' Heq1 Hf1 Hset1.
      edestruct Erase_nested_fundefs_in_name as [e2' [B2 [B2f [n1 [Hf2 [Hr2 [Hs2 Hleq']]]]]]];
        [| | | eapply Hf1 | ]; eauto.
      edestruct (@set_lists_length3 val (def_funs Ball Ball rhoi rhoi) xs1 vs2)
        as [rho2' Hset2].
      rewrite <- Heq1. eapply set_lists_length_eq. now eauto.
      do 3 eexists. split; [| split ].
      + erewrite split_fds_find_def; try eassumption.
        eapply unique_bindings_fundefs_unique_functions. eassumption.
        eapply Erase_nested_fundefs_name_in_fundefs; eassumption.
      + eauto.
      + intros Hlt Hall.
        eapply preord_exp_post_monotonic with (P1 := P1 n1). eapply Hd'. omega.

        assert (Hsplit' := Hsplit).
        eapply split_fds_sym in Hsplit.
        edestruct (split_fds_trans _ _ _ _ _ Hs2 Hsplit) as [Bprev' [Hs3 Hs4]].
        eapply IHe with (Ball := Ball) (Bprev := Bprev');
          last eassumption; try eassumption.
        * omega.
        * eapply unique_bindings_fun_in_fundefs.
          eapply find_def_correct. eassumption.
          eassumption.
        * eapply preord_env_P_antimon;
            [| eapply occurs_free_in_fun; eapply find_def_correct; eauto ].
          eapply preord_env_P_set_lists_l with (P1 := name_in_fundefs B :|: occurs_free_fundefs B);
            try now eauto.
          2:{ intros z Hnin Hinz. inv Hinz; eauto. contradiction. }
          clear Hs3 Hs4. 
          (* eapply IHk to show that inner def_funs are related *)
          { eapply IHk with (Ball := Ball); last eassumption; try eassumption. 
            - intros. eapply IHe; eauto. omega. 
            - reflexivity.
            - intros z Hinz v Hgetz. 
              inv Hinz. 
              setoid_rewrite def_funs_eq; eauto.
              eexists; split; eauto.
              
              
              edestruct Henv as [v2 [Hget2 Hv2]]; eauto. constructor; eauto.
              rewrite Hfuns in Hget2. inv Hget2; eauto.
              eapply preord_val_monotonic. eassumption. omega.
              eapply Hfvs; eauto.
              eapply Hfvs; eauto.
            - eexists. intros f1 Hf. rewrite def_funs_eq. reflexivity.
              eassumption. }
        * eexists. intros f H1. erewrite <- set_lists_not_In; [| now eauto | ].
          rewrite def_funs_eq. reflexivity. eassumption.
          assert (Hun : Disjoint var (FromList xs1) (name_in_fundefs Ball)).
          { eapply unique_bindings_fun_in_fundefs; [| eassumption ].
            erewrite split_fds_fun_in_fundefs; [| eapply Hsplit ].
            left. eapply find_def_correct. eassumption. }
          intros Hc. eapply Hun. constructor. eassumption. eassumption.
        * eapply split_fds_sym. eassumption.
        * eapply Disjoint_Included_r; [| eassumption ].
          eapply Included_Setminus.

          eapply unique_bindings_fun_in_fundefs. eapply find_def_correct. eassumption.
          eapply Erase_fundefs_unique_bindings_mut. eassumption. eassumption.
           
          eapply Included_trans; [| eapply fun_in_fundefs_bound_var_fundefs; eauto;
                                    eapply find_def_correct; eauto ].
          sets.
        * intros Be HBe. eapply Included_trans; [| eapply Hfvs ]. reflexivity.
          right. eapply funs_in_fundef_fun_in_fundefs. eassumption.
          eapply find_def_correct. eassumption.
    - (* show if for S *)
      eapply preord_env_P_def_funs_not_in_P_l; [| sets ]. 
      eapply preord_env_P_antimon. eassumption. sets.
  Qed.

  Require Import Coq.micromega.Lia. 

  (** * Correctness of Erase_fundefs *)
  
  Lemma hoisting_correct k e e' Bprev B Ball rho rho' n (Hleq : n <= G) :
    unique_bindings_fundefs Ball ->
    unique_bindings e ->
    (* environments are related *)
    preord_env_P cenv PG (occurs_free e) k rho rho' ->
    (* Hoisted functions are already defined *)
    funs_inv_env Ball rho' ->
    split_fds Bprev B Ball ->
    (* And will not be shadowed by other vars *)
    Disjoint _ (name_in_fundefs Ball) (bound_var e') ->
    (* the FVs of the original functions are in the global fundefs *)
    fun_fv_in e (name_in_fundefs Ball) ->
    (* Hoisting *)            
    Erase_fundefs e e' B n ->    
    preord_exp cenv (P1 n) PG k (e, rho) (e', rho').
  Proof.
    revert e e' Bprev B Ball n Hleq rho rho'.
    induction k as [k IHk] using lt_wf_rec1.
    intros e; revert k IHk; induction e using exp_ind';
      intros k IHk e' Bprev B Ball m Hleq' rho rho' Hun1 Hun2 Henv Hfuns Hsplit Hdis Hfvs Hhoist;
      inv Hhoist; inv Hun2; try (assert (Hd' := HP m); destruct Hd'; try omega).
    - (* Econstr *)
      eapply preord_exp_constr_compat.
      + now eauto.
      + now eauto.
      + eapply Forall2_same. intros x Hin. eapply Henv.
        now constructor.
      + intros m1 vs1 vs2 Hlt Hall. 
        eapply IHk; [ eassumption | eassumption | eassumption | | | | eassumption | | | ].
        * eassumption.
        * eapply preord_env_P_extend.
          -- eapply preord_env_P_antimon.
             eapply preord_env_P_monotonic; [| eassumption ]. omega. 
             normalize_occurs_free. sets.
          -- rewrite preord_val_eq. constructor; eauto.
             eapply Forall2_Forall2_asym_included. eassumption.
        * eapply funs_inv_env_set. eassumption.
          eapply Disjoint_In_l. eapply Disjoint_sym. eassumption.
          normalize_bound_var; sets.
        * eapply Disjoint_Included_r; [| eassumption ].
          normalize_bound_var; sets.
        * intros B' Hbin. eapply Hfvs. constructor; eauto.
        * eassumption.
    - (* Ecase nil *)
      eapply preord_exp_case_nil_compat. eapply HP. omega.
    - (* Ecase cons *)
      eapply split_fds_sym in H8.
      edestruct split_fds_trans as [Bnew [Hs1 Hs2]].
      now eapply H8. eapply split_fds_sym. eassumption.
      eapply split_fds_sym in H8.
      edestruct split_fds_trans as [Bnew' [Hs1' Hs2']].
      now eapply H8. eapply split_fds_sym. eassumption.      
      eapply preord_exp_case_cons_compat; eauto.
      + eapply HP. omega.
      + eapply HP. omega.
      + eapply HP. omega.
      + eapply Erase_fundefs_Ecase. eassumption.
      + intros m Hlt.
        eapply preord_exp_post_monotonic. eapply HPmon with (n := m0). lia.
        eapply IHk; last eassumption; eauto.
        * lia.
        * eapply preord_env_P_antimon.
          eapply preord_env_P_monotonic; [| eassumption ]. omega.
          normalize_occurs_free; sets.
        * apply split_fds_sym. eassumption.
        * eapply Disjoint_Included_r; [| eassumption ].
          normalize_bound_var; sets.
        * intros x Hin; eapply Hfvs. econstructor; eauto.
          now left.
      + eapply preord_exp_post_monotonic. eapply HPmon with (n := n). lia.
        eapply IHe0; last eassumption; eauto.
        * lia.
        * eapply preord_env_P_antimon. eassumption.
          normalize_occurs_free; sets.
        * apply split_fds_sym. eassumption.
        * eapply Disjoint_Included_r; [| eassumption ].
          normalize_bound_var; sets.
        * intros x Hin; eapply Hfvs.
          inv Hin. econstructor. eassumption.
          right. eassumption.
    - (* Eproj *)
      eapply preord_exp_proj_compat.
      + now eauto.
      + now eauto. 
      + eapply Henv. eauto.
      + intros m1 vs1 vs2 Hlt Hall. 
        eapply IHk; [ eassumption | eassumption | eassumption | | | | eassumption | | | ].
        * eassumption.
        * eapply preord_env_P_extend.
          -- eapply preord_env_P_antimon.
             eapply preord_env_P_monotonic; [| eassumption ]. omega.
             normalize_occurs_free. sets.
          -- eassumption.
        * eapply funs_inv_env_set. eassumption.
          eapply Disjoint_In_l. eapply Disjoint_sym. eassumption.
          normalize_bound_var; sets.
        * eapply Disjoint_Included_r; [| eassumption ].
          normalize_bound_var; sets.
        * intros B' Hbin. eapply Hfvs. constructor; eauto.
        * eassumption.
    - (* Eletapp *)
      eapply preord_exp_letapp_compat.
      + now eauto.
      + now eauto. 
      + now eauto.
      + eapply Henv. constructor. now left.
      + eapply Forall2_same. intros z Hin. eapply Henv.
        constructor. now right.
      + intros m1 v1 v2 hlew Hrel.
        eapply IHk; [ eassumption | eassumption | eassumption | | | | eassumption | | | ].
        * eassumption.
        * eapply preord_env_P_extend.
          -- eapply preord_env_P_antimon.
             eapply preord_env_P_monotonic; [| eassumption ]. omega.
             normalize_occurs_free. sets.
          -- eassumption.
        * eapply funs_inv_env_set. eassumption.
          eapply Disjoint_In_l. eapply Disjoint_sym. eassumption.
          normalize_bound_var; sets.
        * eapply Disjoint_Included_r; [| eassumption ].
          normalize_bound_var; sets.
        * intros B' Hbin. eapply Hfvs. constructor; eauto.
        * eassumption.
    - (* Efun -- the only non trivial case *)
      eapply preord_exp_Efun_l.
      + eapply HP. lia. 
      + now eauto.
      + eapply split_fds_sym in Hsplit.
        eapply split_fds_sym in H6.
        edestruct split_fds_trans as [Bnew [Hs1 Hs2]]. now eapply H6. eassumption.        
        eapply split_fds_sym in H6.
        edestruct split_fds_trans as [Bnew' [Hs1' Hs2']]. now eapply H6. eassumption.
        eapply preord_exp_post_monotonic. eapply HPmon with (n := n). lia.
                                  
        eapply IHe with (Ball := Ball); [ | | eassumption | eassumption | | | | | | eassumption ].
        * intros. eapply IHk; eauto. omega.
        * lia. 
        * eapply preord_env_P_antimon.
          -- { eapply Erase_nested_fundefs_correct with (S := occurs_free_fundefs f2 :|: occurs_free e);
               [ | | | | | | | | | | eassumption ].
               - lia. 
               - intros. eapply IHk; eauto. omega.
               - eapply Hun1.
               - eassumption.
               - sets.
               - eapply preord_env_P_antimon. eapply preord_env_P_monotonic; [| eassumption ].
                 omega. normalize_occurs_free; sets.
                 rewrite Setminus_Union_distr. sets.
               - eassumption.
               - eapply split_fds_sym.  eassumption.
               - edestruct Erase_fundefs_unique_bindings.

                 eapply Efun_erase. eassumption. eassumption. eassumption. constructor; eassumption.
                 destructAll.
                 
                 rewrite (split_fds_name_in_fundefs _ _ _ Hs2). eapply Union_Disjoint_l.
                 now sets.
                 eapply split_fds_unique_bindings_fundefs_l in Hs2. destructAll.
                 eapply Disjoint_Included_l. eapply name_in_fundefs_bound_var_fundefs. sets.
                 eassumption.
               - intros x Hfv. inv Hfv; eauto. }
          -- sets.         
        * eassumption.
        * eapply split_fds_sym. eassumption.
        * eapply Disjoint_Included_r; [| eassumption ]. reflexivity. 
        * intros x Hin. eapply Hfvs. constructor; eauto.
    - (* Eapp *)
      eapply preord_exp_app_compat.
      + eapply HP. lia.
      + eapply HP. lia.
      + eapply Henv. constructor.
      + eapply Forall2_same. intros z Hin. eapply Henv.
        now constructor.
    - (* Eprim *)
      eapply preord_exp_prim_compat.
      + now eauto.
      + eapply Forall2_same. intros x Hin. eapply Henv.
        now constructor.
    - (* Ehalt *)
      eapply preord_exp_halt_compat; eauto.
      + eapply HP. lia.
      + eapply HP. lia.
  Qed.


  (* TODO move *)
  Open Scope alg_scope.
  

  Context (P2: @PostT fuel trace). 

  Context (Hp2 : forall n, n <= G -> post_Efun_r (P1 n) P2) (Hoot2 : post_OOT P2). 
  
  Lemma Erase_fundefs_correct_top e e' B n (Hleq : n <= G) :
    unique_bindings e ->
    Disjoint _ (occurs_free e) (bound_var e) ->
    fun_fv_in e (funnames_in_exp e) ->
    (* Hoisting *)            
    Erase_fundefs e e' B n ->

    (forall k rho rho',
        preord_env_P cenv PG (occurs_free e) k rho rho' ->
        preord_exp cenv P2 PG k (e, rho) (Efun B e', rho')) /\
    unique_bindings (Efun B e') /\
    Disjoint _ (occurs_free (Efun B e')) (bound_var (Efun B e')) /\
    occurs_free (Efun B e') \subset occurs_free e.
  Proof.
    intros Hub Hdis Hin Her. split; [| split; [| split ] ].
    { intros k rho rho' Henv. 
      eapply preord_exp_Efun_r.
      - eassumption.
      - eauto.
      - edestruct Erase_fundefs_unique_bindings. eassumption. eassumption. destructAll.
        eapply hoisting_correct with (Bprev := Fnil) (B := B) (Ball := B).
        + omega. 
        + eassumption.
        + eassumption.
        + eapply preord_env_P_def_funs_not_in_P_r. eassumption. 
          eapply Disjoint_Included_r; [| eassumption ].
          rewrite Erase_fundefs_bound_var; [| eassumption ].
          eapply Included_trans. eapply name_in_fundefs_bound_var_fundefs. sets.
        + eexists rho'. intros f Hfin. rewrite def_funs_eq. reflexivity. eassumption.
        + eapply split_fds_nil_r.
        + eapply Disjoint_Included_l. eapply name_in_fundefs_bound_var_fundefs. eassumption.
        + eapply Erase_fundefs_fun_fv_in. eassumption. eassumption.
        + eassumption. }
    { edestruct Erase_fundefs_unique_bindings. eassumption. eassumption. destructAll.
      constructor; eauto. sets. }
    { normalize_occurs_free.
      eapply Disjoint_Included_r.
      eapply Included_Union_Setminus with (s2 := name_in_fundefs B). tci. 

      eapply Union_Disjoint_l.
      - rewrite Erase_fundefs_occurs_free_fundefs_Empty_set. sets. eassumption.
        eapply Erase_fundefs_fun_fv_in. eassumption. eassumption.        
      - eapply Union_Disjoint_r; [| sets ].
        eapply Disjoint_Included_l. eapply Included_Setminus_compat. 
        eapply Erase_fundefs_occurs_free. eassumption.
        eapply split_fds_nil_r. eapply Erase_fundefs_fun_fv_in. eassumption. eassumption.        
        reflexivity. rewrite Setminus_Union_distr. rewrite Setminus_Same_set_Empty_set.
        repeat normalize_sets.
        normalize_bound_var. rewrite Union_commut. rewrite <- Erase_fundefs_bound_var; [| eassumption ].
        sets. }
    { repeat normalize_occurs_free.
      rewrite Erase_fundefs_occurs_free_fundefs_Empty_set; try eassumption.
      2:{ eapply Erase_fundefs_fun_fv_in. eassumption. eassumption. }
      normalize_sets. 
      
      eapply Included_trans. eapply Included_Setminus_compat; [| reflexivity ].
      eapply Erase_fundefs_occurs_free. eassumption.
      eapply split_fds_nil_r. eapply Erase_fundefs_fun_fv_in. eassumption. eassumption.        
      sets. }
  Qed.

  Context (Hinc : forall n, n <= G -> inclusion (exp * env * fuel * trace) (P1 n) P2).
  
  Lemma Erase_fundefs_correct_top_Fnil e e' n (Hleq : n <= G) :
    unique_bindings e ->
    Disjoint _ (occurs_free e) (bound_var e) ->
    fun_fv_in e (funnames_in_exp e) ->
    (* Hoisting *)            
    Erase_fundefs e e' Fnil n ->

    (forall k rho rho',
        preord_env_P cenv PG (occurs_free e) k rho rho' ->
        preord_exp cenv P2 PG k (e, rho) (e', rho')) /\
    unique_bindings e' /\
    Disjoint _ (occurs_free e') (bound_var e') /\
    occurs_free e' \subset occurs_free e.
  Proof.
    intros Hub Hdis Hin Her.
    edestruct Erase_fundefs_correct_top; try eassumption. destructAll. clear H.
    inv H0.
    rewrite occurs_free_Efun, occurs_free_fundefs_Fnil in H1.
    rewrite bound_var_Efun, bound_var_fundefs_Fnil in H1.
    simpl in H1. repeat normalize_sets.

    split; [| split; [| split ] ]; try eassumption.
    intros k rho rho' Henv. 

    edestruct Erase_fundefs_unique_bindings. eassumption. eassumption. destructAll.
    eapply preord_exp_post_monotonic. eapply Hinc. eassumption. 
    eapply hoisting_correct with (Bprev := Fnil) (B := Fnil) (Ball := Fnil).
    + eassumption.
    + eassumption.
    + eassumption.
    + eassumption.
    + eexists rho'. intros f Hfin. inv Hfin.
    + eapply split_fds_nil_r.
    + now sets.
    + eapply Erase_fundefs_fun_fv_in. eassumption. eassumption.
    + eassumption.
    + eapply Included_trans.
      eapply Erase_fundefs_occurs_free. eassumption.
      eapply split_fds_nil_r. eapply Erase_fundefs_fun_fv_in. eassumption. eassumption.        
      sets.
  Qed.

  Lemma exp_hoist_correct_top e e' n (Hleq : n <= G) :
    unique_bindings e ->
    Disjoint _ (occurs_free e) (bound_var e) ->
    fun_fv_in e (funnames_in_exp e) ->
    
    exp_hoist e = (e', n) -> 

    (forall k rho rho',
        preord_env_P cenv PG (occurs_free e) k rho rho' ->
        preord_exp cenv P2 PG k (e, rho) (e', rho')) /\
    unique_bindings e' /\
    Disjoint _ (occurs_free e') (bound_var e') /\
    occurs_free e' \subset occurs_free e.
  Proof.
    intros Hun Hdis Hfv Hh.
    unfold exp_hoist in Hh.

    edestruct (proj1 erase_fundefs_in_Erase_fundefs) as [e1 [B1 [B2 [m [H1 [Hs H2]]]]]].
    rewrite H1 in Hh. unfold id in *. clear H1.
    eapply split_fds_Fnil_eq_l in Hs. rewrite Hs in *. clear Hs. 
    destruct B1.
    - inv Hh. eapply Erase_fundefs_correct_top; eauto.
    - inv Hh. eapply Erase_fundefs_correct_top_Fnil; eauto.
  Qed.
    
End Hoisting_correct.

(* 

(** Hoisting as a rewrite relation *)
Inductive hoist_rw : relation exp :=
| EConstr_hoist :
    forall x t ys B e,
      hoist_rw (Econstr x t ys (Efun B e))
               (Efun B (Econstr x t ys e))
| Ecase_hoist :
    forall x tes t e' tes' B,
      hoist_rw (Ecase x (tes ++ ((t, Efun B e') :: tes')))
               (Efun B (Ecase x (tes ++ ((t, e') :: tes'))))
| Eproj_hoist :
    forall x tau N y e B,
      hoist_rw (Eproj x tau N y (Efun B e))
               (Efun B (Eproj x tau N y e))
| Eletapp_hoist :
    forall x f tau ys e B,
      hoist_rw (Eletapp x f tau ys (Efun B e))
               (Efun B (Eletapp x f tau ys e))
| Efun_hoist :
    forall B B' B'' e,
      split_fds B B' B'' ->
      hoist_rw (Efun B (Efun B' e)) (Efun B'' e)
| Eprim_hoist :
    forall x f ys e B,
      hoist_rw (Eprim x f ys (Efun B e))
               (Efun B (Eprim x f ys e))
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
    | Econstr _ _ _ e | Eproj _ _ _ _ e | Eletapp _ _ _ _ e
    | Eprim _ _ _ e => exp_fun_count e
    | Ecase _ P =>
      fold_left (fun n p => n + (exp_fun_count (snd p))) P 0
    | Efun B e => exp_fun_count e + fundefs_fun_count B
    | Eapp _ _ _ => 0
    | Ehalt _ => 0
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
    + revert c1 e tes l0 H1 H2 H0. induction l; intros c1 e tes l0 H1 H2 H0.
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
  - revert c1 e tes l0 H1 H2 H0. induction l; intros c1 e tes l0 H1 H2 H0.
    + simpl in *. inv H0. constructor; eauto.
    + inv H1.
      inv H0. symmetry in H3. apply app_eq_nil in H3. inv H3. inv H0.
      inv H0. simpl. constructor; eauto. 
Qed.

Ltac exp_to_ctx e c :=
  match e with
  | Econstr ?x ?t ?ys ?e => constr:(Econstr_c x t ys c)
  | Eletapp ?x ?f ?t ?ys ?e => constr:(Eletapp_c x f t ys c)                                    
  | Ecase ?x (?tes ++ (?t, ?e) :: ?tes') => constr:(Ecase_c x tes t e c tes')
  | Eproj ?x ?tau ?N ?y ?e => constr:(Eproj_c x tau N y c)
  | Efun ?B ?e => constr:(Efun1_c B c)
  | Eprim ?x ?f ?ys ?e => constr:(Eprim_c x f ys c)
  end.

Fixpoint f c e' e : exp :=
  match e with
    | Econstr x t ys e =>
      Econstr x t ys (f c e' e)
    | Ecase x l => Ecase x ((c, e') :: l)
    | Eproj x tag n y e =>
      Eproj x tag n y (f c e' e)
    | Eletapp x g tag ys e =>
      Eletapp x g tag ys (f c e' e)
    | Efun B e => Efun B (f c e' e)
    | Eapp x ft x0 => e
    | Eprim x f' ys e =>
      Eprim x f' ys (f c e' e)
    | Ehalt x => e
  end.

Inductive g (f' : var) (t : ctor_tag) (xs' : list var) (e' : exp)
: exp -> exp -> Prop :=
| g_constr :
    forall x tag ys e1 e2,
      g f' t xs' e' e1 e2 ->
      g f' t xs' e' (Econstr x tag ys e1) (Econstr x tag ys e2)
| g_proj :
    forall x tag N y e1 e2,
      g f' t xs' e' e1 e2 ->
      g f' t xs' e' (Eproj x tag N y e1) (Eproj x tag N y e2)
| g_letapp :
    forall x f tag ys e1 e2,
      g f' t xs' e' e1 e2 ->
      g f' t xs' e' (Eletapp x f tag ys e1) (Eletapp x f tag ys e2)
| g_fun1 :
    forall B e,
      B <> Fnil ->
      g f' t xs' e' (Efun B e) (Efun (Fcons f' t xs' e' B) e)
| g_fun2 :
    forall B e,
      B <> Fnil ->
      g f' t xs' e' (Efun B e) (Efun B e)
| g_fun_Fnil :
    forall e1 e2,
      g f' t xs' e' e1 e2 ->
      g f' t xs' e' (Efun Fnil e1) (Efun Fnil e2)
| g_prim :
    forall x f ys e1 e2,
      g f' t xs' e' e1 e2 ->
      g f' t xs' e' (Eprim x f ys e1) (Eprim x f ys e2)
| g_app :
    forall f ft xs,
      g f' t xs' e' (Eapp f ft xs) (Eapp f ft xs)
| g_halt :
    forall x, g f' t xs' e' (Ehalt x) (Ehalt x)
| g_case :
     forall x P,
       g f' t xs' e' (Ecase x P) (Ecase x P).


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
    + right. exists (Ecase_c v ((c, e) :: l) c0 c' l0); eauto.
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
    eapply compat_closure_compat with (c:= Econstr_c v c l Hole_c). eauto.
    constructor. eauto.
  - inv Hr'. edestruct IHc as [e2'' [Hrw2 Hr2]]; eauto. 
    eexists; split; eauto.
    eapply compat_closure_compat with (c:= Eproj_c v c n v0 Hole_c). eauto.
    constructor. eauto.
  - inv Hr'. edestruct IHc as [e2'' [Hrw2 Hr2]]; eauto. 
    eexists; split; eauto.
    eapply compat_closure_compat with (c:= Eprim_c v p l Hole_c). eauto.
    constructor. eauto.
  - inv Hr'. edestruct IHc as [e2'' [Hrw2 Hr2]]; eauto. 
    eexists; split; eauto.
    eapply compat_closure_compat with (c:= Eletapp_c v v0 f0 l Hole_c). eauto.
    constructor. eauto.    
  - inv Hr'. eexists.  split; try now constructor.
    apply Compat with (c := Ecase_c v l c c0 l0); eauto.
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
    inv Hrw'; try (now inv Hg;
                   match goal with [ _ : g _ _ _ _ _ _, H : g _ _ _ _ _ _ |- _ ] => inv H end;
                   eexists; split; constructor; eauto; try (constructor; eauto)).
    + inv Hg. eexists. split.
      econstructor. try now constructor.
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
    + right. exists (Ecase_c v ((c, e) :: l) c0 c' l0); eauto.
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
  - eapply hoist_star_compat with (c := Econstr_c v t l Hole_c); eauto.
  - exists 0; econstructor; eauto.
  - apply split_fds_Fnil in H8. inv H8.
    specialize (IHl (Ecase v tes') H6). inv IHl; eauto.
    eapply hoist_star_trans.
    eapply hoist_star_compat with (c := Ecase_c v [] c Hole_c l); eauto.
    eapply hoist_star_Ecase_cons_1; try (now eexists; eauto).
  - eapply hoist_star_compat with (c := Eproj_c v t n v0 Hole_c); eauto.
  - eapply hoist_star_compat with (c := Eletapp_c x f0 ft ys Hole_c); eauto.
  - apply split_fds_Fnil in H6. inv H6.
    eapply hoist_star_trans.
    eapply hoist_star_compat with (c := Efun1_c f2 Hole_c); eauto.
    apply IHdefs; eauto.
  - exists 0; constructor; eauto.
  - eapply hoist_star_compat with (c := Eprim_c v p l Hole_c); eauto.
  - econstructor. constructor.
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
  [| | | | | | | | | intros B' e1 Hnil H |intros B' e1 Hnil H ];
  try intros e1 B' Hnil H; inv H.
  - eapply hoist_star_trans.
    eapply hoist_star_compat with (c := Econstr_c v t l Hole_c); eauto.
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
  - eapply hoist_star_trans.
    eapply hoist_star_compat with (c := Eletapp_c x f0 ft ys Hole_c); eauto.
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
    eapply hoist_star_compat with (c := Eprim_c v p l Hole_c); eauto.
    apply hoist_rw_hoist_star. constructor.
  - congruence.
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
Proof with now eauto 6 with Ensembles_DB.
  intros e1 e2 Hun Hrw; inv Hrw; simpl.
  - inv Hun. inv H4. constructor; eauto. constructor; eauto.
    normalize_bound_var.
    eapply Union_Disjoint_l. eassumption. 
    eapply Disjoint_Singleton_l. intros HB; eauto.
  - inv Hun. exfalso. eapply app_cons_not_nil; eauto.
    destruct tes.
    + inv H0. simpl. inv H2. rewrite bound_var_Efun in H3.
      constructor; eauto. constructor; eauto.
      eauto with Ensembles_DB.
      normalize_bound_var...
    + inv H0.
      edestruct unique_bindings_Ecase_l as [H1' [H2' [H3' [H4' [H5' H6']]]]]; eauto.
      inv H1'. repeat normalize_bound_var_in_ctx.
      constructor; eauto.
      * eapply unique_bindings_Ecase_r; [ assumption | | assumption | | | ].
        constructor. assumption. assumption. now eauto with Ensembles_DB. 
        clear H5' H6' H6. normalize_bound_var...
        eauto with Ensembles_DB.
        normalize_bound_var...
      * clear H6'. repeat normalize_bound_var. eauto 9 with Ensembles_DB.
  - inv Hun. inv H5. constructor; eauto. constructor; eauto.
    normalize_bound_var...
  - inv Hun. inv H5. constructor; eauto. constructor; eauto.
    normalize_bound_var...    
  - inv Hun. inv H2. rewrite bound_var_Efun in H4. constructor; eauto.
    eapply (split_fds_unique_bindings_fundefs_r B B' B''); eauto.
    eauto with Ensembles_DB.
    rewrite split_fds_bound_vars; eauto...
  - inv Hun. inv H4. constructor; eauto. constructor; eauto.
    normalize_bound_var...
  - inv Hun; eauto.
  - inv Hun. 
    edestruct split_fds_unique_bindings_fundefs_l as [H1' [H2' H3']];
      [| apply H |]; eauto. inv H2'. inv H17.
    rewrite bound_var_Efun in *. rewrite bound_var_fundefs_Fcons in *.
    repeat normalize_bound_var_in_ctx.
    constructor; eauto.
    + clear H13 H14. eapply (split_fds_unique_bindings_fundefs_r B3 B4); eauto.
      eapply (split_fds_unique_bindings_fundefs_r B1 (Fcons f0 tau xs e' Fnil)); eauto.
      constructor; eauto.
      clear H9. eauto 6 with Ensembles_DB.
      normalize_bound_var...
      normalize_bound_var...
      repeat normalize_bound_var. eauto with Ensembles_DB.
      rewrite (split_fds_bound_vars B1 (Fcons f0 tau xs e' Fnil) B4); eauto.
      repeat normalize_bound_var. eauto 15 with Ensembles_DB.
    + rewrite (split_fds_bound_vars B3 B4 B); eauto.
      rewrite (split_fds_bound_vars B1 (Fcons f0 tau xs (Efun B3 e') Fnil) B2)
        in *; eauto.
      rewrite (split_fds_bound_vars B1 (Fcons f0 tau xs e' Fnil) B4); eauto.
      repeat normalize_bound_var_in_ctx. repeat normalize_bound_var.
      clear H13 H14. eauto 15 with Ensembles_DB.
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
Proof with now eauto with Ensembles_DB.
  intros Hs HI1 HI2. unfold closed_fundefs.
  rewrite occurs_free_fundefs_big_cup in *.
  rewrite Same_Set_big_cup_l; [| eapply split_fds_fun_in_fundefs; eassumption ].
  rewrite Setminus_big_cup in *.
  rewrite Union_big_cup.
  rewrite split_fds_name_in_fundefs; [| eassumption ].
  rewrite Setminus_Union_distr.
  rewrite (Union_commut (name_in_fundefs B1) (name_in_fundefs B2)) at 2.
  rewrite <- !Setminus_Union.
  split; [| intros x Hc; now inv Hc ].
  eapply Included_trans.
  eapply Included_Union_compat.
  eapply Included_Setminus_compat. eassumption. now eapply Included_refl.
  eapply Included_Setminus_compat. eassumption. now eapply Included_refl.
  eauto with Ensembles_DB.
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
        simpl in *. rewrite !Union_Empty_set_neut_r, H3, !Union_Empty_set_neut_l.
        rewrite occurs_free_fundefs_Fnil in *.
        rewrite Setminus_Empty_set_abs_r, Union_Empty_set_neut_r, Setminus_Union.
        eapply Included_Setminus_antimon; [| now eapply occurs_free_Efun_Included ].
        rewrite Setminus_Union_distr, <- Union_assoc at 1.
        rewrite H2, Union_Empty_set_neut_l. now eauto with Ensembles_DB.
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
Proof with now eauto with Ensembles_DB.
  exp_fundefs_ctx_induction IHc IHf; eauto;
  try (intros e' [H1 H2];
       assert (H3 : unique_bindings e')
         by (eapply unique_bindings_SubtermInvariant; eauto);
      split; [| assumption ]); simpl in *.
  - inv H2. apply IHc. split; [| assumption ].
    repeat normalize_bound_var_in_ctx.
    repeat normalize_occurs_free_in_ctx.
    eapply Disjoint_Included;
      [ now apply occurs_free_Econstr_Included with (t := t)
      | now apply Included_refl |].
    normalize_occurs_free...
  - inv H2. apply IHc; split; [| assumption ].
    rewrite bound_var_Eproj, occurs_free_Eproj in *.
    eapply Disjoint_Included;
      [ now apply occurs_free_Eproj_Included with (tau := t) (t := n)
      | now apply Included_refl |]. 
    normalize_occurs_free...
  - inv H2. apply IHc; split; [| assumption ].
    rewrite bound_var_Eletapp, occurs_free_Eletapp in *.
    eapply Disjoint_Included;
      [ now apply (occurs_free_Eletapp_Included v f0 ft ys)
      | now apply Included_refl |]. 
    normalize_occurs_free...
  - inv H2. apply IHc; split; [| assumption ].
    rewrite bound_var_Eprim, occurs_free_Eprim in *.
    eapply Disjoint_Included;
      [ now apply occurs_free_Eprim_Included with (f := p)
      | now apply Included_refl |]. 
    normalize_occurs_free...
  - intros l' e' [H1 H2].
    assert (H3 : unique_bindings e') 
      by (eapply unique_bindings_SubtermInvariant
          with (c := Ecase_c v l t e l'); eauto).
    split; [| assumption ].
    repeat normalize_occurs_free_in_ctx. repeat normalize_bound_var_in_ctx.
    edestruct unique_bindings_Ecase_l as [H1' [H2' [H3' [H4' [H5' H6']]]]].
    eassumption. 
    eapply IHc; split; [| eassumption ].
    eapply Disjoint_Included; [| | now eapply H1 ]...
  - inv H2. eapply IHc; split; [| eassumption ].
    repeat normalize_occurs_free_in_ctx. repeat normalize_bound_var_in_ctx.
    eapply Disjoint_Included; [| now apply Included_refl |].
    now apply occurs_free_Efun_Included. 
    normalize_occurs_free.
    eapply Union_Disjoint_r. eauto with Ensembles_DB. 
    eapply Disjoint_Included_r.
    now eapply name_in_fundefs_bound_var_fundefs. eassumption.
  - inv H2. eapply IHf. split; [| eassumption ].
    repeat normalize_occurs_free_in_ctx. repeat normalize_bound_var_in_ctx.
    eapply Disjoint_Included; [| | now apply H1 ]...
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
    apply Union_Disjoint_r. eassumption.
    apply Union_Disjoint_r. apply Union_Disjoint_r.
    eauto with Ensembles_DB.
    eapply Disjoint_Included_r. now apply name_in_fundefs_bound_var_fundefs.
    eassumption. eauto with Ensembles_DB.
  - intros e' [H1 H2].
    assert (H3 : unique_bindings e')
      by (eapply unique_bindings_SubtermInvariant'
          with (f := Fcons2_c v t l e f7); eauto).
    split; [| eassumption ].
    inv H2. eapply IHf; split; [| eassumption ].
    repeat normalize_bound_var_in_ctx. repeat normalize_occurs_free_in_ctx.
    eapply Disjoint_Included; [| now apply Included_refl |].
    eapply (occurs_free_fundefs_Fcons_Included v t l e (f7 <[ e' ]>)).
    rewrite occurs_free_fundefs_Fcons.
    eauto 6 with Ensembles_DB.
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
Proof with now eauto 6 with Ensembles_DB.
  intros e1 e2 [HD [Hclo Hun]] Hrw.
  assert (Hun' : unique_bindings e2)
    by (eapply unique_bindings_Invariant; eauto).
  assert (Hclo'' : closed_fundefs_in_exp e2)
    by (eapply closed_fundefs_in_exp_Invariant; eauto).
  split; [| split; eassumption ];
  inv Hrw; simpl; clear Hun Hun';
  repeat normalize_occurs_free_in_ctx; repeat normalize_bound_var_in_ctx;
  repeat normalize_occurs_free; repeat normalize_bound_var.    
  - assert (Hclo' : closed_fundefs B) by (eapply Hclo; eauto).
    unfold closed_fundefs in Hclo'. rewrite Hclo', !Union_Empty_set_neut_l in *.
    rewrite Union_assoc.    
    eapply Disjoint_Included_r; [| now apply HD].
    rewrite Setminus_Union_distr. eauto 6 with Ensembles_DB.
  - assert (Hclo' : closed_fundefs B) by (eapply Hclo''; eauto).
    unfold closed_fundefs in Hclo'. rewrite Hclo', !Union_Empty_set_neut_l in *.
    eapply Disjoint_Included; [| | eassumption ]; eauto 6 with Ensembles_DB.
    apply Setminus_Included_Included_Union.
    rewrite <- !Union_assoc,  <- Union_Included_Union_Setminus;
      eauto with Ensembles_DB typeclass_instances.
  - assert (Hclo' : closed_fundefs B) by (eapply Hclo; eauto).
    unfold closed_fundefs in Hclo'. rewrite Hclo', !Union_Empty_set_neut_l in *.
    rewrite Union_assoc.
    eapply Disjoint_Included_r; [| now apply HD].
    rewrite Setminus_Union_distr...
  - assert (Hclo' : closed_fundefs B) by (eapply Hclo; eauto).
    unfold closed_fundefs in Hclo'. rewrite Hclo', !Union_Empty_set_neut_l in *.
    rewrite Union_assoc.
    eapply Disjoint_Included_r; [| now apply HD].
    rewrite Setminus_Union_distr...
  - rewrite split_fds_bound_vars; [| eassumption ].
    rewrite split_fds_name_in_fundefs; [| eassumption ].
    rewrite split_fds_occurs_free_fundefs; [| eassumption ].
    assert (Hclo1 : closed_fundefs B') by (eapply Hclo; eauto).
    assert (Hclo2 : closed_fundefs B) by (eapply Hclo; eauto).
    unfold closed_fundefs in Hclo1, Hclo2.
    rewrite Hclo1, Hclo2.
    rewrite <- Union_assoc. eapply Disjoint_Included_r; [| eassumption ].
    rewrite !Setminus_Empty_set_abs_r, !Union_Empty_set_neut_l...
  - assert (Hclo' : closed_fundefs B) by (eapply Hclo; eauto).
    unfold closed_fundefs in Hclo'. rewrite Hclo'.
    rewrite Union_assoc. eapply Disjoint_Included_r; [| eassumption ].
    rewrite !Union_Empty_set_neut_l,  !Setminus_Union_distr.
    apply Union_Included. eauto with Ensembles_DB.
    rewrite !Setminus_Union. eauto with Ensembles_DB.
  - rewrite Setminus_Empty_set_neut_r, !Union_Empty_set_neut_l in HD. assumption.
  - assert (Hclo2 : closed_fundefs B) by (eapply Hclo''; eauto).
    unfold closed_fundefs in Hclo2. rewrite Hclo2, !Union_Empty_set_neut_l in *.
    clear Hclo2.
    rewrite split_fds_bound_vars in *; try eassumption. 
    rewrite (split_fds_bound_vars B1 (Fcons f0 tau xs e' Fnil) B4) in *; try eassumption.
    rewrite split_fds_occurs_free_fundefs in *; try eassumption.
    rewrite split_fds_name_in_fundefs with (B3 := B)  in *; try eassumption.
    rewrite split_fds_name_in_fundefs with (B3 := B2)  in *; try eassumption.
    rewrite split_fds_name_in_fundefs with (B3 := B4) at 1; try eassumption.
    repeat normalize_bound_var. repeat normalize_bound_var_in_ctx.
    simpl in *.
    eapply Disjoint_Included; [|  | now apply HD].
    + eapply Setminus_Included_Included_Union.
      repeat rewrite (Union_Empty_set_neut_r (Singleton _ _)) at 1.
      rewrite <- Union_assoc, <- (Union_Included_Union_Setminus (occurs_free _));
        eauto with Ensembles_DB typeclass_instances.
    + rewrite !Union_Empty_set_neut_r. eauto 7 with Ensembles_DB. 
Qed.


Lemma bound_var_Invariant S :
  Invariant hoist_rw (fun e => Same_set _ (bound_var e) S).
Proof with now eauto 10 with Ensembles_DB.
  intros e1 e2 HS Hrw; inv Hrw; repeat normalize_bound_var_in_ctx; repeat normalize_bound_var;
  try (now rewrite <- HS; eauto with Ensembles_DB).
  - rewrite <- HS.
    rewrite split_fds_bound_vars; [| eassumption ]. symmetry...
  - rewrite split_fds_bound_vars; [| eassumption ].
    rewrite (split_fds_bound_vars B1 (Fcons f0 tau xs e' Fnil) B4); [| eassumption ].
    rewrite (split_fds_bound_vars B1 (Fcons f0 tau xs (Efun B3 e') Fnil) B2) in HS
    ; [| eassumption ].
    rewrite <- HS. repeat normalize_bound_var.
    rewrite !Union_Empty_set_neut_r, (Union_commut (bound_var_fundefs B3))...
Qed.

Require Import L6.tactics.

Lemma occurs_free_disjoint_ident_Invariant S :
  Invariant hoist_rw (fun e => Same_set _(occurs_free e) S /\
                               Disjoint _ (bound_var e) (occurs_free e)  /\
                               closed_fundefs_in_exp e /\
                               unique_bindings e).
Proof with now eauto with Ensembles_DB.
  intros e1 e2 [HS [HD [Hcl Hun]]] Hrw.
  assert ( H : Disjoint var (bound_var e2) (occurs_free e2) /\
               closed_fundefs_in_exp e2 /\ unique_bindings e2)
    by (eapply disjoint_ident_Invariant; eauto).
  split; [| eassumption ]. destruct H as [HD' [Hcl' _]].
  unfold closed_fundefs_in_exp, closed_fundefs in *.
  rewrite <- HS; clear HS.
  inv Hrw; repeat normalize_bound_var_in_ctx; repeat normalize_occurs_free_in_ctx;
  repeat normalize_occurs_free; repeat normalize_bound_var;
  try (now rewrite <- HS; eauto with Ensembles_DB).
  - inv Hun. rewrite !Setminus_Union_distr.
    rewrite (Union_assoc (FromList _) _), (Union_commut (FromList _)), <- Union_assoc.
    apply Same_set_Union_compat; [| apply Same_set_Union_compat ].
    + rewrite Setminus_Disjoint. reflexivity.
      rewrite Hcl.
      now apply Disjoint_Empty_set_l. now constructor.
    + rewrite Setminus_Disjoint. reflexivity. 
      eapply Disjoint_sym. eapply Disjoint_Included; [| | now apply HD ].
      now apply Included_Union_l.
      rewrite <- Union_assoc. apply Included_Union_preserv_l.
      now apply name_in_fundefs_bound_var_fundefs.
    + rewrite !Setminus_Union...
  - rewrite !Setminus_Union_distr, Union_commut, <- Union_assoc.
    apply Same_set_Union_compat.
    + rewrite Setminus_Disjoint. reflexivity.
      apply Disjoint_sym. eapply Disjoint_Included; [| | now apply HD ].
      eauto with Ensembles_DB.
      apply Included_Union_preserv_r. do 2 apply Included_Union_preserv_l.
      now apply name_in_fundefs_bound_var_fundefs.
    + rewrite <- Union_assoc.
      apply Same_set_Union_compat. rewrite Setminus_Disjoint. reflexivity.
      eapply Disjoint_sym.
      eapply Disjoint_Included; [| | now apply HD ].
      eauto with Ensembles_DB.
      apply Included_Union_preserv_r. do 2 apply Included_Union_preserv_l.
      now apply name_in_fundefs_bound_var_fundefs.
      rewrite Union_commut, Union_assoc.
      apply Same_set_Union_compat; [ now apply Same_set_refl |].
      apply Setminus_Disjoint. eapply Disjoint_sym.
      eapply Disjoint_Included; [| | now apply HD ].
      eauto with Ensembles_DB. 
      apply Included_Union_preserv_r. do 2 apply Included_Union_preserv_l.
      now apply name_in_fundefs_bound_var_fundefs.
  - rewrite !Setminus_Union_distr.
    rewrite (Union_assoc (Singleton _ _) _), (Union_commut (Singleton _ _)), <- Union_assoc.
    apply Same_set_Union_compat; [| apply Same_set_Union_compat ].
    + apply Same_set_sym. apply Setminus_Disjoint. rewrite Hcl.
      now apply Disjoint_Empty_set_l. now constructor.
    + apply Setminus_Disjoint. eapply Disjoint_sym.
      eapply Disjoint_Included; [| | now apply HD ].
      now apply Included_Union_l.
      rewrite <- Union_assoc. apply Included_Union_preserv_l.
      now apply name_in_fundefs_bound_var_fundefs.
    + rewrite !Setminus_Union...
  - rewrite !Setminus_Union_distr, !Setminus_Union.
    rewrite !Union_assoc. eapply Same_set_Union_compat; sets.
    rewrite (Union_commut _ ([set f0] \\ _)). rewrite <- !Union_assoc.
    rewrite (Union_commut (FromList _) _).
    apply Same_set_Union_compat; [| apply Same_set_Union_compat ].
    + apply Setminus_Disjoint.
      eapply Disjoint_sym.
      eapply Disjoint_Included; [| | now apply HD ].
      now sets.
      do 2 apply Included_Union_preserv_l.
      now apply name_in_fundefs_bound_var_fundefs.
    + apply Same_set_sym. apply Setminus_Disjoint. rewrite Hcl.
      now apply Disjoint_Empty_set_l. now constructor.
    + apply Setminus_Disjoint. 
      eapply Disjoint_sym.
      eapply Disjoint_Included; [| | now apply HD ].
      now sets.
      do 2 apply Included_Union_preserv_l.
      now apply name_in_fundefs_bound_var_fundefs.
  - rewrite split_fds_occurs_free_fundefs; [| eassumption ].
    rewrite (split_fds_name_in_fundefs B B' B''); [| eassumption ].
    rewrite !Setminus_Union_distr, <- Union_assoc, Setminus_Union,
    (Union_commut (name_in_fundefs B)).
    apply Same_set_Union_compat; try now apply Same_set_Union_compat.
    apply Setminus_Disjoint. eapply Disjoint_sym.
    eapply Disjoint_Included; [| | now apply HD ].
    eauto with Ensembles_DB.
    apply Included_Union_preserv_r. apply Included_Union_preserv_l.
    now apply name_in_fundefs_bound_var_fundefs.
  - rewrite !Setminus_Union_distr.
    rewrite (Union_assoc (FromList _) _), (Union_commut (FromList _)), <- Union_assoc.
    apply Same_set_Union_compat; [| apply Same_set_Union_compat ].
    + apply Same_set_sym. apply Setminus_Disjoint. rewrite Hcl.
      now apply Disjoint_Empty_set_l. now constructor.
    + apply Setminus_Disjoint. eapply Disjoint_sym.
      eapply Disjoint_Included; [| | now apply HD ].
      now apply Included_Union_l.
      rewrite <- Union_assoc. apply Included_Union_preserv_l.
      now apply name_in_fundefs_bound_var_fundefs.
    + rewrite !Setminus_Union...
  - eauto with Ensembles_DB.
  - rewrite Hcl'; [| now constructor ]. rewrite Hcl; [| now constructor ].
    rewrite !Union_Empty_set_neut_l.  
    rewrite split_fds_name_in_fundefs with (B3 := B)  in *; try eassumption.
    rewrite split_fds_name_in_fundefs with (B3 := B2); try eassumption.
    rewrite split_fds_name_in_fundefs with (B3 := B4) in *; try eassumption.
    simpl in *. do 2 rewrite Union_Empty_set_neut_r at 1. 
    rewrite <- Setminus_Union.
    eapply Same_set_Setminus_compat; [| now apply Same_set_refl ].
    apply Setminus_Disjoint. eapply Disjoint_sym.
    eapply Disjoint_Included;
      [ now eapply occurs_free_Efun_Included with (B := B2)
      |  now apply Included_refl |].
    eapply Union_Disjoint_r.
    + eapply Disjoint_Included; [ now apply occurs_free_Efun | | now apply HD ].
      apply Included_Union_preserv_l.
      rewrite split_fds_bound_vars with (B3 := B2); try eassumption.
      rewrite bound_var_fundefs_Fcons, bound_var_Efun.
      do 3 apply Included_Union_preserv_r.
      do 2 apply Included_Union_preserv_l.
      now apply name_in_fundefs_bound_var_fundefs.
    + inv Hun.
      eapply split_fds_unique_bindings_fundefs_l in H5;
        [| eassumption ].
      edestruct H5 as [_ [H1' H2']].
      inv H1'. 
      rewrite split_fds_name_in_fundefs with (B3 := B2); try eassumption.
      simpl. rewrite Union_Empty_set_neut_r. eapply Union_Disjoint_r.
      apply Disjoint_sym. eapply Disjoint_Included; [| | now apply H2' ].
      rewrite bound_var_fundefs_Fcons, bound_var_Efun.
      do 2 apply Included_Union_preserv_r. do 2 apply Included_Union_preserv_l.
      now apply name_in_fundefs_bound_var_fundefs.
      now apply name_in_fundefs_bound_var_fundefs.
      eapply Disjoint_sym. eapply Disjoint_Singleton_l.
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
    + unfold closed_fundefs. rewrite occurs_free_fundefs_ctx_c.
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
    + rewrite occurs_free_exp_ctx.
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

Section hoisting_correct.

  Variable (pr : prims).
  Variable (cenv : ctor_env).

  Context (P : Post) (PG : PostG)
          (Hcompat : post_compat P P)
          (Happcompat : post_app_compat PG P)
          (Hletappcompat : post_letapp_compat PG P P)
          (Hrefl : post_refl P)
          (Hlocalstrong :
             forall (m : nat) (e1 e2 : exp) (rho rho' : env) (c1 c2 : nat),
               P c1 c2 -> PG m (e1, rho, c1) (e2, rho', c2)).
  
  Lemma hoist_rw_correct e e' rho rho' k :
    closed_fundefs_in_exp e ->
    unique_bindings e ->
    (Disjoint var (bound_var e) (occurs_free e)) ->
    hoist_rw e e' ->
    preord_env_P pr cenv (occurs_free e) k PG rho rho' ->
    preord_exp pr cenv k P PG (e, rho) (e', rho').
  Proof.
    intros Hclo Hun HD Hrw Henv; inv Hrw.
    - intros v1 c1 Hleq1 Hstep1.
      { inv Hstep1. inv H8; eauto.
        edestruct preord_env_P_get_list_l as [vs' [Hgetl Hpre]]; eauto.
        rewrite occurs_free_Econstr. now apply Included_Union_l. 
        edestruct (preord_exp_refl pr cenv P PG) with (k := k) (e := e0)
          as [v2 [c2 [Hstep2 [Hpost2 Hpre2]]]]; (try now eapply H4); eauto.
        - eapply preord_env_P_antimon.          
          eapply preord_env_set_def_funs_permut with (v2 := Vconstr t vs'); eauto.
          admit. admit. admit. admit. admit.
          + inv Hun. intros Hb. eapply H1. constructor; eauto.
          + rewrite preord_val_eq. split; eauto using Forall2_Forall2_asym_included.
          + eapply Included_trans. eapply occurs_free_Efun_Included with (B := B).
            rewrite Union_assoc. apply Included_Union_compat; eauto using Included_refl.
          eapply occurs_free_Econstr_Included.
        - omega. 
        - eexists; eexists (c2 + (1 + numOf_fundefs B + set_util.PS.cardinal (fundefs_fv B))
                            + 1 + Datatypes.length ys).
          repeat split; eauto. rewrite <- plus_assoc.
          rewrite (plus_comm _ (1 + _)). rewrite plus_assoc.
          econstructor. rewrite (plus_comm (_ c0)), plus_assoc. econstructor; eauto.
          eapply get_list_fundefs; eauto. 
          intros y Hin Hc. eapply HD.
          constructor. constructor 2. constructor.
          now apply name_in_fundefs_bound_var_fundefs; eauto.
          now constructor. eapply preord_val_monotonic. eassumption. omega. }
    -  intros v1 c1 Hleq1 Hstep1.
       { inv Hstep1.
         edestruct Henv as [v' [Hget Hpre]]; eauto.
         rewrite preord_val_eq in Hpre.
         destruct v'; try (now simpl in Hpre; contradiction). inv Hpre. 
         inv H4. 
         - edestruct (preord_exp_refl pr cenv) with (k :=k) (e := e) as [v2 [c2 [Hstep2 [Hcost2 Hpre2]]]];
           (try now eapply H7); eauto.
           + eapply preord_env_P_def_funs_not_in_P_r with (B := B).
             * eapply preord_env_P_antimon; eauto.
               eapply occurs_free_Ecase_Included.
               rewrite <- H3. now left.
             * eapply Disjoint_sym. eapply Disjoint_Included; eauto.
               eapply occurs_free_Ecase_Included. rewrite <- H3. now left.
               eapply Included_trans. apply name_in_fundefs_bound_var_fundefs.
               intros x' H'. 
               econstructor; [| eapply in_or_app; right; constructor; eauto ].
               constructor; eauto.
           + omega. 
           + eexists; exists (c2 + 1). eauto. constructor; eauto. econstructor; eauto.
             rewrite def_funs_neq; eauto. intros Hn.
             eapply HD. econstructor.
          simpl. econstructor; [| eapply in_or_app; right; constructor; eauto ].
          constructor. now apply name_in_fundefs_bound_var_fundefs; eauto.
          constructor.
             * eapply caseConsistent_same_ctor_tags; [| eassumption ].
               apply Forall2_app.
               now eapply Forall2_same. constructor. reflexivity.
               now eapply Forall2_same.
             * erewrite findtag_append_is_Some; eauto.
         - simpl in H5. destruct (M.elt_eq t c); subst.
           + inv H5. inv H7.
             edestruct (preord_exp_refl pr cenv k e'0) as [v2 [c2 [Hstep2 Hpre2]]];
               [| now eauto | now eauto |]. 
              eapply preord_env_P_def_funs_cor; eauto.
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
             eapply caseConsistent_same_ctor_tags; [| eassumption ].
             apply Forall2_app.
             now eapply Forall2_same. constructor. reflexivity.
             now eapply Forall2_same.
             erewrite findtag_append_not_In; eauto. simpl.
             rewrite peq_true. reflexivity.
           + edestruct (preord_exp_refl pr cenv k e) as [v2 [c2 [Hstep2 Hpre2]]];
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
               eapply caseConsistent_same_ctor_tags; [| eassumption ].
               apply Forall2_app.
               now eapply Forall2_same. constructor. reflexivity.
               now eapply Forall2_same.
               erewrite findtag_append_not_In; eauto. simpl.
               destruct (M.elt_eq t c); try congruence. }
       { inv Hstep1. inv H9; eauto.
         edestruct Henv as [vs' [Hgetl Hpre]]; eauto. rewrite preord_val_eq in Hpre.
         destruct vs'; try (simpl in Hpre; contradiction). inv Hpre.
         edestruct (@Forall2_asym_nthN val) as [v' [Hnth Hpre']]; eauto.
         edestruct (preord_exp_refl pr cenv k e0) as [v2 [c2 [Hstep2 Hpre2]]];
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
         edestruct (preord_exp_refl pr cenv k e0) as [v2 [c2 [Hstep2 Hpre2]]]; [| eauto | eauto |].
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
       { inv Hstep1. inv H10; eauto.
         edestruct preord_env_P_get_list_l as [vs' [Hgetl Hpre]]; eauto.
         rewrite occurs_free_Eprim. now apply Included_Union_l.
         edestruct Prim_axiom as [v' [Heq Hpre']]; eauto.
         edestruct (preord_exp_refl pr cenv k e0) as [v2 [c2 [Hstep2 Hpre2]]];
           [| eauto | eauto |].
         eapply preord_env_P_antimon.
         eapply preord_env_set_def_funs_permut; eauto.
         - inv Hun. intros Hb. eapply H1. constructor; eauto.
         - eapply Included_trans. eapply occurs_free_Efun_Included with (B := B).
           rewrite Union_assoc. apply Included_Union_compat; eauto using Included_refl.
           eapply occurs_free_Eprim_Included.
         - repeat eexists; eauto. constructor. econstructor; eauto.
           eapply get_list_fundefs; eauto. 
           intros y Hin Hc. eapply HD.
           constructor; [| now constructor; eauto ].
           constructor. constructor.
           now apply name_in_fundefs_bound_var_fundefs. }
       { inv Hstep1. simpl in H4.
         edestruct (preord_exp_refl pr cenv k e') as [v2 [c2 [Hstep2 Hpre2]]];
           [| eauto | eauto |].
         eapply preord_env_P_antimon; eauto.
         eapply Included_trans. eapply occurs_free_Efun_Included with (B := Fnil).
         simpl. rewrite Union_Empty_set_neut_r. apply Included_refl.
         repeat eexists; eauto. }
       { inv Hun. inv Hstep1. 
         edestruct preord_exp_refl with (e := e0) as [v2 [c2 [Hstep2 Hpre2]]]; eauto;
           [| exists v2, c2; repeat split; try constructor; eauto ].
         specialize (unique_bindings_hoist _ _ _ _ _ _ _ _ _ H H0 H1 H5); intros Hun.
         eapply preord_env_P_trans with (rho2 := def_funs B2 B2 rho' rho').
         + eapply preord_env_P_def_funs_cor.
           rewrite occurs_free_Efun in Henv. unfold closed_fundefs_in_exp, closed_fundefs in Hclo.
           now rewrite Union_commut.
         + clear Henv. intros m.
           eapply preord_env_P_trans.
           * eapply preord_env_P_Same_set_fun_in_fundefs
               with (B2 := Fcons f0 tau xs (Efun B3 e'0) B1)
                    (B2' := Fcons f0 tau xs (Efun B3 e'0) B1); eauto;
               solve
                 [ rewrite split_fds_fun_in_fundefs; eauto; simpl; eauto with Ensembles_DB
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
               do 3 apply Included_Union_preserv_r.
               apply Included_Union_preserv_l. now apply Included_refl.
               edestruct split_fds_unique_bindings_fundefs_l as [H1' [H2' H3']];
                 [| apply H1 |]; eauto.
               rewrite (split_fds_bound_vars B1 (Fcons f0 tau xs e'0 Fnil) B4) in H3' ; eauto.
               rewrite bound_var_fundefs_Fcons in H3'.
               apply Disjoint_sym. eapply Disjoint_Included; [ | | apply H3' ]; eauto.
               simpl. rewrite Union_commut.
               apply Included_Union_compat; eauto using Included_Union_l;
                 now apply name_in_fundefs_bound_var_fundefs.
               now apply name_in_fundefs_bound_var_fundefs.
               eapply preord_env_P_refl.
               eapply Included_trans. apply occurs_free_Efun_Included.
               eapply Included_Union_compat. apply Included_refl.
               rewrite split_fds_name_in_fundefs; eauto. simpl. rewrite Union_Empty_set_neut_r.
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
      + intros e1' e2' c H. eapply occurs_free_exp_ctx. eauto.
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
    preord_env_P pr cenv (occurs_free e) k rho rho' ->
    preord_exp pr cenv k (e, rho) (e', rho').
  Proof.
    intros Hclo Hun HD [n Hrw].
    revert k rho rho'. 
    eapply (relation_inclusion_refl_trans_strong (compat_closure hoist_rw)) with
    (Pre := fun e => closed_fundefs_in_exp e /\
                  unique_bindings e /\
                  (Disjoint var (bound_var e) (occurs_free e)))
      (R' := fun e e' : exp =>
               forall k rho rho',
                 preord_env_P pr cenv (occurs_free e) k rho rho' ->
                 preord_exp pr cenv k (e, rho) (e', rho')); eauto.
    - intros e1 e2 Hpre HR.
      eapply (relation_inclusion_compat_strong hoist_rw) with
      (Pre := fun e => closed_fundefs_in_exp e /\
                    unique_bindings e /\
                    Disjoint var (bound_var e) (occurs_free e))
        (R' := fun e e' : exp =>
                 forall k rho rho',
                   preord_env_P pr cenv (occurs_free e) k rho rho' ->
                   preord_exp pr cenv k (e, rho) (e', rho')); eauto.
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
    preord_env_P pr cenv (occurs_free e) k rho rho' ->
    preord_exp pr cenv k (e, rho) (exp_hoist e, rho').
  Proof.
    intros.
    eapply hoist_star_correct; try eassumption.
    now eapply exp_hoist_in_hoist_star.
  Qed.

End hoisting_correct.
*)

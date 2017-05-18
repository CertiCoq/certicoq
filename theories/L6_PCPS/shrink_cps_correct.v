Require Import Coq.Relations.Relations.
Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.Morphisms.
Import RelationClasses.


Require compcert.lib.Maps.
Require Import ExtLib.Data.Bool.
Require Coq.funind.Recdef.
Import Nnat.
Require Import Coq.Arith.Arith Coq.NArith.BinNat ExtLib.Data.String ExtLib.Data.List Coq.omega.Omega Coq.Program.Program Coq.micromega.Psatz Coq.Sets.Ensembles Coq.Logic.Decidable Coq.Lists.ListDec.
Require Import Libraries.CpdtTactics Coq.Sorting.Permutation.
Require Import Libraries.HashMap.
Require Import Libraries.maps_util.
Require Import compcert.lib.Coqlib L6.Ensembles_util. 
Require Import L6.cps.
Require Import L6.ctx L6.logical_relations.
Require Import L6.cps_util L6.List_util L6.shrink_cps L6.eval L6.set_util L6.identifiers L6.stemctx.

   Ltac pi0 :=
    repeat match goal with
             | [ H: _ + _ = 0 |- _ ] =>  apply plus_is_O in H; destruct H; subst; pi0
             | [ H: 0 = _ + _ |- _ ] => symmetry in H; pi0
             | [ H: (if cps_util.var_dec ?X ?Y then _ else _) = 0 |- _] => destruct (cps_util.var_dec X Y); try inversion H; pi0                | [ H: ?X <> ?X |- _] => exfalso; apply H; auto
           end.





Theorem find_def_rename: forall f t xs e sigma fds,
  find_def f fds = Some (t, xs, e) ->
  find_def f (rename_all_fun sigma fds) = Some (t, xs, rename_all (remove_all sigma xs) e).
Proof.
  induction fds; intros.
  - simpl in *.  destruct (M.elt_eq f v).
    + subst; inversion H; reflexivity.
    + apply IHfds; auto.
  -   inversion H.
Qed.


Theorem split_fds_nil:
  (forall fds fds',
     split_fds Fnil fds fds' -> fds = fds') /\
  (forall fds fds',
     split_fds fds Fnil fds' -> fds = fds').
Proof.
  split; induction fds; intros; inversion H; subst.
  erewrite IHfds; eauto.
  reflexivity.
  erewrite IHfds; eauto.
  reflexivity.
Qed.

     Inductive unique_name_fundefs: fundefs -> Prop :=
     | Uname_Fcons: forall f tau ys e defs,
                      ~ name_in_fundefs defs f ->
                      unique_name_fundefs defs ->
                      unique_name_fundefs (Fcons f tau ys e defs)
     | Uname_Fnil:
         unique_name_fundefs Fnil
     .


  (** general rewrite rules that preserves semantics
    - Fun_inline replaces one occurence on f by its definition
    - Fun_dead removes the definition of a set of functions if none of them occur free in the rest of the program
    - Fun_rm removes a function if it doesn't occur anywhere in its mutual bundle or in the rest of the term
    -  Constr_dead removes the binding of a datatype when it doesn't occur free in the rest of the program 
    -  Constr_proj replaces a binding by the nth projection of a datatype when the datatype is known (in ctx) 
    -  Constr_case reduces a pattern match into an application of the right continuation on the datatype when the datatype is known
*)
  Inductive rw: relation exp :=
  (* Rules about dead var elimination *)
| Constr_dead: forall x t ys e, 
                 ~ occurs_free e x ->
                 rw (Econstr x t ys e) e
| Prim_dead: forall x p ys e,
               ~ occurs_free e x ->
               rw (Eprim x p ys e) e
| Proj_dead: forall x t n y e,
               ~ occurs_free e x ->
               rw (Eproj x t n y e) e
| Fun_dead: forall e fds,
              Forall (fun v => ~ occurs_free e v) (all_fun_name fds) ->
              rw (Efun fds e) e 
| Fun_rem: forall f t xs fb B1 B2 e,
             unique_name_fundefs (fundefs_append B1 (Fcons f t xs fb B2)) ->
               num_occur (Efun (fundefs_append B1 (Fcons f t xs fb B2)) e) f 0 ->  
               rw (Efun (fundefs_append B1 (Fcons f t xs fb B2)) e) (Efun (fundefs_append B1 B2) e)

(* Rules about inlining/constant-folding *)
| Constr_case: forall x c cl co e ys,
    findtag cl co = Some e ->
    (* x isn't rebind on the way to the case statement *)
      ~bound_stem_ctx c x ->
      rw (Econstr x co ys (c |[ Ecase x cl ]|)) (Econstr x co ys (c |[e]|))

| Constr_proj: forall v  t t' n x e k ys c, 
                 (* nothing shadows constructor x or var k in c *)
                 ~ bound_stem_ctx c x ->
                 ~ bound_stem_ctx c k ->
                 (* nothing rebinds k in e *)
                 ~ bound_var e k ->
                 x <> k ->
                 v <> k ->
                 nthN ys n = Some k -> 
                 rw (Econstr x t ys (c |[Eproj v t' n x e]|)) (Econstr x t ys (c |[ rename k v e]|))
| Fun_inline: forall c  vs f  t xs fb  fds,
    find_def f fds = Some (t, xs, fb) ->
                (* nothing rebinds vs in \xs.fb *)
                Disjoint _ (Union _ (FromList xs) (bound_var fb)) (FromList vs) ->
                unique_name_fundefs fds ->
                (* nothing shadows the names and FV of fds in c *)
                Disjoint var (bound_stem_ctx c) (occurs_free_fundefs fds)  ->
                Disjoint var (bound_stem_ctx c) (name_in_fundefs fds)  -> 
                List.NoDup xs ->
                rw (Efun fds (c |[ Eapp f t vs ]|)) (Efun fds (c |[ (rename_all (set_list (combine xs vs) (M.empty var)) fb)]|))                     
.
         

Fixpoint collect_funvals (fds:fundefs)  : list (var * svalue) :=
  match fds with
    | Fnil => []
    | Fcons v t ys e fds' => ( v, (SVfun t ys e))::(collect_funvals fds')
  end.


Inductive gen_rw : relation exp :=
| Ctx_rw : forall c e e',
             rw e e' ->
             gen_rw (c |[ e ]|) (c |[ e' ]|)
.


Definition gr_clos := clos_refl_trans exp gen_rw.

Section Shrink_correct.

  Variable pr : prims.
  Variable cenv : cEnv.





Lemma preord_val_constr: forall k t vl x, 

  preord_val pr cenv k (cps.Vconstr t vl) x  ->
 exists vl',  x = cps.Vconstr t vl' /\ Forall2_asym (preord_val pr cenv k) vl vl'.
Proof.
  intros.
  eapply preord_val_eq in H.
  destruct x.
  simpl in H.
  destructAll.
  eauto.
  destruct H.
  destruct H.
Qed.



  
Lemma not_occur_list_not_in:
  forall v l,
    num_occur_list l v = 0 <-> ~ List.In  v l.
Proof.
  induction l; split; intros.
  - intro. inversion H0.
  - auto. 
  - intro. inversion H0.
    + subst. simpl in H.
      unfold cps_util.var_dec in *.
      destruct (M.elt_eq v v).
      inversion H.
      apply n; auto.
    + inversion H.
      apply IHl.
      destruct (cps_util.var_dec v a).
      inversion H3. auto.
      auto.
  - simpl.
    destruct (cps_util.var_dec v a).
    exfalso.
    apply H. constructor. auto.
    apply IHl.
    intro. apply H. constructor 2.
    auto.
Qed.    



Lemma not_occurs_not_free:
  forall v, (forall e,
  num_occur e v 0 -> 
  ~occurs_free e v )
  /\
  (forall f, num_occur_fds f v 0 ->
               ~ occurs_free_fundefs f v )
.
Proof.
  intro v. eapply (exp_def_mutual_ind (fun e =>
  num_occur e v 0 -> 
  ~occurs_free e v ) (fun f => num_occur_fds f v 0 ->
               ~ occurs_free_fundefs f v)); intros; intro; try (inversion H0; inversion H1; subst; pi0).
  - apply H; auto. 
     exfalso.
     revert H14.
     apply not_occur_list_not_in.
     auto.
  - apply H; auto.
  - inversion H; subst.
    destruct (cps_util.var_dec v v). inversion H6. apply n0; auto.
  - inversion H1; inversion H2; subst; pi0.
    inversion H6; subst; pi0.
    revert H13; apply H; auto.
    revert H13; apply H0; auto.
    replace 0 with (num_occur_list [v0] v + 0).
    constructor.
    inversion H6; pi0. auto.
    simpl. destruct (cps_util.var_dec v v0). exfalso; auto. auto.    
  - revert H17; apply H; auto.

  - inversion H1; inversion H2; subst; pi0.
    revert H13; apply H0; auto.
    revert H12; apply H; auto.
  - inversion H; inversion H0; subst.
    pi0. pi0.
  - inversion H; inversion H0; subst. pi0.
    revert H12; apply not_occur_list_not_in; auto.
    pi0.
    reflexivity.
  - revert H14; apply not_occur_list_not_in; auto.
  - revert H15; apply H; auto.
  - inversion H; pi0.
  - inversion H1; inversion H2; subst; pi0.
    + revert H21; apply H; auto.
    + revert H18; apply H0; auto.
Qed.



Lemma preord_env_P_set_not_in_P_l':
      forall (pr : prims) (cenv : cEnv) (x : var) (v : val) 
             (P : Ensemble var) (k : nat) (rho1 rho2 : env),
        preord_env_P pr cenv P k (M.set x v rho1) rho2 ->
        Disjoint var P (Singleton var x) ->
        preord_env_P pr cenv P k rho1 rho2.
Proof.
  intros; intro; intro; intro; intros.
  apply H. auto.
  rewrite M.gso; auto.
  intro.
  subst.
  inv H0.
  specialize (H3 x).
  apply H3. auto.
Qed.

Lemma preord_env_P_set_not_in_P_r':
      forall (pr : prims) (cenv : cEnv) (x : var) (v : val) 
             (P : Ensemble var) (k : nat) (rho1 rho2 : env),
        preord_env_P pr cenv P k rho1 (M.set x v rho2) ->
        Disjoint var P (Singleton var x) ->
        preord_env_P pr cenv P k rho1 rho2.
Proof.
  intros; intro; intro; intro; intros.
  apply H in H2; auto.
  destructAll. exists x1. split; auto.
  rewrite M.gso in H2; auto.
  intro.
  subst.
  inv H0.
  specialize (H4 x).
  apply H4. auto.
Qed.

Theorem preord_env_P_def_funs_not_in_P_l':
  forall (pr : prims) (cenv : cEnv) (B B' : fundefs) 
         (P : Ensemble var) (k : nat) (rho : M.t val) (rho1 rho2 : env),
    preord_env_P pr cenv P k (def_funs B' B rho rho1) rho2 ->
  Disjoint var P (name_in_fundefs B) ->
    preord_env_P pr cenv P k rho1 rho2. 
Proof.
  intros; intro; intro; intro; intros.
  apply H; auto.
  rewrite def_funs_neq; auto.
  inv H0.
  specialize (H3 x).
  intro. apply H3; auto.
Qed.  


  

  Lemma rm_set :
   forall k rho e m v,
  num_occur e v 0 ->
  preord_exp pr cenv k (e, (M.set v m rho)) (e, rho).
  Proof.
    intros; intro; intros.
    eapply preord_exp_refl in H1.
    destructAll. 
    exists x, x0.
    split; eauto.
    intro. intros. intro. intros.
    destruct (var_dec x v).    
    - subst. exfalso. revert H2; apply not_occurs_not_free. auto.
    - rewrite M.gso in H3 by auto.
      exists v0; split; auto.
      apply preord_val_refl.
    - auto.
  Qed.

    Corollary  rm_constr' :
   forall k rho rho' e' v t l,
     num_occur e' v 0 ->
  preord_env_P pr cenv (occurs_free e') k rho rho' ->
  preord_exp  pr cenv k (Econstr v t l e', rho) (e', rho').
  Proof.
    intros; intro; intros.
    inversion H2; subst.
    apply not_occurs_not_free in H.
    eapply preord_env_P_set_not_in_P_l in H0; eauto with Ensembles_DB.
    eapply preord_exp_refl in H12; eauto.
  Qed.

  

  Corollary  rm_constr :
   forall k rho rho' e' v t l,
     ~occurs_free e' v ->
  preord_env_P pr cenv (occurs_free (Econstr v t l e')) k rho rho' ->
  preord_exp  pr cenv k (Econstr v t l e', rho) (e', rho').
  Proof.
    intros; intro; intros.
    inversion H2; subst.
    rewrite occurs_free_Econstr in H0.
    assert (preord_env_P pr cenv
                         (occurs_free e') k rho rho').
    eapply preord_env_P_antimon.
    apply H0.
    right. split. auto. intro. inv H4. 
    apply H. auto.
    eapply preord_env_P_set_not_in_P_l in H3; eauto with Ensembles_DB.
    eapply preord_exp_refl in H12; eauto.
  Qed.

  Corollary rm_prim:
    forall k rho rho' e x p l,
      ~occurs_free e x ->
      preord_env_P pr cenv (occurs_free (Eprim x p l e)) k rho rho' ->
      preord_exp pr cenv k (Eprim x p l e, rho) (e, rho').
  Proof.
        intros; intro; intros.
    inversion H2; subst.
    rewrite occurs_free_Eprim in H0.
    assert (preord_env_P pr cenv
                         (occurs_free e) k rho rho').
    eapply preord_env_P_antimon.
    apply H0.
    right. split. auto. intro. inv H4. 
    apply H. auto.
    eapply preord_env_P_set_not_in_P_l in H3; eauto with Ensembles_DB.
    eapply preord_exp_refl in H14; eauto.
  Qed.


  Corollary rm_proj:
    forall k rho rho' e x t n y,
      ~occurs_free e x ->
      preord_env_P pr cenv (occurs_free (Eproj x t n y e)) k rho rho' ->
      preord_exp pr cenv k (Eproj x t n y e, rho) (e, rho').
  Proof.
            intros; intro; intros.
    inversion H2; subst.
    rewrite occurs_free_Eproj in H0.
    assert (preord_env_P pr cenv
                         (occurs_free e) k rho rho').
    eapply preord_env_P_antimon.
    apply H0.
    right. split. auto. intro. inv H4. 
    apply H. auto.
    eapply preord_env_P_set_not_in_P_l in H3; eauto with Ensembles_DB.
    eapply preord_exp_refl in H13; eauto.
  Qed.
  
  
  Theorem get_preord_env: forall rho rho' k,
    map_get_r _ rho rho' ->
    preord_env pr cenv k rho rho'.
  Proof.
    intros; intro; intros; intro; intros.
    rewrite H in H1.
    exists v1. split; auto.
    apply preord_val_refl.
  Qed.



  Definition fundefs_suffix fd fds:= (exists fd', fundefs_append fd' fd = fds). 

  Theorem fundefs_append_assoc: forall F1 F2 F3,
    fundefs_append F1 (fundefs_append F2 F3) =
    fundefs_append (fundefs_append F1 F2) F3.
  Proof.
    induction F1; intros.
    - simpl. rewrite IHF1. auto.
    -     simpl. reflexivity.
  Qed.

  
  Theorem fundefs_suffix_cons: forall v f l e fds fds', 
    fundefs_suffix (Fcons v f l e fds) fds' ->
    fundefs_suffix fds fds'.
  Proof.
    induction fds'; intros.
    - unfold fundefs_suffix in *. destructAll.
      destruct x.
      + inversion H; subst. exists ( Fcons v0 f0 l0 e0 (fundefs_append x (Fcons v f l e Fnil))).
        simpl.  rewrite <- fundefs_append_assoc. reflexivity.
      + inversion H; subst.
        exists (Fcons v0 f0 l0 e0 Fnil). auto.
    - unfold fundefs_suffix in H; destructAll.
      destruct x; inversion H.
  Qed.


  Lemma fundefs_suffix_in: forall v f l e fds fds', 
  fundefs_suffix (Fcons v f l e fds) fds' ->
  List.In v (all_fun_name fds'). 
  Proof.
    induction fds'.
    - intro. inversion H. destruct x.
      + inversion H0. assert (fundefs_suffix (Fcons v f l e fds) fds'). exists x. auto.
        apply IHfds' in H1. subst.
        simpl. right. auto.
      + inversion H0. simpl. left; reflexivity.
    - intro. inversion H. destruct x; inversion H0.
  Qed.


   Theorem forall_name_fundefs: forall x P fds,
     Forall P (all_fun_name fds) ->
     name_in_fundefs fds x ->
     P x.
   Proof.
     induction fds; intros.
     - inversion H0; inversion H; subst.
       + inversion H1; subst. auto.
       + apply IHfds; auto.
     - inversion H0.
   Qed.

   Theorem all_name_fundefs: forall fds x,
    List.In x (all_fun_name fds) <-> name_in_fundefs fds x.
   Proof.
     induction fds; simpl; intros; split; intros.
     - destruct H. subst. left; auto.
       right. apply IHfds; auto.
     - inversion H; subst. inversion H0; auto.
       right. apply IHfds; auto.
     - inversion H.
     - inversion H.
   Qed.

   
  Theorem disjoint_not_occurs_fun: forall e fds,
  Forall (fun v => num_occur e v 0) (all_fun_name fds) ->
  Disjoint var (occurs_free e) (name_in_fundefs fds).
  Proof.
    intros.
    apply Disjoint_intro; intros.
    intro.
    inversion H0; subst.
    assert (Hof := (not_occurs_not_free x)).
    destruct Hof.
    specialize (H3 e).
    apply H3; auto.
    rewrite Forall_forall in H.
    apply H.
    apply all_name_fundefs; auto.
  Qed.


    Theorem disjoint_occurs_free_fun: forall e fds,
  Forall (fun v => ~occurs_free e v) (all_fun_name fds) ->
  Disjoint var (occurs_free e) (name_in_fundefs fds).
  Proof.
    intros.
    apply Disjoint_intro; intros.
    intro.
    inversion H0; subst.
    rewrite Forall_forall in H.
    specialize (H x).
    apply H. 
    apply all_name_fundefs; auto. auto.
  Qed.


  Theorem in_fun_name_suffix: forall fds fds' x,
    List.In x (all_fun_name fds) ->
            fundefs_suffix fds fds' ->
    List.In x (all_fun_name fds').
  Proof.
    induction fds. intros.
    simpl in H. destruct H.
    subst.
    eapply fundefs_suffix_in. eauto.
    apply fundefs_suffix_cons in H0. apply IHfds; eauto.
    intros. inversion H.
  Qed.
    
    
  Theorem forall_all_fun_name_suffix: forall P fds fds',
    Forall P (all_fun_name fds') ->
  fundefs_suffix fds fds' ->
  Forall P (all_fun_name fds).
  Proof.
    intros; rewrite Forall_forall.
    rewrite Forall_forall in H.
    intros.
    apply H.
    eapply in_fun_name_suffix; eauto.
  Qed.

    
    (* corrolary of preord_env_P_def_funs_not_in_P_l *)
   Lemma rm_fundefs_env: forall fds' fds e  k rho,
    Forall (fun v => num_occur e v 0) (all_fun_name fds') ->
    fundefs_suffix fds fds' ->
    preord_env_P pr cenv (occurs_free e) k (def_funs fds' fds rho rho) rho. 
   Proof.
     intros.
     eapply preord_env_P_def_funs_not_in_P_l.
     apply preord_env_P_refl.
     apply disjoint_not_occurs_fun.
     eapply forall_all_fun_name_suffix; eauto.     
   Qed.

   (* corrolary of preord_env_P_def_funs_not_in_P_r *)
   Lemma rm_fundefs_env': forall fds' fds e  k rho,
    Forall (fun v => num_occur e v 0) (all_fun_name fds') ->
    fundefs_suffix fds fds' ->
    preord_env_P pr cenv (occurs_free e) k rho (def_funs fds' fds rho rho).  
   Proof.
     induction fds; intros.
     - assert (fundefs_suffix fds fds').
       unfold fundefs_suffix in *. destruct H0.
       exists (fundefs_append x (Fcons v f l e Fnil)).
       rewrite <- H0.
       rewrite <- fundefs_append_assoc.
       simpl. reflexivity.       
       specialize (IHfds _ k rho H H1). 
       simpl.
       apply preord_env_P_set_not_in_P_r.
       auto.
       split; intro; intro.
       inv H2. inv H4; subst. revert H3.
       apply not_occurs_not_free.
       rewrite Forall_forall in H.
       apply H.
       eapply fundefs_suffix_in. 
       eauto.
     -simpl. apply preord_env_P_refl.
   Qed.

   
   Lemma rm_fundefs_env_of: forall fds' fds e  k rho,
    Forall (fun v => ~occurs_free e v) (all_fun_name fds') ->
    fundefs_suffix fds fds' ->
    preord_env_P pr cenv (occurs_free e) k (def_funs fds' fds rho rho) rho. 
   Proof.
     intros.
     eapply preord_env_P_def_funs_not_in_P_l.
     apply preord_env_P_refl.
     apply disjoint_occurs_free_fun.
     eapply forall_all_fun_name_suffix in H; eauto.
   Qed.

   Lemma rm_fundefs_env_of': forall fds' fds e  k rho,
    Forall (fun v => ~occurs_free e v) (all_fun_name fds') ->
    fundefs_suffix fds fds' ->
    preord_env_P pr cenv (occurs_free e) k rho (def_funs fds' fds rho rho).  
   Proof.
     induction fds; intros.
     - assert (fundefs_suffix fds fds').
       unfold fundefs_suffix in *. destruct H0.
       exists (fundefs_append x (Fcons v f l e Fnil)).
       rewrite <- H0.
       rewrite <- fundefs_append_assoc.
       simpl. reflexivity.       
       specialize (IHfds _ k rho H H1). 
       simpl.
       apply preord_env_P_set_not_in_P_r.
       auto.
       split; intro; intro.
       inv H2. inv H4; subst. revert H3.
       rewrite Forall_forall in H.
       apply H.
       eapply fundefs_suffix_in. 
       eauto.
     -simpl. apply preord_env_P_refl.
   Qed.




     Theorem unique_bind_has_unique_name: forall fds,
       unique_bindings_fundefs fds -> unique_name_fundefs fds.
     Proof.
       induction fds; intros; auto.
       -        inversion H; subst.
                constructor. intro; apply H6.
                apply name_in_fundefs_bound_var_fundefs.
                auto.
                apply IHfds; auto.
       - constructor.
     Qed.

     Theorem split_fds_to_nil f1 f2:
       split_fds f1 f2 Fnil -> f1 = Fnil /\ f2 = Fnil.
     Proof.
       intros; destruct f1; destruct f2; inversion H. auto.
     Qed.


       
     Theorem split_fds_unique_name_l: forall fds,
                                     unique_name_fundefs fds ->
                                     forall fds' fds'',
                                       split_fds fds' fds'' fds ->
                                       unique_name_fundefs fds' /\ unique_name_fundefs fds'' /\
     Disjoint var (name_in_fundefs fds') (name_in_fundefs fds'').
     Proof.
       induction fds; intros.
       - inversion H; subst.
         specialize (IHfds H7).
         inversion H0; subst.         
         + specialize (IHfds _ _ H5).           
           destruct IHfds.
           split.
           constructor.
           intro; apply H3.
           eapply split_fds_name_in_fundefs; eauto.
           auto.  destruct H2. split; auto. simpl.
           apply Union_Disjoint_l.
           apply split_fds_name_in_fundefs in H5.
           split; intro. intro. apply H3.
           inv H6. inv H8.
           apply H5. auto.
           auto.
         + specialize (IHfds _ _ H5).
           destruct IHfds.
           destruct H2.
           split.  auto.
           split. 
           constructor.
           intro.
           apply H3.
           eapply split_fds_name_in_fundefs.
           eauto.
           right; auto.
           auto.
           simpl.
           apply Union_Disjoint_r.
           split; intro. intro. apply H3. inv H6.
           inv H9. eapply split_fds_name_in_fundefs.
           apply H5. auto.
           auto.
       - apply split_fds_to_nil in H0.
         destruct H0; subst.
         split; constructor.
         auto. simpl. auto with Ensembles_DB.
     Qed.

     Lemma split_fds_unique_name_fundefs_r B1 B2 B3 :
       unique_name_fundefs B1 -> unique_name_fundefs B2 ->
       Disjoint var (name_in_fundefs B1) (name_in_fundefs B2) ->
       split_fds B1 B2 B3 ->
       unique_name_fundefs B3.
     Proof with eauto with Ensembles_DB.
       intros Hun1 Hun2 HD Hspl. induction Hspl; simpl; repeat normalize_bound_var_in_ctx.
       - inv Hun1. constructor; eauto.                  
         + intros Hc.
           eapply split_fds_name_in_fundefs in Hc; [| eauto].
           inv Hc; auto.
           inv HD. specialize (H0 v). apply H0; split; auto.
           constructor. auto.
         + eapply IHHspl...
       - inv Hun2. constructor; eauto.
         + intros Hc.
           eapply split_fds_name_in_fundefs in Hc; [| eauto].
           inv Hc; auto.
           inv HD. specialize (H0 v). apply H0; split; auto.
           constructor. auto.
         + eapply IHHspl...
       - constructor.
     Qed.

     
     
     Lemma fundefs_append_unique_name_l B1 B2 B3 :
       unique_name_fundefs B3 ->
       fundefs_append B1 B2 = B3 ->
       unique_name_fundefs B1 /\
       unique_name_fundefs B2 /\
       Disjoint var (name_in_fundefs B1) (name_in_fundefs B2).
     Proof.
       intros. edestruct split_fds_unique_name_l; eauto.
       apply fundefs_append_split_fds; eauto.       
     Qed.


     Lemma fundefs_append_unique_name_r B1 B2 B3 :
       fundefs_append B1 B2 = B3 ->
       unique_name_fundefs B1 ->
       unique_name_fundefs B2  ->
       Disjoint var (name_in_fundefs B1) (name_in_fundefs B2) ->
       unique_name_fundefs B3.
     Proof.
       intros.
       eapply split_fds_unique_name_fundefs_r;
         [ apply H0 | | | ]; eauto.
       apply fundefs_append_split_fds; eauto.
     Qed.

     

     Theorem fundefs_swap_fun_order2: 
       forall k x y tx ty xs ys ex ey rho1  B B12 B11',
         x <> y -> 
         preord_env pr cenv k (def_funs B (fundefs_append B11' (Fcons x tx xs ex (Fcons y ty ys ey  B12))) rho1 rho1)
                              (def_funs B (fundefs_append B11' (Fcons y ty ys ey (Fcons  x tx xs ex B12))) rho1 rho1).
     Proof.
       induction B11'; intros.
       - simpl.
         apply preord_env_extend; auto.
         apply preord_val_refl.
       - simpl.
         intro. intro. intro. intro.
         rewrite set_permut in H1; auto. exists v1. split; auto.
         apply preord_val_refl.
     Qed.         


   Theorem  find_def_fundefs_append_none:
  forall (f : var) (B1 B2 : fundefs) (v : fTag * list var * exp),
    find_def f B1 = None -> find_def f (fundefs_append B1 B2) = find_def f B2.
   Proof.
     induction B1; intros.
     simpl in *.
     destruct (M.elt_eq f v); eauto. inv H.
     simpl. auto.
   Qed.     




   
(*
     Theorem fundefs_swap_val:
       forall k x y tx ty xs ys ex ey rho1  B12 B11' v,
         x <> y ->
         preord_val pr cenv k (Vfun rho1 (fundefs_append B11' (Fcons x tx xs ex (Fcons y ty ys ey B12))) v)
    (Vfun rho1 (fundefs_append B11' (Fcons y ty ys ey (Fcons x tx xs ex B12))) v).
     Proof.
       intros.
       apply preord_val_eq. intro. intros.
       assert ( find_def v (fundefs_append B11' (Fcons x tx xs ex (Fcons y ty ys ey B12))) =
                 find_def v (fundefs_append B11' (Fcons y ty ys ey (Fcons x tx xs ex B12)))).
       { destruct (find_def v B11') eqn:fd.
         erewrite find_def_fundefs_append_l; eauto.
         symmetry.
         erewrite find_def_fundefs_append_l; eauto.
         rewrite find_def_fundefs_append_none; auto.
         rewrite find_def_fundefs_append_none; auto.
         simpl. destruct (M.elt_eq v x); destruct (M.elt_eq v y); eauto.
         subst. exfalso. auto.
       }
       rewrite H3 in H1. exists xs1, e1.
       Admitted.
  *)       

     Theorem rm_fundefs_of': forall k rho e fds,
    Forall (fun v => ~occurs_free e v) (all_fun_name fds) ->
    preord_exp pr cenv k (Efun fds e, rho) (e, rho). 
  Proof.
    intros; intro; intros.
    inversion H1; subst.
    eapply preord_exp_refl in H7; eauto.
    eapply rm_fundefs_env_of.
    apply H. exists Fnil. simpl. auto.
  Qed.


  Theorem rm_fundefs_of: forall k rho rho' e fds,
    Forall (fun v => ~occurs_free e v) (all_fun_name fds) ->
    preord_env_P pr cenv (occurs_free (Efun fds e))  k rho rho' ->                     
    preord_exp pr cenv k (Efun fds e, rho) (e, rho'). 
  Proof.
    intros.    
    eapply preord_exp_trans_pre.
    Focus 2.
    apply preord_exp_refl.
    apply H0.
    intros. eapply preord_val_trans; eauto.
    intros. apply rm_fundefs_of'. auto.
  Qed.


  Theorem rm_fundefs': forall k rho e fds,
    Forall (fun v => num_occur e v 0) (all_fun_name fds) ->
    preord_exp pr cenv k (Efun fds e, rho) (e, rho). 
  Proof.
    intros; intro; intros.
    eapply Forall_impl in H.
    eapply rm_fundefs_of'; eauto.
    intros.
    simpl. apply not_occurs_not_free; auto.
  Qed.


  Theorem rm_fundefs: forall k rho rho' e fds,
    Forall (fun v => num_occur e v 0) (all_fun_name fds) ->
    preord_env_P pr cenv (occurs_free (Efun fds e))  k rho rho' ->                     
    preord_exp pr cenv k (Efun fds e, rho) (e, rho'). 
  Proof.
    intros.    
    eapply preord_exp_trans_pre.
    Focus 2.
    apply preord_exp_refl.
    apply H0.
    intros. eapply preord_val_trans; eauto.
    intros. apply rm_fundefs'. auto.
  Qed.

  




  Theorem preord_env_dead_fun: forall f t xs fb k fds' e rho1,
           ~(occurs_free (Efun fds' e)) f->
         ~ name_in_fundefs fds' f ->                  
         preord_env_P pr cenv (Union _ (occurs_free (Efun fds' e)) (name_in_fundefs fds')) k (def_funs (Fcons f t xs fb fds') (Fcons f t xs fb fds') rho1 rho1) (def_funs fds' fds' rho1 rho1).
  Proof.
    induction k as [ k IH' ] using lt_wf_rec1.
    intros. simpl. intro. intros.
    assert (Hxf: x <> f).
    {
      intro; subst.
      inv H1; auto.
    }
    intro. intros. rewrite M.gso in H2; auto.
    apply Union_Setminus in H1.
    inv H1.
    - inv H3.  rewrite def_funs_neq; auto.
      rewrite def_funs_neq in H2; auto.
      exists v1; split; auto.
      apply preord_val_refl.
    - erewrite def_funs_eq in H2; auto.
      inv H2.
      erewrite def_funs_eq; auto.
      exists  (Vfun rho1 fds' x).
      split; auto.
      rewrite preord_val_eq. intro. intros.
      assert (fundefs_append Fnil (Fcons f t xs fb fds') = (Fcons f t xs fb fds')) by auto.
      rewrite <- H5 in H2.
      rewrite find_def_fundefs_append_Fcons_neq in H2; auto. simpl in H2. 
      clear H5.
      symmetry in H4.
      assert (Hsl:= setlist_length _ (def_funs fds' fds' rho1 rho1) _ _ _  _ H1 H4).
      destruct Hsl.
      exists xs1, e1, x0.
      split; auto. split; auto.
      intros.
      eapply preord_exp_refl.      
      eapply preord_env_P_setlist_l; eauto.  intros.
      apply find_def_correct in H2.
      eapply occurs_free_in_fun in H9; eauto.
      inv H9.
      exfalso; apply H8; auto.
      inv H10.
      right; auto.
      left.
      rewrite occurs_free_Efun. left.
      auto.
    - apply Decidable_name_in_fundefs.
  Qed.

  Theorem find_def_append_not_cons:
    forall B2 f t xs fb x B1, 
    x <> f ->
    find_def x (fundefs_append B1 (Fcons f t xs fb B2)) = find_def x (fundefs_append B1 B2). 
  Proof.
    induction B1; intros.
    - simpl. destruct (M.elt_eq x v); auto.
    - simpl. destruct (M.elt_eq x f).
      exfalso; auto.
      auto.
  Qed.

  (* adapted from identifiers.fun_in_fundefs_unique_fundefs_split *)
Lemma fun_in_fundefs_unique_name_split f tau xs e B :
  fun_in_fundefs B (f, tau, xs, e) ->
  unique_name_fundefs B ->
  exists B1 B2,
    B = fundefs_append B1 (Fcons f tau xs e B2) /\
    ~ name_in_fundefs B1 f /\
    Same_set _ (Union _ (fun_in_fundefs B1) (fun_in_fundefs B2))
             (Setminus _ (fun_in_fundefs B) (Singleton _ (f, tau, xs, e))) /\
    unique_name_fundefs (fundefs_append B1 B2).
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
        inv Hun; auto.
      * exfalso. inv Hun. apply H2. eapply fun_in_fundefs_name_in_fundefs. eauto. 
    + inv H. inv H0. congruence. inv Hun; eauto.
      edestruct IHB as [B1 [B2 [Heq [Hn [Hs Hun']]]]]; eauto.
      edestruct fundefs_append_unique_name_l as [H1 [H2s H3]];
        [ apply Hun' | | ]; eauto.
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
        eapply Disjoint_Singleton_r. intros Hc. 
        apply Hn.
        eapply fun_in_fundefs_name_in_fundefs; eauto.
        eapply Disjoint_Singleton_r. intro.
        assert (In _ (Union (var * fTag * list var * exp) (fun_in_fundefs B1) (fun_in_fundefs B2)) (f, tau, xs, e)). right; auto. rewrite Hs in H4. inv H4. apply H7. auto.
      * simpl. constructor; eauto.
        intros H. apply H2.
        eapply fundefs_append_name_in_fundefs.
        symmetry. apply Heq.
        eapply fundefs_append_name_in_fundefs in H; [|reflexivity].
        inv H; auto.
        right. constructor 2. auto.
  - inv H.
Qed.

Lemma find_def_Included_name_in_fundefs f B B' :
  unique_name_fundefs B ->
  unique_name_fundefs B' ->
  Included _ (fun_in_fundefs B) (fun_in_fundefs B') ->
  name_in_fundefs B f ->
  find_def f B = find_def f B'.
Proof with eauto with Ensembles_DB.
  revert B'. induction B; simpl; intros B' Hun Hun' H Hn.
  - edestruct fun_in_fundefs_unique_name_split
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
      eapply Disjoint_Singleton_r. inv Hun; eauto. intros Hc. apply H2.
      now eapply fun_in_fundefs_name_in_fundefs; eauto.
      inv Hn. inv H0; try congruence. eauto.
  - destruct B'; eauto. inv Hn.
Qed.


Lemma find_def_Same_set_name_in_fundefs f B B' :
  unique_name_fundefs B ->
  unique_name_fundefs B' ->
  Same_set _ (fun_in_fundefs B) (fun_in_fundefs B') ->
  find_def f B = find_def f B'.
Proof.
  intros Hun1 Hun2 HS.
  destruct (@Dec _ _ (Decidable_name_in_fundefs B) f).
  - inv HS. eapply find_def_Included_name_in_fundefs; eauto.
  - rewrite !name_not_in_fundefs_find_def_None; eauto.
    intros Hn. apply H.
    apply name_in_fundefs_big_cup_fun_in_fundefs in Hn.
    destruct Hn as [[[[f' t] xs] e] [H1 H2]]. inv H2.
    eapply fun_in_fundefs_name_in_fundefs. now eapply HS; eauto.
Qed.

(* stronger version of preord_env_P_Same_set_fun_in_fundefs *)
    Lemma preord_env_P_Same_set_name_in_fundefs k S1 B1 B1' B2 B2' rho1 rho1' :
    Same_set _ (fun_in_fundefs B1) (fun_in_fundefs B2) ->
    Same_set _ (fun_in_fundefs B1') (fun_in_fundefs B2') ->
    unique_name_fundefs B1'->
    unique_name_fundefs B1 ->
    unique_name_fundefs B2'->
    unique_name_fundefs B2 ->
    preord_env_P pr cenv S1 k (def_funs B1' B1 rho1 rho1') (def_funs B2' B2 rho1 rho1').
  Proof. 
    revert B1 S1 B1' B2 B2' rho1 rho1'. induction k using lt_wf_rec1.
    induction B1; intros S1 B1' B2 B2' rho1 rho1' HS1 HS2 Hun1' Hun1 Hun2' Hun2.    
    - edestruct fun_in_fundefs_unique_name_split
      with (B := B2) as [B [B' [Heq [Hn [HS Hun']]]]]; eauto.
      eapply HS1. left. eauto.
      edestruct fundefs_append_unique_name_l as [H1 [H2 H3]]; eauto.
      rewrite Heq. 
      eapply preord_env_P_antimon;
        [| apply (@Included_Union_Setminus _ _ (Singleton var v) _)].
      eapply preord_env_P_union.
      + simpl. eapply preord_env_P_set_not_in_P_l;
          eauto using Disjoint_Setminus_l, Included_refl.
        eapply preord_env_P_trans;
          [| intros m; apply proerd_env_P_def_funs_weakening; intros Hc; inv Hc; eauto ].
        eapply IHB1; eauto ; try (now inv Hun1; eauto).
        rewrite (fundefs_append_fun_in_fundefs B B' (fundefs_append B B')); eauto.
        rewrite HS, <- HS1. eauto with Ensembles_DB. simpl.
        rewrite Setminus_Union_distr, Setminus_Same_set_Empty_set, Union_Empty_set_neut_l.
        inv Hun1. rewrite Setminus_Disjoint; eauto with Ensembles_DB.
        eapply Disjoint_Singleton_r.
        intros Hc. apply H5.
        eapply fun_in_fundefs_name_in_fundefs; eauto.
      + rewrite def_funs_append;
        eapply preord_env_P_def_funs_not_in_P_r.
        * simpl. eapply preord_env_P_extend.
          rewrite Setminus_Same_set_Empty_set. apply preord_env_Empty_set.
          rewrite preord_val_eq. intros vs1 vs2 j t1 xs1 e1 rho1'' Hlen Hf Hs. 
          edestruct (@setlist_length val) as [rho2'' Hs']; [eauto | | ]. eauto.
          exists xs1, e1, rho2''. repeat split; eauto.
          erewrite <- find_def_Same_set_name_in_fundefs; eauto.
          intros Hleq Hpre'. eapply preord_exp_refl; eauto.
          eapply preord_env_P_setlist_l; [| | | eauto | eauto ]; eauto.
        * eauto with Ensembles_DB.
    - simpl. destruct B2; eauto using preord_env_P_refl.
      destruct HS1 as [_ H1]. exfalso. eapply not_In_Empty_set. eapply H1.
      simpl. eauto.
  Qed.



  (*
  Theorem preord_env_dead_fun_of: forall f t xs fb   B1' k B1 B2 e rho1,
      ~occurs_free (Efun (fundefs_append B1 B2) e) f->
      ~ name_in_fundefs (fundefs_append B1 B2) f ->
      fundefs_suffix B1' B1 ->
      preord_env_P pr cenv (Union _ (occurs_free (Efun (fundefs_append B1 B2) e)) (name_in_fundefs (fundefs_append B1 B2))) k (def_funs (fundefs_append B1 (Fcons f t xs fb B2)) (fundefs_append B1' (Fcons f t xs fb B2)) rho1 rho1) (def_funs (fundefs_append B1 B2) (fundefs_append B1' B2) rho1 rho1).
      Proof.
      induction B1'; intros.
      - simpl.
        eapply preord_env_P_extend.
        eapply preord_env_P_antimon.
        apply IHB1'; eauto.
        inv H1.
        exists (fundefs_append x (Fcons v f0 l e Fnil)).
        rewrite <- fundefs_append_assoc. simpl. auto.
        eauto with Ensembles_DB.
        
        admit.
        
      - simpl. eapply preord_env_P_set_not_in_P_l; eauto.
        Focus 2. eauto with Ensembles_DB.
         admit.
  Admitted.
*)
        (*
  
    Lemma preord_env_dead_rm_fun_df: forall f t xs fb  k B1 B2 e B rho1 rho2,
         ~occurs_free (Efun (fundefs_append B1 B2) e) f->
         ~ name_in_fundefs (fundefs_append B1 B2) f ->
         ~ name_in_fundefs B f ->
         preord_env_P pr cenv (Union _ (occurs_free (Efun (fundefs_append B1 B2) e)) (name_in_fundefs (fundefs_append B1 B2))) k rho1 rho2 ->
         preord_env_P pr cenv (Union _ (occurs_free (Efun (fundefs_append B1 B2) e)) (name_in_fundefs (fundefs_append B1 B2))) k (def_funs (fundefs_append B1 (Fcons f t xs fb B2)) B rho1 rho1) (def_funs (fundefs_append B1 B2) B rho2 rho2).
    Proof.
      induction B; intros.      
      - simpl.  apply preord_env_P_extend.
        + eapply preord_env_P_antimon.
          apply IHB; eauto. intro; apply H1. constructor 2. auto.
          eauto with Ensembles_DB.
        + apply preord_val_eq.
          intro; intros.           
          exists xs1, e1.
          rewrite find_def_append_not_cons in H4.
          assert (exists rho2', 
    setlist xs1 vs2
            (def_funs (fundefs_append B1 B2) (fundefs_append B1 B2) rho2 rho2) = Some rho2').
          eapply setlist_length. Focus 2. symmetry. apply H5. auto.
          destruct H6. exists x. split; auto. split; auto. intros.
          Focus 2. intro; apply H1. constructor. subst. constructor.
          apply preord_exp_refl.
          eapply preord_env_P_setlist_l; eauto.
          
          admit.
      - simpl. apply H2.
Admitted.      *)

      (*
    Theorem preord_env_dead_fun_of: forall f t xs fb  B1 B2 e B1' k rho1,
         ~occurs_free (Efun (fundefs_append B1 B2) e) f->
         ~ name_in_fundefs (fundefs_append B1 B2) f ->
         fundefs_suffix B1' B1 ->
         preord_env_P pr cenv (Union _ (occurs_free (Efun (fundefs_append B1 B2) e)) (name_in_fundefs (fundefs_append B1 B2))) k (def_funs (fundefs_append B1 (Fcons f t xs fb B2)) (fundefs_append B1' (Fcons f t xs fb B2)) rho1 rho1) (def_funs (fundefs_append B1 B2) (fundefs_append B1' B2) rho1 rho1).
    Proof.
      intros. 
      do 2 (rewrite def_funs_append).   simpl. SearchAbout def_funs. 
       induction B1'. 
      - simpl.

        intros; intro; intros.
        assert (Hxf: x <> f).
        {
          intro; subst.
          inv H2.
          auto.
          auto.
        }
        simpl.
        apply preord_var_env_extend.
        apply IHB1'. inv H1.
        exists (fundefs_append x0 (Fcons v f0 l e0 Fnil)).
        rewrite <- fundefs_append_assoc. simpl. auto.
        auto.
        apply preord_val_eq.
          intro; intros.           
          exists xs1, e1.
          rewrite find_def_append_not_cons in H4.
          assert (exists rho2', 
                    setlist xs1 vs2
            (def_funs (fundefs_append B1 B2) (fundefs_append B1 B2) rho1 rho1) = Some rho2').
          eapply setlist_length. Focus 2. symmetry. apply H5. auto.
          destruct H6. exists x0. split; auto. split; auto. intros.
          Focus 2. intro; subst. apply H0.
          inv H1.
          eapply fundefs_append_name_in_fundefs. reflexivity.
          left.
          eapply fundefs_append_name_in_fundefs.  reflexivity. right. constructor. auto.
          eapply preord_exp_refl. SearchAbout preord_env_P setlist.
          eapply preord_env_P_setlist_l; eauto.
          
      - intros.
        simpl.
        apply preord_env_P_set_not_in_P_l.
        
        admit.
        eauto with Ensembles_DB.
      
    
    
    intro. intros. rewrite M.gso in H2; auto.
    apply Union_Setminus in H1.
    inv H1.
    - inv H3.  rewrite def_funs_neq; auto.
      rewrite def_funs_neq in H2; auto.
      exists v1; split; auto.
      apply preord_val_refl.
    - erewrite def_funs_eq in H2; auto.
      inv H2.
      erewrite def_funs_eq; auto.
      exists  (Vfun rho1 fds' x).
      split; auto.
      rewrite preord_val_eq. intro. intros.
      assert (fundefs_append Fnil (Fcons f t xs fb fds') = (Fcons f t xs fb fds')) by auto.
      rewrite <- H5 in H2.
      rewrite find_def_fundefs_append_Fcons_neq in H2; auto. simpl in H2. 
      clear H5.
      symmetry in H4.
      assert (Hsl:= setlist_length _ (def_funs fds' fds' rho1 rho1) _ _ _  _ H1 H4).
      destruct Hsl.
      exists xs1, e1, x0.
      split; auto. split; auto.
      intros.
      eapply preord_exp_refl.      
      eapply preord_env_P_setlist_l; eauto.  intros.
      apply find_def_correct in H2.
      eapply occurs_free_in_fun in H9; eauto.
      inv H9.
      exfalso; apply H8; auto.
      inv H10.
      right; auto.
      left.
      rewrite occurs_free_Efun. left.
      auto.
    - apply Decidable_name_in_fundefs.
  Qed.

  *)


  Theorem rm1_fundefs: forall k rho1 rho2 fb e fds xs t f ,
                         ~ (name_in_fundefs fds f) -> 
                         num_occur (Efun (Fcons f t xs fb fds) e) f 0 -> 
                         preord_env_P pr cenv (occurs_free (Efun (Fcons f t xs fb fds) e)) k rho1 rho2 -> 
                         preord_exp pr cenv k (Efun (Fcons f t xs fb fds) e, rho1) ((Efun fds e), rho2).
  Proof.
    intros k rho1 rho2 fb e fds xs t f Hub H H0.
    eapply preord_exp_trans.
    - eapply preord_exp_refl.
    apply H0.
    - 
      intros; intro; intros. clear H0.
      inv H2.
      eapply preord_exp_refl in H7. Focus 2.
      eapply preord_env_P_antimon.
      apply preord_env_dead_fun with (e := e). 
      inv H; subst. apply plus_is_O in H3. destruct H3; subst.
      apply not_occurs_not_free. rewrite <- plus_0_r.
      constructor. auto. inv H6; pi0; auto.
      auto.
      rewrite occurs_free_Efun.
      intro. intro.
      assert (Hv := Decidable_name_in_fundefs fds).
      inv Hv. specialize (Dec x).
      destruct Dec. right; auto.
      left. right. split; auto.
      destructAll.
      exists x, x0.
      split; eauto.
      constructor. auto.
      auto.
  Qed.


      Lemma split_fds_unique_bindings_lr:
        forall B1 B11 B12 B2 ,
        unique_bindings_fundefs B1 ->
        split_fds B11 B12 B1 ->
        split_fds B11 B12 B2 ->
        unique_bindings_fundefs B2.
      Proof.
        intros.
        assert (HB1112 := split_fds_unique_bindings_fundefs_l _ _ _ H H0).
        destructAll.
        eapply split_fds_unique_bindings_fundefs_r.
        apply H2. apply H3. apply H4. auto.
      Qed.        

      Theorem fundefs_append_num_occur:
        forall B1 B2 B,
          fundefs_append B1 B2 = B ->
          forall x n m,
            num_occur_fds B1 x n ->
            num_occur_fds B2 x m ->
        num_occur_fds B x (n+m).
      Proof.
        induction B1; intros.
        - simpl in H. destruct B. inversion H.
          specialize (IHB1 _ _ H7).
          subst.
          inv H0.
          specialize (IHB1 _ _ _ H10 H1).
          replace (n0 + m0 + m) with (n0 + (m0 + m)) by omega.
          constructor; auto.
          inv H.
        - simpl in H. inv H0. auto.
      Qed.

      Theorem fundefs_append_num_occur':
        forall B1 B2 nm x,
          num_occur_fds (fundefs_append B1 B2) x nm ->
          exists n m,
            num_occur_fds B1 x n /\ num_occur_fds B2 x m /\ n + m = nm.
      Proof.
        induction B1; intros.
        - simpl in H. inv H.
          apply IHB1 in H8. destructAll. exists (n + x0), x1. split.
          constructor; auto. split; auto. omega.
        -         simpl in H. exists 0, nm. split; auto. constructor.
      Qed.

  Theorem rm_any_fundefs: forall k rho1 rho2 fb e B1 B2 B xs t f ,
                            unique_name_fundefs B ->
                            fundefs_append B1 (Fcons f t xs fb B2) = B ->
                            num_occur (Efun B e) f 0 -> 
                         preord_env_P pr cenv (occurs_free (Efun B e)) k rho1 rho2 -> 
                         preord_exp pr cenv k (Efun B e, rho1) ((Efun (fundefs_append B1 B2) e), rho2).
  Proof.
    intros; subst.
    assert (Same_set (var * fTag * list var * exp)
                     (fun_in_fundefs (fundefs_append B1 (Fcons f t xs fb B2)))
                     (fun_in_fundefs (fundefs_append (Fcons f t xs fb B1) B2))).
    {    rewrite fundefs_append_fun_in_fundefs.
         Focus 2. reflexivity. symmetry. rewrite fundefs_append_fun_in_fundefs.
         Focus 2. reflexivity. simpl. eauto with Ensembles_DB.
    }
    assert (Hub : unique_name_fundefs (fundefs_append (Fcons f t xs fb B1) B2)). {
      eapply fundefs_append_unique_name_l in H. 2: reflexivity.
      destructAll. inv H3. simpl. constructor; auto.
      intro. eapply fundefs_append_name_in_fundefs in H3; [| reflexivity]. inv H3; auto.
      inv H4. specialize (H3 f). apply H3. split; auto.
      constructor. auto.
      eapply fundefs_append_unique_name_r.
      reflexivity.
      auto.
      auto.
      eauto with Ensembles_DB.
    }    
    eapply preord_exp_trans.
    apply preord_exp_refl. apply H2.
    intros.
    eapply preord_exp_trans.
    -   intro. intros.
      inv H4. eapply preord_exp_refl in H10.
      Focus 2.
      
      eapply preord_env_P_Same_set_name_in_fundefs.
      apply H0.
      apply H0.
      auto. auto.
      auto.
      auto.
      destructAll.
      exists x, x0.
      split.
      constructor; eauto.
      apply H5. auto.
    - intros. intro. intros.
      inv H4.
      eapply preord_exp_refl in H10. Focus 2.
      eapply preord_env_P_antimon.
      apply preord_env_dead_fun with (e := e).
      inv H1. apply plus_is_O in H6. destruct H6; subst.
      apply fundefs_append_num_occur' in H9. destructAll.
      inv H4. apply plus_is_O in H5. destruct H5.
      apply plus_is_O in H5. destruct H5; subst.
      apply not_occurs_not_free.
      rewrite <- plus_0_l. constructor; auto.
      rewrite <-plus_0_l.
      eapply fundefs_append_num_occur. reflexivity.
      auto. auto.
      simpl in Hub. inv Hub. auto.
      rewrite occurs_free_Efun. 
      intro. intros.
      assert (Hv := Decidable_name_in_fundefs (fundefs_append B1 B2)).
      inv Hv. specialize (Dec x).
      destruct Dec. right; auto.
      left. right. split; auto.
      destructAll.
      exists x, x0.
      split; eauto.
      constructor. auto.
      auto.
Qed.
      
  
  Theorem proper_getlist: forall A rho rho',
    map_get_r A rho rho' ->
    forall vs, getlist vs rho = getlist vs rho'.
  Proof.
    intros A rho rho' Hp.
    induction vs; auto.
    simpl. rewrite IHvs. rewrite Hp. reflexivity.
  Qed.

  Definition context_size (rho:env) := 1.

  Definition measure_map: forall A, (A -> nat) -> M.t A -> nat :=
    fun A f rho => 
      M.fold1 (fun n a => n + (f a)) rho 0.
 


    

    
  Theorem exp_case_equiv: forall (vs:list val) e rho k cl (x :var) t,
                            M.get x rho = Some (Vconstr t vs) ->
                            findtag cl t = Some e -> 
                            preord_exp pr cenv k (Ecase x cl, rho) (e, rho).
  Proof.  
    intros; intro; intros.
    inversion H2; subst.
    rewrite H in H5. inversion H5; subst.
    rewrite H8 in H0. inversion H0; subst. eexists; eexists. split; eauto. apply preord_val_refl.
  Qed.


Theorem caseConsistent_app: forall cenv t0 l0 l,
  caseConsistent cenv (l ++ l0) t0 ->
  caseConsistent cenv l t0 /\ caseConsistent cenv l0 t0.
Proof.
  induction l; intros.
  split. apply CCnil.
  simpl in H. auto.
  inversion H; subst.
  apply IHl in H6.
  destruct H6.
  split; auto.
  eapply CCcons; eauto.
Qed.  


Theorem findtag_app_in: forall l0 t (e:exp) l,
   List.In (t, e) l ->
   findtag (l++l0) t = Some e ->
   findtag l t = Some e.
Proof.
  induction l; intros.
  inversion H.
  simpl in H0. destruct a. simpl. destruct (M.elt_eq c t).
  auto. apply IHl; auto. inversion H.
  inversion H1; exfalso; auto.
  auto.
Qed.

Theorem preord_env_exchange: forall x y k v1 v2 v3 v4 rho1 rho2,
  x <> y ->
  preord_env pr cenv k (M.set x v1 (M.set y v2 rho1)) (M.set x v3 (M.set y v4 rho2)) ->
  preord_env pr cenv k (M.set y v2 (M.set x v1 rho1)) (M.set y v4 (M.set x v3 rho2)).  
Proof.
  intros; intro; intros.
  intro. intros. rewrite set_permut in H2; auto.  apply H0 in H2. destruct H2. rewrite set_permut in H2; auto. exists x1; auto. auto.
Qed.




Theorem get_fundefs_ctx :
forall e (y : M.elt) (v : val) B (B' : fundefs) (rho : M.t val),
M.get y rho = Some v ->
~ bound_var_fundefs_ctx B y -> M.get y (def_funs B' (B<[e]>) rho rho) = Some v.
Proof.
  induction B; intros.
  - simpl. assert (y <> v0).
    intro; apply H0; subst; constructor.
    rewrite M.gso; auto.
    eapply get_fundefs; auto.
    intro; apply H0.
    constructor 4.
    apply name_in_fundefs_bound_var_fundefs.
    apply H2.
  - assert (y <> v0).
    intro; apply H0; subst; constructor.
    simpl. rewrite M.gso; auto.
Qed.
    
    

Theorem bv_in_find_def: forall x f t1 xs1 c B, 
  find_def f B = Some (t1, xs1, c) ->
  bound_var c x -> bound_var_fundefs B x.
Proof.
  induction B; intros.
  - simpl in H. destruct (M.elt_eq f v).
    + inversion H; subst. constructor 3. auto.
    + apply IHB in H; eauto.
  - inversion H.
Qed.

Theorem bv_in_find_def_ctx: forall x f t1 e xs1 c B, 
  find_def f B = Some (t1, xs1, c |[ e ]|) ->
  bound_var_ctx c x -> bound_var_fundefs B x.
Proof.
  induction B; intros.
  - simpl in H. destruct (M.elt_eq f v).
    + inversion H; subst. constructor 3.  apply bound_var_app_ctx. left. assumption.
    + apply IHB in H; eauto.
  - inversion H.
Qed.



Fixpoint ctx_size (c:exp_ctx): nat :=
  match c with
    | Hole_c => 0
    | Econstr_c v t vs c' => 1 + ctx_size c'
    | Eproj_c v t i r c' => 1 + ctx_size c'
    | Eprim_c v p vs c' => 1 + ctx_size c'
    | Ecase_c v l t c' l0 => 1 + fold_right
                                    (fun (p : cTag * exp) (n : nat) => let (_, e1) := p in n + term_size e1)
                                    0 (l ++ l0) + ctx_size c'
                                   
    | Efun1_c fds c' => 1 + ctx_size c' + funs_size fds
    | Efun2_c cfds e => 1 + fundefs_ctx_size cfds + term_size e
  end
with fundefs_ctx_size (cfds:fundefs_ctx): nat :=
       match cfds with
         | Fcons1_c v t ys c fds => 1 + ctx_size c + funs_size fds
         | Fcons2_c v t ys e cfds => 1 + term_size e + fundefs_ctx_size cfds
       end.



  
Theorem app_ctx_size: (forall c e,
                        term_size (c |[e]|) = ctx_size c + term_size e) /\
                        (forall cfds e,
                        funs_size (cfds <[ e ]>) = fundefs_ctx_size cfds + term_size e).
Proof.
  exp_fundefs_ctx_induction IHe IHf; intros; auto; try (simpl; rewrite IHe; reflexivity).
  - simpl.
    apply eq_S.
    induction l. simpl. rewrite IHe. omega.
    simpl. destruct a.
    rewrite IHl. omega.
  - simpl. rewrite IHe. omega.
  - simpl. rewrite IHf. omega.
  - simpl. rewrite IHe. omega.
  - simpl. rewrite IHf. omega.    
Qed.




Theorem ctx_circular: forall c e,
                        c |[e]|  = e  ->
                                  c = Hole_c. 
Proof.   
  intros.
  assert (term_size(c |[e]|) = ctx_size c + term_size e) by apply app_ctx_size.
  rewrite H in H0.
  destruct c; auto; exfalso; simpl in H0; omega.
Qed.



  

Theorem bv_in_ctx: (forall c e x c',
                     c' |[ e ]| = c |[ e ]| -> bound_var_ctx c x -> bound_var_ctx c' x) /\
(forall f e x  c',
  c' <[ e ]> = f <[e]> -> bound_var_fundefs_ctx f x -> bound_var_fundefs_ctx c' x).
  Proof.
    exp_fundefs_ctx_induction IHe IHf; intros; destruct c'; try (inversion H; inversion H0; contradiction). 
  - symmetry in H. exfalso. apply ctx_circular in H. inversion H.
  -   inversion H; subst.
      inversion H0; auto; subst. constructor.
     eapply IHe; eauto.
  - symmetry in H. exfalso. apply ctx_circular in H. inversion H.
  -  inversion H; subst.
     inversion H0; auto; subst.
     constructor.
     eapply IHe; eauto.     
  - symmetry in H. exfalso. apply ctx_circular in H. inversion H.
  -  inversion H; subst.
     inversion H0; auto.
     subst. constructor; eapply IHe; eauto.
  - symmetry in H. exfalso. apply ctx_circular in H. inversion H.
  - inversion H; subst.
    revert H0; revert H3; revert H.
    revert l1; revert l.
    induction l; induction l1; intros; simpl in *.
    + inversion H3; subst.
      apply bound_var_Case_c in H0. inv H0.
      inv H1. inv H7.
      inv H1.
      apply bound_var_Case_c. right. left. eapply IHe; eauto.
      apply bound_var_Case_c; auto.
    + destruct a. inversion H3; subst.
      apply bound_var_Case_c in H0. 
      inv H0.
      inversion H1; subst. inversion H6.
      inv H1. apply bound_var_Case_c.
      left. apply bound_var_Ecase_cons. left. apply bound_var_app_ctx; auto.
      apply bound_var_Ecase_app in H0. inv H0.
      apply bound_var_Case_c. left. apply bound_var_Ecase_cons. auto.
      apply bound_var_Ecase_cons in H1. inv H1.
      apply bound_var_app_ctx in H0. inv H0.
      apply bound_var_Case_c. auto.
      apply bound_var_Case_c.  left. apply bound_var_Ecase_cons.
      left. apply bound_var_app_ctx; auto.
      apply bound_var_Case_c. auto.
    + destruct a; inversion H3; subst.
      apply bound_var_Case_cons1_c in H0. inversion H0; subst.
      * apply bound_var_app_ctx in H1. inversion H1; auto.
        subst.
        simpl. apply bound_var_Case_c. right. right. apply bound_var_Ecase_app. right. apply bound_var_Ecase_cons. left.
        apply bound_var_app_ctx. auto.
      * apply bound_var_Case_c in H1. destruct H1.
        apply bound_var_Case_c. right. right. apply bound_var_Ecase_app. auto.
        inv H1.
        apply bound_var_Case_c. right; right.
        apply bound_var_Ecase_app. right.
        apply bound_var_Ecase_cons. left. apply bound_var_app_ctx. auto.
        apply bound_var_Case_c. right. right.
        apply bound_var_Ecase_app. right. apply bound_var_Ecase_cons. auto.
    + destruct a0; destruct a.
      inversion H3; subst.
      apply bound_var_Case_cons1_c in H0.
      inversion H0.
      * subst.
        apply bound_var_Case_cons1_c. auto.
      * subst. apply bound_var_Case_cons1_c. right.
        apply IHl; eauto.
        inversion H; subst.
        reflexivity.
  - symmetry in H. exfalso. apply ctx_circular in H. inversion H.
  - inversion H; subst.
    inversion H0; auto.
    subst.
    apply Bound_Fun12_c. eapply IHe; eauto.
  - inversion H.
    inversion H0; subst.
    + apply bound_var_app_f_ctx in H6.
      destruct H6.
      * constructor. auto.
      * apply Bound_Fun22_c.
        apply bound_var_app_ctx. right. auto.
    + apply bound_var_Fun2_c.
      right.
      apply bound_var_app_ctx. left; auto.
  - symmetry in H. exfalso. apply ctx_circular in H. inversion H.
  - inversion H.
    rewrite <- H3 in H0.
    apply bound_var_Fun2_c in H0.
    apply  bound_var_Fun1_c.
    inversion H0; subst.
    left. apply bound_var_app_f_ctx. left; auto.
    apply bound_var_app_ctx in H1.
    inversion H1.
    subst. right; auto.
    left.
    apply bound_var_app_f_ctx. right; auto.
  - inversion H.
    inversion H0; subst.
    + constructor.
      eapply IHf; eauto.
    + apply Bound_Fun22_c. auto.
  - inversion H; subst. apply bound_var_Fcons1_c in H0.
      apply bound_var_Fcons1_c.
      destruct H0. auto.
      destruct H0.
      auto.
      destruct H0.
      right. right. left.
      eapply IHe; eauto.
      auto.
  - inversion H; subst.
    apply bound_var_Fcons2_c.
      apply bound_var_Fcons1_c in H0.
      inv H0.
      auto.
      inv H1.
      auto.
      inv H0.
      right; right. left.
      apply bound_var_app_ctx. auto.
      apply bound_var_app_f_ctx in H1.
      inv H1; auto.
      right; right. left.
      apply bound_var_app_ctx. auto.
  - inversion H; subst.
    apply bound_var_Fcons1_c.
      apply bound_var_Fcons2_c in H0.
      inv H0; auto.
      inv H1; auto.
      inv H0; auto.
      apply bound_var_app_ctx in H1.
      inv H1; auto.
      right; right; right.
      apply bound_var_app_f_ctx. auto.
      right; right; right.
      apply bound_var_app_f_ctx. auto.
  - inversion H; subst.
    apply bound_var_Fcons2_c.
      apply bound_var_Fcons2_c in H0.
      inv H0; auto.
      inv H1; auto.
      inv H0; auto.
      right. right.
      right. eapply IHf; eauto.
Qed.


  

    
Theorem bv_in_find_def_ctx2: forall x f t1 e xs1 c B, 
  find_def f (B<[e]>) = Some (t1, xs1, c |[ e ]|) ->
  bound_var_ctx c x -> bound_var_fundefs_ctx B x.
Proof.
  induction B; intros; simpl in H; destruct (M.elt_eq f v); subst.
  - inversion H; subst.
    constructor 3.
    eapply bv_in_ctx; eauto.
  - constructor 4.
    eapply bv_in_find_def_ctx; eauto.
  -     inversion H; subst.
        constructor 7. apply bound_var_app_ctx. left. auto.
  - apply IHB in H; auto.
Qed.





Theorem name_boundvar_ctx: forall  x B' e1,
    name_in_fundefs (B' <[ e1 ]>) x -> bound_var_fundefs_ctx B' x.
Proof.
  intros.
  induction B'; intros.
  - inversion H; subst. inversion H0; subst.
    constructor.
    constructor 4.
    apply name_in_fundefs_bound_var_fundefs; auto.    
  - inversion H; subst. inversion H0; subst. constructor.
    apply Bound_Fcons24_c.
    apply IHB'; auto. 
Qed.

 Theorem name_boundvar_arg: forall x xs1 f c t1 f0,
  List.In x xs1 ->
  find_def f f0 = Some (t1, xs1, c) -> bound_var_fundefs f0 x.
 Proof.
   induction f0; intros.
   - simpl in H0.
     destruct (M.elt_eq f v).
     inversion H0; subst.
     constructor. right. apply H.
     constructor 2. apply IHf0; auto.
   - inversion H0.
 Qed.
 
Theorem name_boundvar_arg_ctx: forall x xs1 t1 c e2 f B',
  List.In x xs1 ->
  find_def f (B' <[ e2 ]>) = Some (t1, xs1, c) -> bound_var_fundefs_ctx B' x.
Proof.
  induction B'; intros.
  - simpl in H0. destruct (M.elt_eq f v).
    + subst. inversion H0; subst.
      constructor 2. auto.
    + constructor 4. eapply name_boundvar_arg; eauto.
  - simpl in H0. destruct (M.elt_eq f v).
    + subst. inversion H0; subst.
      constructor. auto.
    + constructor 8. apply IHB'; auto.
Qed.

Theorem included_bound_var_arg_ctx: forall  xs1 t1 c e2 f B',
  find_def f (B' <[ e2 ]>) = Some (t1, xs1, c) ->
  Included var (FromList xs1) (bound_var_fundefs_ctx B').
Proof.
  intros. intro. intros.
  eapply name_boundvar_arg_ctx; eauto.
Qed.

  Lemma preord_env_P_def_funs_compat_pre_val x val k B  rho1 rho2 B' e1 e2 S1 :
    (forall m c (rho1 rho2 : env),
       m <  k ->
       ~ bound_var_ctx c x ->
       M.get x rho1 = Some val -> 
       preord_env_P pr cenv (occurs_free (c |[ e1 ]|)) m rho1 rho2 ->
       preord_exp pr cenv m (c |[ e1 ]|, rho1) (c |[ e2 ]|, rho2)) ->
    preord_env_P pr cenv (Union _ (occurs_free_fundefs (B' <[ e1 ]>))
                        (Setminus _ S1 (name_in_fundefs (B' <[ e1 ]>))))
                 k rho1 rho2 ->
    ~ bound_var_fundefs_ctx B x ->
    ~ bound_var_fundefs_ctx B' x ->
    M.get x rho1 = Some val ->        
    preord_env_P pr cenv (Union _ (Setminus _ S1 (name_in_fundefs (B' <[ e1 ]>)))
                        (Union _ (occurs_free_fundefs (B' <[ e1 ]>))
                               (name_in_fundefs (B <[ e1 ]>))))
                 k (def_funs (B' <[ e1 ]>) (B <[ e1 ]>) rho1 rho1)
                 (def_funs (B' <[ e2 ]>) (B <[ e2 ]>) rho2 rho2).
  Proof.
        revert B rho1 rho2 B' e1 e2 S1.
    induction k as [ k IH' ] using lt_wf_rec1.
    intros B rho1 rho2 B' e1 e2 S1 Hpre Henv Hbv Hbv' Hx.
    assert (Hval : forall f, preord_val pr cenv k (Vfun rho1 (B' <[ e1 ]>) f)
                                   (Vfun rho2 (B' <[ e2 ]>) f)).
    { intros f. rewrite preord_val_eq.
      intros vs1 vs2 j t1 xs1 e' rho1' Hlen Hf Hs.
      edestruct find_def_def_funs_ctx as [H1 | [c [H1 H2]]]; eauto.
      + edestruct (@setlist_length cps.val) as [rho2' Hs']; eauto.
        do 4 eexists; eauto. split; eauto.
        intros Hleq Hall.
        eapply preord_exp_refl.
        eapply preord_env_P_setlist_l; [| | now eauto | now eauto | now eauto ].
        eapply IH'; eauto. 
        intros. eapply Hpre; eauto. omega. 
        eapply preord_env_P_monotonic; [| eassumption ]. omega.
        intros x0 H Hfv. 
        eapply find_def_correct in Hf; eauto.
        eapply occurs_free_in_fun in Hfv; eauto.
        inv Hfv. exfalso. eauto. right. eapply Ensembles_util.Union_commut. eauto.
      + subst. edestruct (@setlist_length cps.val) as [rho2' Hs']; eauto.
        do 4 eexists; eauto. split; eauto.
        intros Hleq Hall. eapply Hpre; eauto.
        intro. apply Hbv'.
        eapply bv_in_find_def_ctx2; eauto.
        erewrite <- setlist_not_In.
        Focus 2. symmetry. apply Hs.

        apply get_fundefs_ctx; auto.
        
        intro.  apply Hbv'. eapply name_boundvar_arg_ctx; eauto. 
        eapply preord_env_P_setlist_l; [| | eauto | eauto | eauto ].
        eapply IH'; eauto.
        intros. eapply Hpre; eauto. omega. 
        eapply preord_env_P_monotonic; [| eassumption ]. omega.
        intros x0 H Hfv. 
        eapply find_def_correct in Hf; eauto.
        eapply occurs_free_in_fun in Hfv; eauto.
        inv Hfv. exfalso. eauto. right. eapply Ensembles_util.Union_commut. eauto. }
    induction B.
    - simpl. apply preord_env_P_extend.
      + clear Hbv. induction f.
        { simpl. apply preord_env_P_extend.
          - eapply preord_env_P_antimon; [ eassumption |].
            rewrite Ensembles_util.Setminus_Union.
            eauto 15 with Ensembles_DB typeclass_instances.
          - eapply Hval. }
        { simpl. eapply preord_env_P_antimon ; [ eassumption |].
          eauto with Ensembles_DB. }
      + eapply Hval.
    - simpl. apply preord_env_P_extend.
      + eapply preord_env_P_antimon; [now eauto |].
        eauto 10 with Ensembles_DB.
      + apply Hval.
  Qed.


  Theorem included_name_fundefs_ctx: forall B e,
    Included var (name_in_fundefs (B <[ e ]>)) (bound_var_fundefs_ctx B).
  Proof. 
    intros. intro. eapply name_boundvar_ctx.
  Qed.
    


  Lemma preord_env_P_def_funs_compat_pre_vals xs vs vs' k B  rho1 rho2 B' e1 e2 S1 :
    (forall m c (rho1 rho2 : env),
       m <  k ->
       Disjoint var (bound_var_ctx c) (FromList xs)->
       getlist xs rho1 = Some vs ->
       getlist xs rho2 = Some vs' ->
       preord_env_P pr cenv (occurs_free (c |[ e1 ]|)) m rho1 rho2 ->
       preord_exp pr cenv m (c |[ e1 ]|, rho1) (c |[ e2 ]|, rho2)) ->
    preord_env_P pr cenv (Union _ (occurs_free_fundefs (B' <[ e1 ]>))
                        (Setminus _ S1 (name_in_fundefs (B' <[ e1 ]>))))
                 k rho1 rho2 ->
    Disjoint var (bound_var_fundefs_ctx B) (FromList xs) ->
    Disjoint var (bound_var_fundefs_ctx B') (FromList xs) ->
    getlist xs rho1 = Some vs ->
    getlist xs rho2 = Some vs' ->
    preord_env_P pr cenv (Union _ (Setminus _ S1 (name_in_fundefs (B' <[ e1 ]>)))
                        (Union _ (occurs_free_fundefs (B' <[ e1 ]>))
                               (name_in_fundefs (B <[ e1 ]>))))
                 k (def_funs (B' <[ e1 ]>) (B <[ e1 ]>) rho1 rho1)
                 (def_funs (B' <[ e2 ]>) (B <[ e2 ]>) rho2 rho2).
  Proof.
    revert B rho1 rho2 B' e1 e2 S1.
    induction k as [ k IH' ] using lt_wf_rec1.
    intros B rho1 rho2 B' e1 e2 S1 Hpre Henv Hbv Hbv' Hx Hx'.
    assert (Hval : forall f, preord_val pr cenv k (Vfun rho1 (B' <[ e1 ]>) f)
                                   (Vfun rho2 (B' <[ e2 ]>) f)).
    { intros f. rewrite preord_val_eq.
      intros vs1 vs2 j t1 xs1 e' rho1' Hlen Hf Hs.
      edestruct find_def_def_funs_ctx as [H1 | [c [H1 H2]]]; eauto.
      + edestruct (@setlist_length cps.val) as [rho2' Hs']; eauto.
        do 4 eexists; eauto. split; eauto.
        intros Hleq Hall.
        eapply preord_exp_refl.
        eapply preord_env_P_setlist_l; [| | now eauto | now eauto | now eauto ].
        eapply IH'; eauto. 
        intros. eapply Hpre; eauto. omega. 
        eapply preord_env_P_monotonic; [| eassumption ]. omega.
        intros x0 H Hfv. 
        eapply find_def_correct in Hf; eauto.
        eapply occurs_free_in_fun in Hfv; eauto.
        inv Hfv. exfalso. eauto. right. eapply Ensembles_util.Union_commut. eauto.
      + subst. edestruct (@setlist_length cps.val) as [rho2' Hs']; eauto.
        do 4 eexists; eauto. split; eauto.
        intros Hleq Hall. eapply Hpre; eauto.
        {
          split; intro; intro. inv H.
          inv Hbv'.
          specialize (H x).
          apply H. split; auto.
          eapply bv_in_find_def_ctx2; eauto.
        }          
        erewrite getlist_setlist_Disjoint.
        rewrite getlist_def_funs_Disjoint.
        apply Hx.
        3: (symmetry in Hs; eauto).
        { split. intros. intro.

          inversion H; subst.
          inversion Hbv'.
          specialize (H3 x).
          apply H3. split; auto.
          eapply name_boundvar_ctx.
          apply H1.
        }
        eapply Disjoint_Included_l.
        eapply included_bound_var_arg_ctx.
        apply Hf. auto.
        erewrite getlist_setlist_Disjoint.
        rewrite getlist_def_funs_Disjoint.
        apply Hx'.
        3: (symmetry in Hs'; eauto).
        { split. intros. intro.

          inversion H; subst.
          inversion Hbv'.
          specialize (H3 x).
          apply H3. split; auto.
          eapply name_boundvar_ctx.
          apply H1.
        }
        eapply Disjoint_Included_l.
        eapply included_bound_var_arg_ctx.
        apply H2. auto.        
        eapply preord_env_P_setlist_l; [| | eauto | eauto | eauto ].
        eapply IH'; eauto.
        intros. eapply Hpre; eauto. omega. 
        eapply preord_env_P_monotonic; [| eassumption ]. omega.
        intros x0 H Hfv. 
        eapply find_def_correct in Hf; eauto.
        eapply occurs_free_in_fun in Hfv; eauto.
        inv Hfv. exfalso. eauto. right. eapply Ensembles_util.Union_commut. eauto. }
    induction B.
    - simpl. apply preord_env_P_extend.
      + clear Hbv. induction f.
        { simpl. apply preord_env_P_extend.
          - eapply preord_env_P_antimon; [ eassumption |].
            rewrite Ensembles_util.Setminus_Union.
            eauto 15 with Ensembles_DB typeclass_instances.
          - eapply Hval. }
        { simpl. eapply preord_env_P_antimon ; [ eassumption |].
          eauto with Ensembles_DB. }
      + eapply Hval.
    - simpl. apply preord_env_P_extend.
      + eapply preord_env_P_antimon. apply IHB.
        rewrite bound_var_Fcons2_c in Hbv.
        eapply Disjoint_Included_l.
        2: apply Hbv.
        right; right; right; auto.        
        eauto 10 with Ensembles_DB.
      + apply Hval.
  Qed.


  
  
  

 Theorem var_dec_eq: decidable_eq var.
 Proof.
   intro. intros. unfold decidable.
   destruct (var_dec x y); auto.
 Qed.

 
 Theorem fundefs_append_fnil_r: forall B, fundefs_append B Fnil = B.
 Proof.
   induction B.
   simpl. rewrite IHB. auto.
   auto.
 Qed.


 
 Definition eq_env_P {A}:  Ensemble var -> M.t A -> M.t A -> Prop :=
    fun S rho1 rho2 =>
      forall x, S x -> M.get x rho1 = M.get x rho2.

  Theorem eq_env_P_refl: forall {A} S (r:M.t A), eq_env_P S r r.
  Proof.
    intros; intro; intros. reflexivity.
  Qed.

  Theorem eq_env_P_sym: forall {A} S (r:M.t A) r', eq_env_P S r r' -> eq_env_P S r' r.
  Proof.
    intros; intro. intro. apply H in H0. auto.
  Qed.
  
  Theorem eq_env_P_trans: forall {A} S (r1:M.t A) r2 r3,
                            eq_env_P S r1 r2 -> eq_env_P S r2 r3 -> eq_env_P S r1 r3.
  Proof.
    intros. intro. intros.
    specialize (H x H1).
    specialize (H0 x H1).
    rewrite H. auto.
  Qed.

 Theorem eq_P_apply_r:
   forall x sub sub',
   eq_env_P (Singleton _ x) sub sub' ->
   apply_r sub x = apply_r sub' x.
 Proof.
   intros.
   unfold apply_r.   
   rewrite H.
   auto.
   constructor.
 Qed.

 Theorem eq_P_apply_r_list:
   forall sub sub' l,
   eq_env_P (FromList l) sub sub' ->
   apply_r_list sub l = apply_r_list sub' l.
 Proof.
   induction l.
   auto.
   simpl.
   intros.
   erewrite eq_P_apply_r.
   erewrite IHl. auto.
   intro. intro. apply H.
   constructor 2; auto.
   intro. intro; apply H.
   constructor.
   inv H0. auto.
 Qed.

 
  Theorem eq_env_P_def_funs: forall fl rho,
    eq_env_P (name_in_fundefs fl) (def_funs fl fl rho rho) rho 
     -> eq_env_P (fun v => True) (def_funs fl fl rho rho) rho. 
  Proof.
    intros.
    assert (Hv := Decidable_name_in_fundefs fl).
    destruct Hv.
    intro; intro.
    clear H0.
    specialize (Dec x).
    destruct Dec.
    + apply H in H0. auto.
    + apply def_funs_neq.
      auto.
  Qed.      
      
  Theorem eq_env_preord:
    forall S r1 r2,
      eq_env_P S r1 r2 ->
      forall pr cenv,
    (forall q, preord_env_P pr cenv S q r1 r2).
  Proof.
    intros. intro.
    intro.
    apply H in H0.
    unfold preord_var_env. intros.
    rewrite H0 in H1.
    eexists.
    split; eauto.
    apply preord_val_refl.
  Qed.

  Theorem preord_env_P_eq_r: forall S S' k rho1 rho2 rho3,
    preord_env_P pr cenv S k rho1 rho2 ->
    eq_env_P S' rho2 rho3 ->
    preord_env_P pr cenv (Intersection _ S  S') k rho1 rho3.
  Proof.
    intros. intro. intro. intro. intros.
    inv H1.
    apply H in H2; auto.
    destructAll.
    rewrite H0 in H1; auto.
    exists x0; split; eauto.
  Qed.

  Theorem preord_env_P_eq_l: forall S S' k rho1 rho2 rho3,
                               preord_env_P pr cenv S k rho1 rho2 ->
    eq_env_P S' rho1 rho3 ->
    preord_env_P pr cenv (Intersection _ S  S') k rho3 rho2.
  Proof.
    intros. intro. intro. intro. intros.
    inv H1.
    rewrite <- H0 in H2; auto.
    apply H in H2; auto.
  Qed.

  
  Lemma eq_env_P_set_not_in_P_l':
      forall  (x : var) (v : val) 
             (P : Ensemble var) (rho1 rho2 : env),
        eq_env_P P  (M.set x v rho1) rho2 ->
        Disjoint var P (Singleton var x) ->
        eq_env_P P  rho1 rho2.
Proof.
  intros. intro; intros.
  specialize (H x0 H1).
  rewrite M.gso in H. auto.
  intro.
  inv H0.
  specialize (H3 x).
  apply H3; auto.
Qed.

Theorem eq_env_P_def_funs_not_in_P_l':
  forall (B B' : fundefs) 
         (P : Ensemble var) (rho : M.t val) (rho1 rho2 : env),
    eq_env_P P (def_funs B' B rho rho1) rho2 ->
  Disjoint var P (name_in_fundefs B) ->
    eq_env_P P rho1 rho2. 
Proof.
  intros. intro; intros.
  specialize (H x H1).
  rewrite def_funs_neq in H; auto.
  inv H0.
  specialize (H2 x).
  intro. apply H2; auto.
Qed.



Theorem eq_env_P_def_funs_not_in_P_r:
  forall B B' P rho rho1 rho2,
    eq_env_P P rho1 rho2 ->
    Disjoint _ P (name_in_fundefs B) ->
    eq_env_P P rho1 (def_funs B' B rho rho2).
Proof.
  intros. intro. intro.
  specialize (H x H1).
  rewrite def_funs_neq.
  auto.
  intro. inv H0.
  specialize (H3 x).
  apply H3. auto.
Qed.

Theorem eq_env_P_setlist_not_in_P_r :
forall (xs : list M.elt) 
  (vs : list val) (P : Ensemble var) (rho1 rho2 : env)
  (rho2' : M.t val),
  eq_env_P P rho1 rho2 ->
  Some rho2' = setlist xs vs rho2 ->
  Disjoint var P (FromList xs) -> eq_env_P P rho1 rho2'.
Proof.
  intros. intro. intros.
  specialize (H x H2).
  erewrite <- setlist_not_In with (rho' := rho2'); eauto.
  intro.
  inv H1. specialize (H4 x).
  apply H4; auto.
Qed.

Theorem eq_env_P_getlist: forall {A} S (rho:M.t A) rho',
  eq_env_P S rho rho' -> forall xs,
  Included _ (FromList xs) S ->
  getlist xs rho = getlist xs rho'.
Proof.
  induction xs; intros. auto.
  simpl. destruct (M.get a rho) eqn:gar.
  + assert (S a).
    apply H0.
    constructor. reflexivity.
    apply H in H1.
    rewrite <- H1. rewrite gar.
    rewrite IHxs. reflexivity.
    intro. intros.
    apply H0.
    constructor 2. auto.
  + assert (S a).
    apply H0.
    constructor; reflexivity.
    apply H in H1.
    rewrite <- H1.
    rewrite gar.
    auto.
Qed.    



 



(* More precise statement of find_def_def_funs_ctx *)
  Lemma find_def_def_funs_ctx' B f e1 tau xs e' :
    find_def f (B <[ e1 ]>) = Some (tau, xs, e') ->
    (forall e2, (find_def f (B <[ e2 ]>) = Some (tau, xs, e'))) \/
    (exists c, e' = c |[ e1 ]| /\
              (forall e2, find_def f (B <[ e2 ]>) = Some (tau, xs, c |[ e2 ]|)) /\ (exists fd fd', B = (app_fundefs_ctx fd (Fcons1_c f tau xs c fd')))).
  Proof.
    revert tau xs e'. induction B; simpl; intros tau xs e' Heq.
    - destruct (M.elt_eq f v).
      + inv Heq. right. eexists e.
        split; eauto.
        split; eauto. exists Fnil, f0; auto.
      + left; eauto.
    - destruct (M.elt_eq f v).
      + inv Heq. left; eauto.
      + apply IHB in Heq. inv Heq. left; auto.
        inv H. destruct H0.
        inv H0. right.  exists x. split; auto. split; auto. destruct H2. destruct H.
        exists (Fcons v c l e x0), (x1).
        simpl. rewrite H. auto.        
  Qed.

  

    
  Lemma preord_env_P_def_funs_compat_pre_vals_stem_set S k B  rho1 rho2 B' e1 e2 S1 :
    (forall m c (rho1' rho2' : env),
       m <  k ->
       Disjoint var (bound_stem_ctx c) S ->
       eq_env_P S rho1 rho1' -> 
       eq_env_P S rho2 rho2' -> 
       preord_env_P pr cenv (occurs_free (c |[ e1 ]|)) m rho1' rho2' ->
       preord_exp pr cenv m (c |[ e1 ]|, rho1') (c |[ e2 ]|, rho2')) ->
    preord_env_P pr cenv (Union _ (occurs_free_fundefs (B' <[ e1 ]>))
                        (Setminus _ S1 (name_in_fundefs (B' <[ e1 ]>))))
                 k rho1 rho2 ->
    Disjoint var (Union var (names_in_fundefs_ctx B) (bound_stem_fundefs_ctx B)) S ->
    Disjoint var (Union var (names_in_fundefs_ctx B') (bound_stem_fundefs_ctx B')) S ->
    preord_env_P pr cenv (Union _ (Setminus _ S1 (name_in_fundefs (B' <[ e1 ]>)))
                        (Union _ (occurs_free_fundefs (B' <[ e1 ]>))
                               (name_in_fundefs (B <[ e1 ]>))))
                 k (def_funs (B' <[ e1 ]>) (B <[ e1 ]>) rho1 rho1)
                 (def_funs (B' <[ e2 ]>) (B <[ e2 ]>) rho2 rho2).
  Proof.
    revert B rho1 rho2 B' e1 e2 S1.
    induction k as [ k IH' ] using lt_wf_rec1.
    intros B rho1 rho2 B' e1 e2 S1 Hpre Henv Hbv Hbv'.
    assert (Hval : forall f, preord_val pr cenv k (Vfun rho1 (B' <[ e1 ]>) f)
                                   (Vfun rho2 (B' <[ e2 ]>) f)).
    { intros f. rewrite preord_val_eq.
      intros vs1 vs2 j t1 xs1 e' rho1' Hlen Hf Hs.
      edestruct find_def_def_funs_ctx' as [H1 | [c [H1 H2]]]; eauto.
      
      + edestruct (@setlist_length cps.val) as [rho2' Hs']; eauto.
        do 4 eexists; eauto. split; eauto.
        intros Hleq Hall.
        eapply preord_exp_refl.
        eapply preord_env_P_setlist_l; [| | now eauto | now eauto | now eauto ].
        eapply IH'; eauto. 
        intros. eapply Hpre; eauto. omega. 
        eapply preord_env_P_monotonic; [| eassumption ]. omega.
        intros x0 H Hfv. 
        eapply find_def_correct in Hf; eauto.
        eapply occurs_free_in_fun in Hfv; eauto.
        inv Hfv. exfalso. eauto.  right. eapply Ensembles_util.Union_commut. eauto.
      + destruct H2. inv H0. inv H2. 
        edestruct (@setlist_length cps.val) as [rho2' Hs']; eauto.
        do 4 eexists; eauto.
        split; eauto.
        intros Hleq Hall. eapply Hpre; eauto.
        {
          split; intro; intro. rewrite bound_stem_app_fundefs_ctx in Hbv'.
          inv Hbv'. specialize (H1 x1). apply H1. inv H0; auto.
        }
        eapply eq_env_P_setlist_not_in_P_r; eauto.
        
        
        apply eq_env_P_def_funs_not_in_P_r. apply eq_env_P_refl.

        rewrite <- name_in_fundefs_ctx_ctx.
        eauto with Ensembles_DB.
        rewrite bound_stem_app_fundefs_ctx in Hbv'.
        eauto with Ensembles_DB.

        symmetry in Hs'.
        intro; eapply eq_env_P_setlist_not_in_P_r; eauto.
        apply eq_env_P_def_funs_not_in_P_r.
        apply eq_env_P_refl.
        rewrite <- name_in_fundefs_ctx_ctx.
        eauto with Ensembles_DB.
        rewrite bound_stem_app_fundefs_ctx in Hbv'.
        eauto with Ensembles_DB.

        eapply preord_env_P_setlist_l; [| | eauto | eauto | eauto ].
        eapply IH'; eauto.
        intros. eapply Hpre; eauto. omega. 
        eapply preord_env_P_monotonic; [| eassumption ]. omega.
        intros x1 Hv Hfv. 
        eapply find_def_correct in Hf; eauto.
        eapply occurs_free_in_fun in Hfv; eauto.
        inv Hfv. exfalso. eauto. right. eapply Ensembles_util.Union_commut. eauto. }
    induction B.
    - simpl. apply preord_env_P_extend.
      + clear Hbv. induction f.
        { simpl. apply preord_env_P_extend.
          - eapply preord_env_P_antimon; [ eassumption |].
            rewrite Ensembles_util.Setminus_Union.
            eauto 15 with Ensembles_DB typeclass_instances.
          - eapply Hval. }
        { simpl. eapply preord_env_P_antimon ; [ eassumption |].
          eauto with Ensembles_DB. }
      + eapply Hval.
    - simpl. apply preord_env_P_extend.
      + eapply preord_env_P_antimon. apply IHB.
        eapply Disjoint_Included_l.        
        2: apply Hbv.
        apply Included_Union_compat.
        simpl. right; auto.
        rewrite bound_stem_Fcons2_c. reflexivity. 
        eauto 10 with Ensembles_DB.
      + apply Hval.
  Qed.
 
Lemma preord_env_P_def_funs_compat_pre_vals_set S k B  rho1 rho2 B' e1 e2 S1 :
    (forall m c (rho1' rho2' : env),
       m <  k ->
       Disjoint var (bound_var_ctx c) S ->
       eq_env_P S rho1 rho1' -> 
       eq_env_P S rho2 rho2' -> 
       preord_env_P pr cenv (occurs_free (c |[ e1 ]|)) m rho1' rho2' ->
       preord_exp pr cenv m (c |[ e1 ]|, rho1') (c |[ e2 ]|, rho2')) ->
    preord_env_P pr cenv (Union _ (occurs_free_fundefs (B' <[ e1 ]>))
                        (Setminus _ S1 (name_in_fundefs (B' <[ e1 ]>))))
                 k rho1 rho2 ->
    Disjoint var (bound_var_fundefs_ctx B) S ->
    Disjoint var (bound_var_fundefs_ctx B') S ->
    preord_env_P pr cenv (Union _ (Setminus _ S1 (name_in_fundefs (B' <[ e1 ]>)))
                        (Union _ (occurs_free_fundefs (B' <[ e1 ]>))
                               (name_in_fundefs (B <[ e1 ]>))))
                 k (def_funs (B' <[ e1 ]>) (B <[ e1 ]>) rho1 rho1)
                 (def_funs (B' <[ e2 ]>) (B <[ e2 ]>) rho2 rho2).
  Proof.
    revert B rho1 rho2 B' e1 e2 S1.
    induction k as [ k IH' ] using lt_wf_rec1.
    intros B rho1 rho2 B' e1 e2 S1 Hpre Henv Hbv Hbv'.
    assert (Hval : forall f, preord_val pr cenv k (Vfun rho1 (B' <[ e1 ]>) f)
                                   (Vfun rho2 (B' <[ e2 ]>) f)).
    { intros f. rewrite preord_val_eq.
      intros vs1 vs2 j t1 xs1 e' rho1' Hlen Hf Hs.
      edestruct find_def_def_funs_ctx as [H1 | [c [H1 H2]]]; eauto.
      + edestruct (@setlist_length cps.val) as [rho2' Hs']; eauto.
        do 4 eexists; eauto. split; eauto.
        intros Hleq Hall.
        eapply preord_exp_refl.
        eapply preord_env_P_setlist_l; [| | now eauto | now eauto | now eauto ].
        eapply IH'; eauto. 
        intros. eapply Hpre; eauto. omega. 
        eapply preord_env_P_monotonic; [| eassumption ]. omega.
        intros x0 H Hfv. 
        eapply find_def_correct in Hf; eauto.
        eapply occurs_free_in_fun in Hfv; eauto.
        inv Hfv. exfalso. eauto. right. eapply Ensembles_util.Union_commut. eauto.
      + subst. edestruct (@setlist_length cps.val) as [rho2' Hs']; eauto.
        do 4 eexists; eauto. split; eauto.
        intros Hleq Hall. eapply Hpre; eauto.
        {
          split; intro; intro. inv H.
          inv Hbv'.
          specialize (H x).
          apply H. split; auto.
          eapply bv_in_find_def_ctx2; eauto.
        } 
        eapply eq_env_P_setlist_not_in_P_r; eauto.
        apply eq_env_P_def_funs_not_in_P_r. apply eq_env_P_refl. 
        split. intros. intro. destruct H.
        apply name_boundvar_ctx in H0.
        inv Hbv'. specialize (H1 x). auto.
        split. intros; intro. inv H.
        eapply included_bound_var_arg_ctx in H1; eauto.
        inv Hbv'. specialize (H x); auto.

        symmetry in Hs'.
        intro; eapply eq_env_P_setlist_not_in_P_r; eauto.
        apply eq_env_P_def_funs_not_in_P_r. apply eq_env_P_refl.
        split. intros. intro. destruct H.
        apply name_boundvar_ctx in H0.
        inv Hbv'. specialize (H1 x0). apply H1. auto.
        split. intros; intro. inv H.
        eapply included_bound_var_arg_ctx in H1; eauto.
        inv Hbv'. specialize (H x0); auto.        

        eapply preord_env_P_setlist_l; [| | eauto | eauto | eauto ].
        eapply IH'; eauto.
        intros. eapply Hpre; eauto. omega. 
        eapply preord_env_P_monotonic; [| eassumption ]. omega.
        intros x0 H Hfv. 
        eapply find_def_correct in Hf; eauto.
        eapply occurs_free_in_fun in Hfv; eauto.
        inv Hfv. exfalso. eauto. right. eapply Ensembles_util.Union_commut. eauto. }
    induction B.
    - simpl. apply preord_env_P_extend.
      + clear Hbv. induction f.
        { simpl. apply preord_env_P_extend.
          - eapply preord_env_P_antimon; [ eassumption |].
            rewrite Ensembles_util.Setminus_Union.
            eauto 15 with Ensembles_DB typeclass_instances.
          - eapply Hval. }
        { simpl. eapply preord_env_P_antimon ; [ eassumption |].
          eauto with Ensembles_DB. }
      + eapply Hval.
    - simpl. apply preord_env_P_extend.
      + eapply preord_env_P_antimon. apply IHB.
        rewrite bound_var_Fcons2_c in Hbv.
        eapply Disjoint_Included_l.
        2: apply Hbv.
        right; right; right; auto.        
        eauto 10 with Ensembles_DB.
      + apply Hval.
  Qed.


  
(*This means that only bound variables on the applicative context c will modify the evaluation context rho *)
    Lemma preord_exp_compat_vals_stem_set S k rho1 rho2 c e1 e2 :
      (forall k' rho1' rho2', k' <= k ->
                              preord_env_P pr cenv (occurs_free e1) k' rho1' rho2' ->
                              
                              eq_env_P S rho1 rho1' ->
                              eq_env_P S rho2 rho2' ->
                              preord_exp pr cenv k' (e1, rho1') (e2, rho2')) ->
    Disjoint var (bound_stem_ctx c) S ->
    preord_env_P pr cenv (occurs_free (c |[ e1 ]|)) k rho1 rho2 ->
    preord_exp pr cenv k (c |[ e1 ]|, rho1) (c |[ e2 ]|, rho2).
  Proof.
    revert S c rho1 rho2 e1 e2. induction k as [ k IH' ] using lt_wf_rec1.
    induction c; intros rho1 rho2 e1 e2 Hyp Hbv Hpre; eauto.
    - simpl. apply Hyp. auto.
      simpl in Hpre. apply Hpre.
      apply eq_env_P_refl.
      apply eq_env_P_refl.
    -  rewrite bound_stem_Econstr_c in Hbv. simpl.  
      eapply preord_exp_const_compat; eauto; intros.
      * eapply Forall2_same. intros x0 HIn. apply Hpre. constructor. auto.
      * assert (Disjoint _ S (Singleton _ v)).
        {
          eauto 10 with Ensembles_DB.
        }
        eapply IHc; eauto.
        {
          intros.
          apply Hyp; eauto.
          eapply eq_env_P_set_not_in_P_l'; eauto.
          eapply eq_env_P_set_not_in_P_l'; eauto.
        }

        eapply Disjoint_Included_l; eauto.
        left; auto.
        apply preord_env_P_extend.
        eapply preord_env_P_antimon; eauto.
        simpl.
        rewrite occurs_free_Econstr.
        eauto 10 with Ensembles_DB.
        rewrite preord_val_eq. constructor. reflexivity.
        apply Forall2_Forall2_asym_included; auto.
    - simpl app_ctx_f.
      rewrite bound_stem_Eproj_c in Hbv.
      eapply preord_exp_proj_compat; eauto.
      + eapply Hpre. constructor; eauto.
      + intros vs1 vs2 Hall.
        assert (Disjoint _ S (Singleton _ v)).
        {
          eauto 10 with Ensembles_DB.
        }
        eapply IHc; eauto.
         {
          intros.
          apply Hyp; eauto.
          eapply eq_env_P_set_not_in_P_l'; eauto.
          eapply eq_env_P_set_not_in_P_l'; eauto.
        }
         eauto with Ensembles_DB. 
        eapply preord_env_P_extend; [| assumption ].
        eapply preord_env_P_antimon; eauto.
        simpl. rewrite occurs_free_Eproj.
        eauto with Ensembles_DB.
    - simpl.
      rewrite bound_stem_Eprim_c in Hbv.
      eapply preord_exp_prim_compat; eauto.
      + eapply Forall2_same. intros x0 Hin. eapply Hpre. constructor; eauto.
      + intros vs1 vs2 Hall.
        assert (Disjoint _ S (Singleton _ v)).
        {
          eauto 10 with Ensembles_DB.
        }
        eapply IHc; eauto.
         {
          intros.
          apply Hyp; eauto.
          eapply eq_env_P_set_not_in_P_l'; eauto.
          eapply eq_env_P_set_not_in_P_l'; eauto.
        }
         eauto with Ensembles_DB. 
        eapply preord_env_P_extend; [| assumption ].
        eapply preord_env_P_antimon; eauto.
        simpl. rewrite occurs_free_Eprim.
        eauto with Ensembles_DB.
    - simpl. eapply preord_exp_case_compat; eauto.
      eapply IHc; auto.      
      rewrite bound_stem_Case_c in Hbv.
      eapply Disjoint_Included_l; eauto.
      reflexivity.      
      eapply preord_env_P_antimon; eauto.
      simpl. intros x0 H.
      eapply occurs_free_Ecase_Included; eauto.
      eapply in_or_app. right. left; eauto.
    - simpl.
      rewrite bound_stem_Fun1_c in Hbv.
      eapply preord_exp_fun_compat; eauto.      
      assert (Disjoint _ S (name_in_fundefs f)).
      {
        eapply Disjoint_Included_l in Hbv.
        apply Disjoint_sym. apply Hbv.
        left.
        auto.
        } 
        eapply IHc; eauto.
         {
          intros.
          apply Hyp; eauto.
          eapply eq_env_P_def_funs_not_in_P_l'; eauto.
          eapply eq_env_P_def_funs_not_in_P_l'; eauto.          
        }
         eauto with Ensembles_DB. 
         eapply preord_env_P_def_funs_cor.
         eapply preord_env_P_antimon; [ eassumption |].
         simpl. rewrite occurs_free_Efun.
         eauto with Ensembles_DB.
    - intros v1 c1 Hleq Hstep. inv Hstep.
      edestruct (preord_exp_refl pr cenv k e) as [v2 [c2 [Hstep1 Henv2]]]; eauto.
      + eapply preord_env_P_antimon.
        * rewrite bound_stem_Fun2_c in Hbv.
          assert (Hbv' := Disjoint_Union_l  _ _ _ Hbv).
          eapply preord_env_P_def_funs_compat_pre_vals_stem_set; eauto.
          intros. eapply IH'; eauto.
          intros.
          eapply Hyp; eauto.
          omega.
          eapply eq_env_P_trans.
          apply H1. auto.          
          eapply eq_env_P_trans; eauto.
          eapply preord_env_P_antimon; [ eassumption |].
          intros x' H'. simpl. inv H'.
          now eapply Free_Efun2.
          inv H. constructor; eauto.
        * eapply Ensembles_util.Included_trans.
          eapply occurs_free_Efun_Included.
          normalize_occurs_free. eauto with Ensembles_DB. 
      + repeat eexists; eauto. simpl. constructor; eauto.
  Qed.


  (*This means that only bound variables on the applicative context c will modify the evaluation context rho *)
    Lemma preord_exp_compat_vals_set S k rho1 rho2 c e1 e2 :
      (forall k' rho1' rho2', k' <= k ->
                              preord_env_P pr cenv (occurs_free e1) k' rho1' rho2' ->
                              
                              eq_env_P S rho1 rho1' ->
                              eq_env_P S rho2 rho2' ->
                              preord_exp pr cenv k' (e1, rho1') (e2, rho2')) ->
    Disjoint var (bound_var_ctx c) S ->
    preord_env_P pr cenv (occurs_free (c |[ e1 ]|)) k rho1 rho2 ->
    preord_exp pr cenv k (c |[ e1 ]|, rho1) (c |[ e2 ]|, rho2).
  Proof.
    intros.
    eapply preord_exp_compat_vals_stem_set; eauto.
    eapply Disjoint_Included_l; eauto.
    apply bound_stem_var.
  Qed.

  
    (* almost generalization of preord_exp_combat_vals_le (and val) to sets-> would need rho1 = rho1' /\ rho2 = rho2' on S *)
     Corollary preord_exp_compat_vals_set' S k rho1 rho2 c e1 e2 :
      (forall k' rho1' rho2', k' <= k ->
                              preord_env_P pr cenv (occurs_free e1) k' rho1' rho2' ->
                              (* anything in S will be unchanged *)
                              (forall q, preord_env_P pr cenv S q rho1 rho1') -> 
                              (forall q, preord_env_P pr cenv S q rho2 rho2') -> 
                              preord_exp pr cenv k' (e1, rho1') (e2, rho2')) ->
    Disjoint var (bound_var_ctx c) S ->
    preord_env_P pr cenv (occurs_free (c |[ e1 ]|)) k rho1 rho2 ->
    preord_exp pr cenv k (c |[ e1 ]|, rho1) (c |[ e2 ]|, rho2).
    Proof.
      intros.
      eapply preord_exp_compat_vals_set; eauto.
      intros.
      apply H; eauto.
      intro.
      apply eq_env_preord. auto.
      intro.
      apply eq_env_preord. auto.
  Qed.

  
  Corollary preord_exp_compat_stem_vals_le xs vs vs' k rho1 rho2 c e1 e2 :
      (forall k' rho1 rho2, preord_env_P pr cenv (occurs_free e1) k' rho1 rho2 ->
                           k' <= k ->
                         getlist xs rho1 = Some vs ->
                         getlist xs rho2 = Some vs' -> 
                         preord_exp pr cenv k' (e1, rho1) (e2, rho2)) ->
    Disjoint var (bound_stem_ctx c) (FromList xs) ->
    getlist xs rho1 = Some vs ->
    getlist xs rho2 = Some vs' -> 
    preord_env_P pr cenv (occurs_free (c |[ e1 ]|)) k rho1 rho2 ->
    preord_exp pr cenv k (c |[ e1 ]|, rho1) (c |[ e2 ]|, rho2).
  Proof.
    intros.
    eapply preord_exp_compat_vals_stem_set with (S := FromList xs); eauto.
    intros. apply H; eauto.
    erewrite <- eq_env_P_getlist.
    eauto.
    eauto. intro; auto.
    erewrite <- eq_env_P_getlist.
    eauto.
    eauto. intro; auto.
  Qed.    


  


  Corollary preord_exp_compat_vals_le xs vs vs' k rho1 rho2 c e1 e2 :
      (forall k' rho1 rho2, preord_env_P pr cenv (occurs_free e1) k' rho1 rho2 ->
                           k' <= k ->
                         getlist xs rho1 = Some vs ->
                         getlist xs rho2 = Some vs' -> 
                         preord_exp pr cenv k' (e1, rho1) (e2, rho2)) ->
    Disjoint var (bound_var_ctx c) (FromList xs) ->
    getlist xs rho1 = Some vs ->
    getlist xs rho2 = Some vs' -> 
    preord_env_P pr cenv (occurs_free (c |[ e1 ]|)) k rho1 rho2 ->
    preord_exp pr cenv k (c |[ e1 ]|, rho1) (c |[ e2 ]|, rho2).
  Proof.
    intros.
    eapply preord_exp_compat_stem_vals_le; eauto.
    eapply Disjoint_Included_l; eauto.
    apply bound_stem_var.
  Qed.    

    Corollary preord_exp_compat_stem_vals xs vs vs' k rho1 rho2 c e1 e2 :
    (forall k rho1 rho2, preord_env_P pr cenv (occurs_free e1) k rho1 rho2 ->
                         getlist xs rho1 = Some vs ->
                         getlist xs rho2 = Some vs' -> 
                         preord_exp pr cenv k (e1, rho1) (e2, rho2)) ->
    Disjoint var (bound_stem_ctx c) (FromList xs) ->
    getlist xs rho1 = Some vs ->
    getlist xs rho2 = Some vs' -> 
    preord_env_P pr cenv (occurs_free (c |[ e1 ]|)) k rho1 rho2 ->
    preord_exp pr cenv k (c |[ e1 ]|, rho1) (c |[ e2 ]|, rho2).
  Proof.
    intros.
    eapply preord_exp_compat_stem_vals_le; eauto.
  Qed.


  (* generalization of compat_vals to a list of variable
 see preord_exp_combat_vals_le for stronger theorem that only needs the inner k to be <= the outer k 
 *)
  Corollary preord_exp_compat_vals xs vs vs' k rho1 rho2 c e1 e2 :
    (forall k rho1 rho2, preord_env_P pr cenv (occurs_free e1) k rho1 rho2 ->
                         getlist xs rho1 = Some vs ->
                         getlist xs rho2 = Some vs' -> 
                         preord_exp pr cenv k (e1, rho1) (e2, rho2)) ->
    Disjoint var (bound_var_ctx c) (FromList xs) ->
    getlist xs rho1 = Some vs ->
    getlist xs rho2 = Some vs' -> 
    preord_env_P pr cenv (occurs_free (c |[ e1 ]|)) k rho1 rho2 ->
    preord_exp pr cenv k (c |[ e1 ]|, rho1) (c |[ e2 ]|, rho2).
  Proof.
    intros.
    eapply preord_exp_compat_vals_le; eauto.
  Qed.


      Corollary preord_exp_compat_stem_val x k val rho1 rho2 c e1 e2 :
    (forall k rho1 rho2, preord_env_P pr cenv (occurs_free e1) k rho1 rho2 ->
                         M.get x rho1 = Some val ->                         
                         preord_exp pr cenv k (e1, rho1) (e2, rho2)) ->
    ~ bound_stem_ctx c x ->
    M.get x rho1 = Some val ->  
    preord_env_P pr cenv (occurs_free (c |[ e1 ]|)) k rho1 rho2 ->
    preord_exp pr cenv k (c |[ e1 ]|, rho1) (c |[ e2 ]|, rho2).
  Proof.
    intros.
    eapply preord_exp_compat_vals_stem_set with (S := Singleton _ x); auto.
    intros.
    apply H. auto. specialize (H5 x). rewrite <- H1.
    symmetry. apply H5.
    constructor.
    split. intro. intro. apply H0.
    inv H3. inv H5. auto.
  Qed.

    Corollary preord_exp_compat_val x k val rho1 rho2 c e1 e2 :
    (forall k rho1 rho2, preord_env_P pr cenv (occurs_free e1) k rho1 rho2 ->
                         M.get x rho1 = Some val ->                         
                         preord_exp pr cenv k (e1, rho1) (e2, rho2)) ->
    ~ bound_var_ctx c x ->
    M.get x rho1 = Some val ->  
    preord_env_P pr cenv (occurs_free (c |[ e1 ]|)) k rho1 rho2 ->
    preord_exp pr cenv k (c |[ e1 ]|, rho1) (c |[ e2 ]|, rho2).
    Proof.
     intros. eapply preord_exp_compat_stem_val; eauto.
     intro; apply H0.
     apply bound_stem_var. auto.
    Qed.
  
  

Theorem  name_fds_same: forall x fds,
                          name_in_fundefs fds x <->                
                          List.In x (all_fun_name fds).
Proof.
  induction fds; split; intros.
  - simpl in H. inversion H; subst.
    inversion H0; subst.
    constructor; auto.
    rewrite IHfds in H0.
    constructor 2. auto.
  - simpl.
    simpl in H.
    inversion H.
    subst; left; auto.
    right.
    apply IHfds. auto.
  - inversion H.
  - inversion H.
Qed.

    Theorem same_name_in_fun: forall f,
      Same_set _ (name_in_fundefs f) (FromList (all_fun_name f)).
    Proof.
      intro.
      split; intro; intro; apply name_fds_same; auto.
    Qed.


  Theorem rw_case_local:
    forall (k0 : nat) c0 vs e cl x (rho0 rho3 : env),
  preord_env_P pr cenv (occurs_free (Ecase x cl)) k0 rho0 rho3 ->
  findtag cl c0 = Some e ->
  M.get x rho0 = Some (Vconstr c0 vs) ->
  preord_exp pr cenv k0 (Ecase x cl, rho0) (e, rho3).
  Proof.
    intros; intro; intros.
    inversion H3; subst.
    rewrite H1 in H6. inversion H6; subst.
    rewrite H9 in H0; inversion H0; subst.
    eapply preord_exp_refl; eauto.
    eapply preord_env_P_antimon.
    apply H.
    eapply occurs_free_Ecase_Included.
    apply findtag_In_patterns. eauto.
  Qed.
    
    
   
  Theorem rw_case_equiv: forall cl c0 e x c ys rho1 rho2 k,
      findtag cl c0 = Some e ->
      ~bound_stem_ctx c x ->
      preord_env_P pr cenv (occurs_free (Econstr x c0 ys (c |[ Ecase x cl ]|))) k rho1 rho2 ->
      preord_exp pr cenv k (Econstr x c0 ys (c |[ Ecase x cl ]|), rho1) (Econstr x c0 ys (c |[ e ]|), rho2). 
  Proof.
    intros; intro; intros. inversion H3; subst.
    assert (Hl : Included var (FromList ys) (occurs_free (Econstr x c0 ys (c |[ Ecase x cl ]|)))).  rewrite occurs_free_Econstr. left; auto.
    assert (H11' := preord_env_P_getlist_l _ _ _ _ _ _ _ _ H1 Hl H11). destructAll.
    eapply preord_exp_compat_stem_val in H13; eauto.
    destructAll.
    eexists. eexists.
    split. eapply BStep_constr; eauto. auto.
    intros. eapply rw_case_local; eauto.
    rewrite M.gss. reflexivity.
    apply preord_env_P_extend. eapply preord_env_P_antimon. apply H1. intro. intros. rewrite occurs_free_Econstr. right. auto.
    rewrite preord_val_eq. simpl. split; auto.  apply Forall2_Forall2_asym_included; auto. 
  Qed.

  (* rename a single applied occurence of a variable to *)
  Inductive rename_loc:  var -> var -> exp -> exp -> Prop :=
  | r_Econstr: forall x y v c l l' e, rename_loc x y (Econstr v c (l++(x::l')) e) (Econstr v c (l++(y::l')) e)
  | r_Ecase: forall x y cl, rename_loc x y (Ecase x cl) (Ecase y cl)
  | r_Eproj: forall x y v t n e, rename_loc x y (Eproj v t n x e) (Eproj v t n y e)
  | r_Eprim: forall x y f v ys ys' e, rename_loc x y (Eprim v f (ys++(x::ys')) e) (Eprim v f (ys++(y::ys')) e)
  | r_Eapp1: forall x y t args, rename_loc x y (Eapp x t args) (Eapp y t args)
  | r_Eapp2: forall x y v t l l', rename_loc x y (Eapp v t (l++(x::l'))) (Eapp v t (l++(y::l'))) 
  | r_Ehalt: forall x y, rename_loc x y (Ehalt x) (Ehalt y).

  Inductive rename_glob: var -> var -> exp -> exp -> Prop :=
  | Ctx_r: forall x y e e' c,
      rename_loc x y e e' ->
    rename_glob x y (c|[e ]|) (c|[e']|).

  Inductive rename_fds_glob: var -> var -> fundefs -> fundefs -> Prop :=
  | Ctx_fds_r: forall x y e e' f,
                 rename_loc x y e e' ->
                 rename_fds_glob x y (f <[ e ]>) (f <[ e' ]>).
  
  Definition rename_clos x y := clos_refl_trans exp (rename_glob x y).
  Definition rename_fds_clos x y :=clos_refl_trans fundefs (rename_fds_glob x y).


  (* alternative def. of rename_clos which only admits unshadowed renames *)
  Inductive rename_glob_s: var -> var -> exp -> exp -> Prop :=
  | Ctx_rs: forall x y e e' c,
      rename_loc x y e e' ->
      ~ bound_stem_ctx c x -> 
    rename_glob_s x y (c|[e ]|) (c|[e']|).

  Inductive rename_fds_glob_s: var -> var -> fundefs -> fundefs -> Prop :=
  | Ctx_fds_rs: forall x y e e' f,
      rename_loc x y e e' ->
      ~ bound_stem_fundefs_ctx f x ->
                 rename_fds_glob_s x y (f <[ e ]>) (f <[ e' ]>).
  
  Definition rename_clos_s x y := clos_refl_trans exp (rename_glob_s x y).
  Definition rename_fds_clos_s x y :=clos_refl_trans fundefs (rename_fds_glob_s x y).


  Theorem rename_clos_s_included:
    forall x y e e',
      rename_clos_s x y e e' ->
      rename_clos x y e e'.
  Proof.
    intros. induction H.
    - inv H. constructor. constructor. auto.
    - apply rt_refl.
    - eapply rt_trans; eauto.
  Qed.
      
  Theorem rename_loc_refl_x:
    forall {x} {e e'},
    rename_loc x x e e' ->
    e = e'.
  Proof.
    intros. inversion H; subst; reflexivity.
  Qed.    

  Theorem rename_loc_refl_e:
    forall {x x'} {e},
    rename_loc x x' e e ->
    x = x'.
  Proof.
    intros. inv H; try reflexivity.
    apply app_inv_head in H4. inv H4; auto. 
    apply app_inv_head in H4. inv H4; auto.
    apply app_inv_head in H4. inv H4; auto.
  Qed.


  
  Theorem rename_loc_occurs_free:
    forall {x y} {e e'},
      rename_loc x y e e' ->
      occurs_free e x.
  Proof.
    intros. inv H.
    - apply occurs_free_Econstr.
      left. 
      rewrite FromList_app.
      right; constructor. auto.
    - apply Free_Ecase1. 
    - apply occurs_free_Eproj. left.
      constructor.
    - apply occurs_free_Eprim.
      left.
      rewrite FromList_app.
      right. constructor; auto.
    - apply occurs_free_Eapp. right; constructor.
    - apply occurs_free_Eapp.
      left.
      rewrite FromList_app. right.
      constructor; auto.
    - apply occurs_free_Ehalt. constructor.
  Qed.


  Theorem rename_context_clos:
    forall x y e e',
    rename_clos x y e e' ->      
    forall c,
    rename_clos x y (c |[e ]| ) (c|[e']|).
  Proof.
    intros x y e e' H.
    induction H.
    - intro.
      inversion H; subst.
      apply rt_step.
      rewrite app_ctx_f_fuse.
      rewrite app_ctx_f_fuse.
      constructor. auto.
    - intro. apply rt_refl.
    - intro.
      specialize (IHclos_refl_trans1 c).
      specialize (IHclos_refl_trans2 c).
      eapply rt_trans; eauto.
  Qed.

 

    
  Theorem rename_context_fds_clos:
    forall x y e e',
      rename_clos x y e e' ->
                  forall cfds,
                    rename_fds_clos x y  (cfds <[ e ]>) (cfds <[e' ]>).
    intros x y e e' H.
    induction H.
    - intro.
      inversion H; subst.
      apply rt_step.      
      rewrite app_f_ctx_f_fuse.
      rewrite app_f_ctx_f_fuse.
      constructor. auto.
    - intro. apply rt_refl.
    - intro.
      specialize (IHclos_refl_trans1 cfds).
      specialize (IHclos_refl_trans2 cfds).
      eapply rt_trans; eauto.
  Qed.


    Theorem rename_context_clos_s:
    forall x y e e',
    rename_clos_s x y e e' ->      
    forall c,
      ~ bound_stem_ctx c x ->
    rename_clos_s x y (c |[e ]| ) (c|[e']|).
  Proof.
    intros x y e e' H.
    induction H.
    - intro; intro.
      inversion H; subst.
      apply rt_step.
      rewrite app_ctx_f_fuse.
      rewrite app_ctx_f_fuse.
      constructor. auto.
      intro. apply bound_stem_comp_ctx_mut in H3.
      inv H3; auto.      
    - intro; intro. apply rt_refl.
    - intro; intro.
      specialize (IHclos_refl_trans1 c H1).
      specialize (IHclos_refl_trans2 c H1).
      eapply rt_trans; eauto.
  Qed.

 

    
  Theorem rename_context_fds_clos_s:
    forall x y e e',
      rename_clos_s x y e e' ->
      forall cfds,
        ~ bound_stem_fundefs_ctx cfds x ->
                    rename_fds_clos_s x y  (cfds <[ e ]>) (cfds <[e' ]>).
  Proof.
    intros x y e e' H.
    induction H.
    - intro; intro.
      inversion H; subst.
      apply rt_step.      
      rewrite app_f_ctx_f_fuse.
      rewrite app_f_ctx_f_fuse.
      constructor. auto.
      intro. apply bound_stem_comp_ctx_mut in H3.
      inv H3; auto.      
    - intro; intro. apply rt_refl.
    - intro; intro.
      specialize (IHclos_refl_trans1 cfds H1).
      specialize (IHclos_refl_trans2 cfds H1).
      eapply rt_trans; eauto.
  Qed.


  
  Section inv_app_ctx.

    Theorem inv_app_Hole:
      forall e, e = Hole_c |[ e ]|.
                                 Proof. auto.
                                 Qed.

    Theorem inv_app_Econstr:
      forall x t  ys e,
        Econstr x t ys e = Econstr_c x t ys Hole_c  |[ e ]|.
                                                          Proof. auto.
                                                          Qed.

    Theorem inv_app_Eproj:
      forall x t n y e,
        Eproj x t n y e = Eproj_c x t n y Hole_c |[ e ]|. 
                                                       Proof.
                                                         auto.
                                                       Qed.

    Theorem inv_app_Eprim:
      forall x f ys e,
               Eprim x f ys e = Eprim_c x f ys Hole_c |[ e ]|. 
                                                            Proof.
                                                              auto.
                                                            Qed.

    Theorem inv_app_Ecase:
      forall x te t te' e,
        Ecase x (te ++ (t, e) :: te') = Ecase_c x te t Hole_c te' |[e]|.
                                                                      Proof.
                                                                        auto.
                                                                      Qed.

    Theorem inv_app_Efun1:
      forall e fds,
             Efun fds e = Efun1_c fds Hole_c |[e]|.
                                                 Proof. auto. Qed.
    Theorem inv_app_Efun2:  forall f e e',
                               (Efun (f <[ e ]>) e') = Efun2_c f e' |[ e]|.
Proof. auto.
Qed.                                                              


    
    Theorem inv_app_Fcons1:
      forall f t ys e fds,
        Fcons f t ys e fds = Fcons1_c f t ys Hole_c fds <[ e ]>.
Proof. auto.
Qed.                                                              

                                                              
    Theorem inv_app_Fcons2:  forall z t ys e0 f e,
                               (Fcons z t ys e0 (f <[ e ]>)) = (Fcons2_c z t ys e0 f) <[ e]>.
Proof. auto.
Qed.                                                              
                                                              
  End inv_app_ctx.
  
  Theorem rename_fds_Fcons2:
    forall x y f f',
      rename_fds_clos x y f f' ->
      forall z t ys e,
        rename_fds_clos x y (Fcons z t ys e f) (Fcons z t ys e f').
  Proof.
    intros x y f f' H.
    induction H.
    - inversion H; subst.
    intros. constructor.
    do 2 (rewrite inv_app_Fcons2).
    constructor. auto.
    - intros. apply rt_refl.
    - intros.
      specialize (IHclos_refl_trans1 z0 t ys e).
      specialize (IHclos_refl_trans2 z0 t ys e).
      eapply rt_trans; eauto.
  Qed.

  Theorem rename_fds_Fcons2_s:
    forall x y f f',
      rename_fds_clos_s x y f f' ->
      forall z t ys e,
        rename_fds_clos_s x y (Fcons z t ys e f) (Fcons z t ys e f').
  Proof.
    intros x y f f' H.
    induction H.
    - inversion H; subst.
    intros. constructor.
    do 2 (rewrite inv_app_Fcons2).
    constructor. auto.
    intro. inv H2. auto.
    - intros. apply rt_refl.
    - intros.
      specialize (IHclos_refl_trans1 z0 t ys e).
      specialize (IHclos_refl_trans2 z0 t ys e).
      eapply rt_trans; eauto.
  Qed.

  
Theorem rename_fds_Efun:
      forall x y f f',
      rename_fds_clos x y f f' ->
      forall e,
        rename_clos x y (Efun f e) (Efun f' e).
Proof.
    intros x y f f' H.
    induction H.
    - intro.
      inv H.
      constructor.
      do 2 (rewrite inv_app_Efun2).
      constructor.
      auto.
      - intro.
      apply rt_refl.
    - intro.
      specialize (IHclos_refl_trans1 e).
      specialize (IHclos_refl_trans2 e).
      eapply rt_trans; eauto.
Qed.

Theorem name_in_fundefs_clos_s:
  forall x y z f f',
  rename_fds_clos_s x y f f' ->
  ~ name_in_fundefs f z ->
  ~ name_in_fundefs f' z.
Proof.
  intros. induction H.
  - inv H.
    intro. apply H0.
    apply name_in_fundefs_ctx_ctx. apply name_in_fundefs_ctx_ctx in H. auto.
  - auto.
  - eauto.
Qed.

Theorem rename_fds_Efun_s:
      forall x y f f',
        rename_fds_clos_s x y f f' ->
        ~ name_in_fundefs f x ->
      forall e,
        rename_clos_s x y (Efun f e) (Efun f' e).
Proof.
    intros x y f f' H.
    induction H.
    - intro.
      inv H.
      constructor.
      do 2 (rewrite inv_app_Efun2).
      constructor.
      auto.
      intro. inv H.
      apply H0. apply name_in_fundefs_ctx_ctx. auto.
      auto.      
    - intro; intro.
      apply rt_refl.
    - intro; intro.
      specialize (IHclos_refl_trans1 H1 e).
      eapply rt_trans.
      eauto. apply IHclos_refl_trans2.
      eapply name_in_fundefs_clos_s. apply H. auto.
Qed.



Theorem apply_r_list_end: forall x y l,
  apply_r_list (M.set x y (M.empty var)) (l++[x]) = apply_r_list (M.set x y (M.empty var)) (l++[y]).
Proof.
  induction l.
  simpl. unfold apply_r. rewrite M.gss. destruct (var_dec y x).
  subst. rewrite M.gss. auto.
  rewrite M.gso by auto. rewrite M.gempty.
  auto.
  simpl. rewrite IHl.
  auto.
Qed.




Lemma rename_clos_s_constr_l': forall x y v p e l' l ,
                                rename_clos_s x y (Econstr v p (l++l') e) (Econstr v p (l++(apply_r_list (M.set x y (M.empty var)) l')) e).
  Proof.
    induction l'.
    - simpl. intro. apply rt_refl.
    - simpl.
      intro.      
      unfold apply_r.
      destruct (var_dec x a).
      + subst.
        rewrite M.gss.
        eapply rt_trans.
        constructor.
        rewrite  inv_app_Hole at 1.
        constructor.
        constructor.
        intro. inv H.
        specialize (IHl' (l++[y])).
        rewrite <- app_assoc in IHl'.
        rewrite <- app_assoc in IHl'.
        simpl in IHl'. simpl.
        apply IHl'.
      + rewrite M.gso by auto.
        rewrite M.gempty.
        specialize (IHl' (l++[a])).
        rewrite <- app_assoc in IHl'.
        rewrite <- app_assoc in IHl'.
        simpl in IHl'. apply IHl'.
  Qed.

  Theorem rename_clos_s_constr_l: forall x y v p e l ,
                                rename_clos_s x y (Econstr v p l e) (Econstr v p (apply_r_list (M.set x y (M.empty var)) l) e).
  Proof.
    intros. apply rename_clos_s_constr_l' with (l := nil).
  Qed.
  
Theorem rename_clos_s_prim_l': forall x y v p e l' l,
                                rename_clos_s x y (Eprim v p (l++l') e) (Eprim v p (l++(apply_r_list (M.set x y (M.empty var)) l')) e).
  Proof.
    induction l'.
    - simpl. intro. apply rt_refl.
    - simpl.
      intro.      
      unfold apply_r.
      destruct (var_dec x a).
      + subst.
        rewrite M.gss.
        eapply rt_trans.
        constructor.
        rewrite  inv_app_Hole at 1.
        constructor.
        constructor.
        intro. inv H.
        specialize (IHl' (l++[y])).
        rewrite <- app_assoc in IHl'.
        rewrite <- app_assoc in IHl'.
        simpl in IHl'. simpl.
        apply IHl'.
      + rewrite M.gso by auto.
        rewrite M.gempty.
        specialize (IHl' (l++[a])).
        rewrite <- app_assoc in IHl'.
        rewrite <- app_assoc in IHl'.
        simpl in IHl'. apply IHl'.
  Qed.

  Theorem rename_clos_s_prim_l: forall x y v p e  l,
                                rename_clos_s x y (Eprim v p l e) (Eprim v p (apply_r_list (M.set x y (M.empty var)) l) e).
Proof.    
  intros.
  apply rename_clos_s_prim_l' with (l := nil).
Qed.

Theorem rename_clos_s_app_l': forall x y f c l' l,
                                rename_clos_s x y (Eapp f c (l++l')) (Eapp f c (l++(apply_r_list (M.set x y (M.empty var)) l'))).
  Proof.
    induction l'.
    - simpl. intro. apply rt_refl.
    - simpl.
      intro.      
      unfold apply_r.
      destruct (var_dec x a).
      + subst.
        rewrite M.gss.
        eapply rt_trans.
        constructor.
        rewrite  inv_app_Hole at 1.
        constructor.
        constructor.
        intro. inv H.
        specialize (IHl' (l++[y])).
        rewrite <- app_assoc in IHl'.
        rewrite <- app_assoc in IHl'.
        simpl in IHl'. simpl.
        apply IHl'.
      + rewrite M.gso by auto.
        rewrite M.gempty.
        specialize (IHl' (l++[a])).
        rewrite <- app_assoc in IHl'.
        rewrite <- app_assoc in IHl'.
        simpl in IHl'. apply IHl'.
  Qed.

Theorem rename_clos_s_app_l: forall x y f c  l,
                                rename_clos_s x y (Eapp f c l) (Eapp f c (apply_r_list (M.set x y (M.empty var)) l)).
Proof.  
  intros.
  apply rename_clos_s_app_l' with (l := nil).
Qed.  

Theorem rename_clos_is_case_r: forall x y r y0,
                                 rename_clos x y r y0 ->
                                 forall v l, r = (Ecase v l) ->
                                                   exists v' l', y0 = Ecase v' l'. 
Proof.
  intros x y r y0 H.
  induction H; intros.
  - rewrite  H0 in H.
    inv H. destruct c; inv H1.
    simpl in H.
    destruct e; inv H.
    inv H4.
    exists y, l; auto.
    eexists; eexists. simpl. auto.
  - eexists; eexists; eauto.
  - apply IHclos_refl_trans1 in H1.
    destruct H1.
    destruct H1.
    apply IHclos_refl_trans2 in H1.
    apply H1.
Qed.

Theorem rename_clos_is_case_l: forall x y r y0,
                                 rename_clos x y y0 r ->
                                 forall v l, r = (Ecase v l) ->
                                                   exists v' l', y0 = Ecase v' l'. 
Proof.
  intros x y r y0 H.
  induction H; intros.
  - rewrite  H0 in H.
    inv H. destruct c; inv H1.
    simpl in H.
    destruct e'; inv H.
    inv H5.
    exists x, l; auto.
    eexists; eexists. simpl. auto.
  - eexists; eexists; eauto.
  - apply IHclos_refl_trans2 in H1.
    destruct H1.
    destruct H1.
    apply IHclos_refl_trans1 in H1.
    apply H1.
Qed.



Theorem rename_clos_case_l: forall x y r r' ,
                              rename_clos x y r r' ->
                              forall v v' l l',
                              r = (Ecase v l) ->
                              r' = (Ecase v' l') ->
                              forall a c e,
  rename_clos x y
    (Ecase a ((c, e) :: l))
    (Ecase a ((c, e) :: l')).
Proof.
  intros x y r r' H.
  induction H; intros; subst.
  - inversion H; subst.
   destruct c0; try inv H0.
    + simpl in *. subst.
      inv H4.
      apply rt_refl.
    + 
      assert  (Ecase_c a ((c,e)::l0) c0 c1 l1 |[ e' ]| = Ecase a ((c,e)::l')).
      {
        simpl.
        simpl in H3.
        inv H3.
        reflexivity.
      }
      rewrite <- H0.
      replace ((c, e) :: l0 ++ (c0, c1 |[ e0 ]|) :: l1) with (((c, e) :: l0) ++ (c0, c1 |[ e0 ]|) :: l1).      
      rewrite inv_app_Ecase.
      rewrite app_ctx_f_fuse.
      simpl comp_ctx_f.
      apply rt_step.
      constructor. auto.
      reflexivity.
  - inv H0. apply rt_refl.
  - assert (H0' := H0).
    eapply rename_clos_is_case_l in H0'.
    Focus 2.
    eauto.
    destructAll.        
    specialize (IHclos_refl_trans2 x0 v' x1 l'). 
    specialize (IHclos_refl_trans1 v x0 l x1).
    eapply rt_trans.
    apply IHclos_refl_trans1; auto.
    apply IHclos_refl_trans2; auto.
Qed.

Theorem rename_clos_s_case_l: forall x y r r' ,
                              rename_clos_s x y r r' ->
                              forall v v' l l',
                              r = (Ecase v l) ->
                              r' = (Ecase v' l') ->
                              forall a c e,
  rename_clos_s x y
    (Ecase a ((c, e) :: l))
    (Ecase a ((c, e) :: l')).
Proof.
  intros x y r r' H.
  induction H; intros; subst.
  - inversion H; subst.
    destruct c0; try inv H0.
    + simpl in *. subst.
      inv H4.
      apply rt_refl.
    + 
      assert  (Ecase_c a ((c,e)::l0) c0 c1 l1 |[ e' ]| = Ecase a ((c,e)::l')).
      {
        simpl.
        simpl in H1.
        inv H1.
        reflexivity.
      }
      rewrite <- H0.
      replace ((c, e) :: l0 ++ (c0, c1 |[ e0 ]|) :: l1) with (((c, e) :: l0) ++ (c0, c1 |[ e0 ]|) :: l1).      
      rewrite inv_app_Ecase.
      rewrite app_ctx_f_fuse.
      simpl comp_ctx_f.
      apply rt_step.
      constructor. auto.
      intro. apply H5. inv H2. constructor; auto.
      reflexivity.
  - inv H0. apply rt_refl.
  - assert (H0' := H0).
    apply rename_clos_s_included in H0'. 
    eapply rename_clos_is_case_l in H0'. 
    Focus 2.
    eauto.
    destructAll.        
    specialize (IHclos_refl_trans2 x0 v' x1 l'). 
    specialize (IHclos_refl_trans1 v x0 l x1).
    eapply rt_trans.
    apply IHclos_refl_trans1; auto.
    apply IHclos_refl_trans2; auto.
Qed.



Theorem rename_clos_case: forall (v a x y:var) l c e e' l',
  rename_clos x y (Ecase v l) (Ecase v l') ->
  rename_clos x y e e' ->  
  rename_clos x y
    (Ecase a ((c, e) :: l))
    (Ecase a ((c, e') :: l')).
Proof.
  intros.
  eapply rt_trans.
  replace ((c,e)::l) with ([] ++ (c,e)::l) by auto.
  rewrite inv_app_Ecase.
  apply rename_context_clos.
  apply H0.
  simpl.
  eapply rename_clos_case_l.
  apply H. reflexivity. reflexivity.
Qed.

Theorem rename_clos_s_case: forall (v a x y:var) l c e e' l',
  rename_clos_s x y (Ecase v l) (Ecase v l') ->
  rename_clos_s x y e e' ->  
  rename_clos_s x y
    (Ecase a ((c, e) :: l))
    (Ecase a ((c, e') :: l')).
Proof.
  intros.
  eapply rt_trans.
  replace ((c,e)::l) with ([] ++ (c,e)::l) by auto.
  rewrite inv_app_Ecase.
  apply rename_context_clos_s.
  apply H0.
  intro. inv H1. inv H8.
  simpl.
  eapply rename_clos_s_case_l.
  apply H. reflexivity. reflexivity.
Qed.



Theorem rename_case_one_step:
  forall x y r r',
    rename_clos x y r r' ->
    forall v v' l l',
      r = (Ecase v l) ->
      r' = (Ecase v' l') ->
      forall a, 
      rename_clos x y (Ecase a l) (Ecase a l').
Proof.
  intros x y r r' H.
  induction H; intros.
  - subst.
    inv H.
    destruct c; inv H0.
    + simpl in *; subst.
      inv H4. apply rt_refl.
    + simpl in H3. inv H3.
      rewrite inv_app_Ecase.
      rewrite inv_app_Ecase.
      apply rt_step.
      rewrite app_ctx_f_fuse.
      rewrite app_ctx_f_fuse.
      constructor. apply H4.      
  -   subst. inv H0. apply rt_refl.
  - subst.
    assert (H0' := H0).
    eapply rename_clos_is_case_l in H0'.
    2: reflexivity.
    destruct H0'. destruct H1.
    specialize (IHclos_refl_trans2 x0 v' x1 l' H1).
    specialize (IHclos_refl_trans1 v x0 l x1).
    eapply rt_trans.
    apply IHclos_refl_trans1; auto.
    apply IHclos_refl_trans2. reflexivity.
Qed.

Theorem rename_case_one_step_s:
  forall x y r r',
    rename_clos_s x y r r' ->
    forall v v' l l',
      r = (Ecase v l) ->
      r' = (Ecase v' l') ->
      forall a, 
      rename_clos_s x y (Ecase a l) (Ecase a l').
Proof.
  intros x y r r' H.
  induction H; intros.
  - subst.
    inv H.
    destruct c; inv H0.
    + simpl in *; subst.
      inv H4. apply rt_refl.
    + simpl in H1. inv H1.
      rewrite inv_app_Ecase.
      rewrite inv_app_Ecase.
      apply rt_step.
      rewrite app_ctx_f_fuse.
      rewrite app_ctx_f_fuse.
      constructor. apply H4.
      intro. apply H5. constructor. inv H; auto.
  -   subst. inv H0. apply rt_refl.
  - subst.
    assert (H0' := H0).
    apply rename_clos_s_included in H0'. 
    eapply rename_clos_is_case_l in H0'.
    2: reflexivity.
    destruct H0'. destruct H1.
    subst.
    specialize (IHclos_refl_trans2 x0 v' x1 l' eq_refl eq_refl).
    specialize (IHclos_refl_trans1 v x0 l x1 eq_refl eq_refl).
    eapply rt_trans.
    apply IHclos_refl_trans1; auto.
    apply IHclos_refl_trans2. 
Qed.


Theorem apply_r_none:
  forall v sigma,
    M.get v sigma = None ->
    apply_r sigma v = v. 
Proof.
  intros. unfold apply_r.
  unfold M.get in H. unfold M.get. rewrite H.
  reflexivity.
Qed.

Theorem apply_r_some: forall v y sigma,
                       M.get v sigma = Some y ->
                       apply_r sigma v = y.
Proof.
  intros. unfold apply_r.
  unfold M.get in *. rewrite H. reflexivity.
Qed.  

Theorem apply_r_set2: forall x v y sigma,
                        x <> v ->
                        apply_r (M.set x y sigma) v = apply_r sigma v.
Proof.
  intros. unfold apply_r. rewrite M.gso by auto. auto.
Qed.

Theorem num_occur_arl:
  forall x y l,
    x <> y ->
  num_occur_list (apply_r_list (M.set x y (M.empty var)) l) x = 0.
Proof.
  induction l; intros.
  auto.
  simpl. rewrite IHl; auto.
  destruct (var_dec x a).
  + subst. erewrite apply_r_some by apply M.gss.
    destruct (cps_util.var_dec a y). exfalso; auto. auto.
  + rewrite apply_r_none. 
    destruct (cps_util.var_dec x a). exfalso; auto. auto.
    rewrite M.gso by auto. apply M.gempty.
Qed.


Theorem not_in_sig_rem: forall sigma (x v:var),
  ~ (exists z, M.get z sigma = Some x) ->
~ (exists z, M.get z (M.remove v sigma) = Some x).
Proof.
  intros. intro. destruct H0.
  destruct (var_dec x0 v).
  subst. rewrite M.grs in H0. inversion H0.
  rewrite M.gro in H0; auto. apply H. exists x0; auto.
Qed.

Theorem not_in_sig_list_rem:
  forall  x l sigma,
  ~ (exists z, M.get z sigma = Some x) -> 
  ~ (exists z : M.elt, M.get z (remove_all sigma l) = Some x).
Proof.
  induction l; intros.
  simpl. auto.
  simpl.
  apply IHl.
  apply not_in_sig_rem.
  auto.
Qed.

Theorem apply_r_not_in_sig: forall x v sigma,
    ~ (exists z : M.elt, M.get z sigma = Some x) ->
  x <> v -> x <> apply_r sigma v.
Proof.
  intros.
  unfold apply_r.
  destruct (M.get v sigma) eqn:gvs.
  intro; subst. apply H. exists v; auto.
  auto.
Qed.

Theorem remove_all_none: forall x l sigma,
     M.get x sigma = None ->
     M.get x (remove_all sigma l) = None.
Proof.
  induction l.
  intros. simpl. auto.
  intros.
  apply IHl. apply gr_none. auto.
Qed.   


Theorem one_rename_all_ar: forall x y v sigma,
    ~ (exists z, M.get z sigma = Some x) ->
    (M.get x sigma = None) ->                              
  apply_r (M.set x y sigma) v =   (apply_r (M.set x y (M.empty var)) (apply_r sigma v)).
Proof.
  intros.
  destruct (var_dec x v).
  + subst. erewrite apply_r_some by apply M.gss.
    rewrite apply_r_none with (v := v); auto.
    erewrite apply_r_some by apply M.gss.
    auto.
  + rewrite apply_r_set2; auto.
    rewrite apply_r_set2; auto.
    rewrite apply_r_empty; auto.
    apply apply_r_not_in_sig; auto.
Qed.    
    
Theorem one_rename_all_list: forall y x l sigma,
                               ~ (exists z, M.get z sigma = Some x) ->
                               (M.get x sigma = None) ->                              
                               apply_r_list (M.set x y sigma) l =  (apply_r_list (M.set x y (M.empty var)) (apply_r_list sigma l)).
Proof.
  induction l; intros.
  reflexivity.
  simpl.
  rewrite IHl; auto.
  destruct (var_dec x a).
  - subst.
    erewrite apply_r_some by apply M.gss.
    erewrite apply_r_none with (v := a); auto.
    erewrite apply_r_some by apply M.gss.
    reflexivity.
  - rewrite apply_r_set2; auto.
    rewrite apply_r_set2; auto. rewrite apply_r_empty.
    auto.
    apply apply_r_not_in_sig; auto.
Qed.
Theorem one_rename_all_ar': forall x y v sigma,
    (M.get y sigma = None) ->                              
  apply_r (M.set x y sigma) v = apply_r sigma (apply_r (M.set x y (M.empty var)) v).
Proof.
  intros.
  destruct (var_dec x v).
  + subst. erewrite apply_r_some by apply M.gss.
    erewrite apply_r_some with (v := v) by apply M.gss.
    rewrite apply_r_none with (v := y); auto.
  + rewrite apply_r_set2; auto.
    rewrite apply_r_set2; auto.
    rewrite apply_r_empty; auto.
Qed.     

Theorem one_rename_all_list': forall y x l sigma,
                               (M.get y sigma = None) ->                              
                               apply_r_list (M.set x y sigma) l =  apply_r_list sigma (apply_r_list (M.set x y (M.empty var))  l).
Proof.
  induction l; intros.
  reflexivity.
  simpl.
  rewrite IHl; auto.
  rewrite one_rename_all_ar'; auto.
Qed.


Lemma all_fun_name_removed: 
  forall f2 sigma,
  (all_fun_name (rename_all_fun (remove_all sigma (all_fun_name f2)) f2)) = all_fun_name f2.
Proof.
  induction f2.
  intros. simpl. rewrite IHf2. reflexivity.
  intros. auto.
Qed.
  
Theorem one_rename_all: forall y  x,
                          ( forall e sigma,
                          ~ (exists z, M.get z sigma = Some x) ->
                          (M.get x sigma = None) ->                              
                            rename_all (M.set x y sigma) e  = rename y x (rename_all sigma e)) /\
                          ( forall f sigma,
                              ~ (exists z, M.get z sigma = Some x) ->
                              (M.get x sigma = None) ->                              
                          rename_all_fun (M.set x y sigma) f = rename_all_fun (M.set x y (M.empty var)) (rename_all_fun sigma f)).
Proof.
  intros y x.
  assert (Hpr := prop_rename_all).
  destruct Hpr as (Hpr1, Hpr2).
  eapply exp_def_mutual_ind; intros; simpl.
  - unfold rename.
    simpl.
    rewrite one_rename_all_list; auto.
    destruct (var_dec x v).
    + subst.
      erewrite Hpr1.
      Focus 2. apply remove_set_1.
      symmetry.
      erewrite Hpr1.
      Focus 2. eapply smg_trans. apply remove_set_1.
      apply remove_empty.
      rewrite <- (proj1 rename_all_empty).
      reflexivity.
    + erewrite Hpr1.
      Focus 2.
      apply remove_set_2; auto.
      symmetry.
      erewrite Hpr1.
      Focus 2. eapply smg_trans. apply remove_set_2; auto. apply proper_set.
      apply remove_empty.
      rewrite H; auto.
      apply not_in_sig_rem. auto.
      apply gr_none. auto.
  - destruct (var_dec x v).
    + subst.
      erewrite apply_r_some by apply M.gss.
      unfold rename; simpl.
      rewrite apply_r_none with (v := v); auto.
      erewrite apply_r_some by apply M.gss.
      auto.
    + rewrite apply_r_set2 by auto.
      unfold rename. simpl.
      rewrite apply_r_set2. rewrite apply_r_empty. auto.
      apply apply_r_not_in_sig; auto.
  - unfold rename. simpl.
    rewrite <- one_rename_all_ar; auto.
    rewrite H; auto.
    specialize (H0 sigma H1 H2).
    unfold rename in H0.
    simpl in H0.
    inv H0. reflexivity.
  - unfold rename. simpl.
    destruct (var_dec x v0).
    subst.
    + erewrite apply_r_some by (apply M.gss).
      rewrite apply_r_none with (v := v0); auto.
      erewrite apply_r_some by (apply M.gss).
      destruct (var_dec v v0).
      subst.      
      erewrite Hpr1.
      Focus 2. apply remove_set_1.
      symmetry.
      erewrite Hpr1.
      Focus 2.
      eapply smg_trans.
      apply remove_set_1.
      apply remove_empty.
      rewrite <- (proj1 rename_all_empty).
      reflexivity.
      erewrite Hpr1. Focus 2. apply remove_set_2; auto.
      symmetry.
      erewrite Hpr1. Focus 2. eapply smg_trans. apply remove_set_2; auto. apply proper_set. apply remove_empty.
      rewrite H. unfold rename. reflexivity.
      intro. apply H0. destruct H2.
      destruct (var_dec x v). subst. rewrite M.grs in H2. inversion H2.
      rewrite M.gro in H2 by auto. exists x; auto.
      rewrite M.gro by auto.
      auto.
    + rewrite apply_r_set2 by auto.
      assert (apply_r sigma v0 <> x).
      unfold apply_r. 
      destruct (@M.get M.elt v0 sigma) eqn:gv0s.
      intro; subst. apply H0; eauto.
      auto.
      rewrite apply_r_set2 by auto.
      rewrite apply_r_empty.
      destruct (var_dec v x).
      * subst.
        erewrite Hpr1. Focus 2. apply remove_set_1.
        symmetry.
        erewrite Hpr1. Focus 2. eapply smg_trans. apply remove_set_1. apply remove_empty.
        rewrite <- (proj1 rename_all_empty). reflexivity.
      * erewrite Hpr1. Focus 2.
        apply remove_set_2; auto.
        symmetry.
        erewrite Hpr1. Focus 2. eapply smg_trans. apply remove_set_2; auto. apply proper_set. apply remove_empty.
        rewrite H. unfold rename. reflexivity.
        apply not_in_sig_rem. auto.
        apply gr_none; auto.
  - unfold rename. simpl.
    assert (Hid := in_dec).
    specialize (Hid _ var_dec x (all_fun_name f2)).
    rewrite all_fun_name_removed.
    destruct Hid.
    + erewrite Hpr2.
      Focus 2.
      apply remove_all_in. auto.
      erewrite Hpr1.
      Focus 2.
      apply remove_all_in. auto.
      symmetry.
      erewrite Hpr2. Focus 2.
      eapply smg_trans. apply remove_all_in; auto.
      apply remove_all_empty.      
      rewrite <- (proj2 rename_all_empty).
      erewrite Hpr1. Focus 2.
      eapply smg_trans. apply remove_all_in; auto.
      apply remove_all_empty.
      rewrite <- (proj1 rename_all_empty).
      reflexivity.
    + erewrite Hpr2.
      Focus 2.
      apply remove_all_not_in. auto.
      erewrite Hpr1.
      Focus 2.
      apply remove_all_not_in. auto.
      symmetry.
      erewrite Hpr2. Focus 2.
      eapply smg_trans. apply remove_all_not_in; auto.
      apply proper_set. apply remove_all_empty.      
      erewrite Hpr1. Focus 2.
      eapply smg_trans. apply remove_all_not_in; auto.
      apply proper_set.
      apply remove_all_empty.
      rewrite H; auto.
      rewrite H0; auto.
      apply not_in_sig_list_rem; auto.
      apply remove_all_none; auto.
      apply not_in_sig_list_rem; auto.
      apply remove_all_none; auto.
  - unfold rename; subst.
    rewrite one_rename_all_list; auto.
    simpl.
    rewrite one_rename_all_ar; auto.    
  - unfold rename; simpl.
    rewrite <- one_rename_all_list; auto.
    destruct (var_dec v x).
    + subst.
      erewrite Hpr1. Focus 2.
      apply remove_set_1.
      symmetry.
      erewrite Hpr1. Focus 2.
      eapply smg_trans. apply remove_set_1.
      apply remove_empty.
      rewrite <- (proj1 rename_all_empty).
      reflexivity.
    + erewrite Hpr1. Focus 2.
      apply remove_set_2; auto.
      symmetry.
      erewrite Hpr1. Focus 2.
      eapply smg_trans. apply remove_set_2; auto.
      apply proper_set. apply remove_empty.
      rewrite H; auto.
      apply not_in_sig_rem; auto.
      apply gr_none; auto.      
  - unfold rename; simpl.
    destruct (var_dec x v).
    + subst. erewrite apply_r_some by apply M.gss.
      rewrite apply_r_none with (v := v); auto.
      erewrite apply_r_some by apply M.gss. auto.
    + rewrite apply_r_set2 by auto.
      rewrite apply_r_set2.
      rewrite apply_r_empty.
      reflexivity.
      unfold apply_r.
      destruct (@M.get M.elt v sigma) eqn:gvs.
      intro; subst.
      apply H. exists v; auto.
      auto.
  - erewrite <- H0; auto.
    assert (Hid := in_dec).
    specialize (Hid _ var_dec x l).
    destruct Hid.
    * erewrite Hpr1. Focus 2.
      apply remove_all_in. auto.
      symmetry.
      erewrite Hpr1. Focus 2.
      eapply smg_trans.
      apply remove_all_in; auto.
      apply remove_all_empty.
      rewrite <- (proj1 rename_all_empty). auto.
    * erewrite Hpr1.
      Focus 2.
      apply remove_all_not_in; auto.
      symmetry.
      erewrite Hpr1.
      Focus 2.
      eapply smg_trans.
      apply remove_all_not_in; auto.
      apply proper_set.
      apply remove_all_empty.
      rewrite H; auto.
      apply not_in_sig_list_rem. auto.
      apply remove_all_none; auto.
  - reflexivity.
Qed. 

Theorem one_rename_all': forall y  x,
                          ( forall e sigma,
                              (M.get y sigma = None) ->
                            rename_all (M.set x y sigma) e  = (rename_all sigma (rename y x e))) /\
                          ( forall f sigma,
                              (M.get y sigma = None) -> 
                          rename_all_fun (M.set x y sigma) f = rename_all_fun sigma (rename_all_fun (M.set x y (M.empty var)) f)).
Proof.
  
  intros y x.
   assert (Hpr := prop_rename_all).
  destruct Hpr as (Hpr1, Hpr2).
  eapply exp_def_mutual_ind; intros; simpl.
  - rewrite one_rename_all_list'; auto.
    destruct (var_dec x v).
    + subst.
      erewrite Hpr1.
      Focus 2. apply remove_set_1.
      symmetry.
      erewrite Hpr1 with (e := e).
      Focus 2. eapply smg_trans. apply remove_set_1.
      apply remove_empty.
      rewrite <- (proj1 rename_all_empty).
      reflexivity.
    + erewrite Hpr1.
      Focus 2.
      apply remove_set_2; auto.
      symmetry.
      erewrite Hpr1 with (e := e).
      Focus 2. eapply smg_trans. apply remove_set_2; auto. apply proper_set.
      apply remove_empty.
      rewrite H; auto.
      rewrite <- (proj1 rename_all_empty).
      symmetry.
      rewrite H.
      reflexivity.
      apply gr_none; auto.
      apply M.gempty.
  - rewrite one_rename_all_ar'; auto. 
  - 
   unfold rename. simpl.
    rewrite <- one_rename_all_ar'; auto.
    rewrite <- H; auto.
    specialize (H0 sigma H1).
    unfold rename in H0.
    simpl in H0.
    inv H0. reflexivity. 
  - rewrite one_rename_all_ar'; auto.    
    destruct (var_dec x v).
    subst.
    + erewrite Hpr1. Focus 2. apply remove_set_1.
        symmetry.
        erewrite Hpr1 with (e := e). Focus 2. eapply smg_trans. apply remove_set_1. apply remove_empty.
        rewrite <- (proj1 rename_all_empty). reflexivity.
    + erewrite Hpr1. Focus 2.
        apply remove_set_2; auto.
        symmetry.
        erewrite Hpr1 with (e := e). Focus 2. eapply smg_trans. apply remove_set_2; auto. apply proper_set. apply remove_empty.
        
        rewrite <- H. reflexivity. 
        apply gr_none; auto.
  - assert (Hid := in_dec).
    specialize (Hid _ var_dec x (all_fun_name f2)).
    rewrite all_fun_name_removed.
    destruct Hid.
    + erewrite Hpr2.
      Focus 2.
      apply remove_all_in. auto.
      erewrite Hpr1.
      Focus 2.
      apply remove_all_in. auto.
      symmetry.
      erewrite Hpr2 with (fds := f2). Focus 2.
      eapply smg_trans. apply remove_all_in; auto.
      apply remove_all_empty.      
      rewrite <- (proj2 rename_all_empty).
      erewrite Hpr1 with (e := e). Focus 2.
      eapply smg_trans. apply remove_all_in; auto.
      apply remove_all_empty.
      rewrite <- (proj1 rename_all_empty).
      reflexivity.
    + erewrite Hpr2.
      Focus 2.
      apply remove_all_not_in. auto.
      erewrite Hpr1 with (e:= e).
      Focus 2.
      apply remove_all_not_in. auto.
      symmetry.
      erewrite Hpr2 with (fds := f2). Focus 2.
      eapply smg_trans. apply remove_all_not_in; auto.
      apply proper_set. apply remove_all_empty.      
      erewrite Hpr1 with (e := e). Focus 2.
      eapply smg_trans. apply remove_all_not_in; auto.
      apply proper_set.
      apply remove_all_empty.
      rewrite <- H; auto.
      rewrite <- H0; auto.
      apply remove_all_none; auto.
      apply remove_all_none; auto. 
  - unfold rename; subst.
    rewrite one_rename_all_list'; auto.
    simpl.
    rewrite one_rename_all_ar'; auto.    
  - rewrite <- one_rename_all_list'; auto.
    destruct (var_dec v x).
    + subst.
      erewrite Hpr1. Focus 2.
      apply remove_set_1.
      symmetry.
      erewrite Hpr1 with (e := e). Focus 2.
      eapply smg_trans. apply remove_set_1.
      apply remove_empty.
      rewrite <- (proj1 rename_all_empty).
      reflexivity.
    + erewrite Hpr1. Focus 2.
      apply remove_set_2; auto.
      symmetry.
      erewrite Hpr1 with (e := e). Focus 2.
      eapply smg_trans. apply remove_set_2; auto.
      apply proper_set. apply remove_empty.
      rewrite <- H; auto.
      apply gr_none; auto.      
  - rewrite one_rename_all_ar'; auto.
  -  erewrite <- H0; auto.
    assert (Hid := in_dec).
    specialize (Hid _ var_dec x l).
    destruct Hid.
    * erewrite Hpr1. Focus 2.
      apply remove_all_in. auto.
      symmetry.
      erewrite Hpr1 with (e := e). Focus 2.
      eapply smg_trans.
      apply remove_all_in; auto.
      apply remove_all_empty.
      rewrite <- (proj1 rename_all_empty). auto.
    * erewrite Hpr1.
      Focus 2.
      apply remove_all_not_in; auto.
      symmetry.
      erewrite Hpr1 with (e := e).
      Focus 2.
      eapply smg_trans.
      apply remove_all_not_in; auto.
      apply proper_set.
      apply remove_all_empty.
      rewrite <- H; auto.
      apply remove_all_none; auto.
  - reflexivity.
Qed. 




Theorem disjoint_singletons:
  forall v x,
  Disjoint var (Singleton var x) (Singleton var v) ->
  x <> v.
Proof.
  intros. intro; subst. inv H.
  specialize (H0 v).
  apply H0. split; auto.
Qed.

    
Theorem rename_dead_var:
  forall y x,
    y <> x -> 
(forall e, Disjoint _ (bound_var e) (Singleton _ x) ->
           num_occur (rename y x e) x 0) /\
(forall fds,
   Disjoint _ (bound_var_fundefs fds) (Singleton _ x) ->
           num_occur_fds (rename_all_fun (M.set x y (M.empty var))  fds) x 0).
Proof.
  intros y x Hyx.
  eapply exp_def_mutual_ind; intros.
  - rewrite bound_var_Econstr in H0.
    unfold rename. simpl.    
    assert (He := Disjoint_Union_l _ _ _ H0).
    assert (Hv := Disjoint_Union_r _ _ _ H0).
    apply H in He.
    eapply num_occur_n.
    apply Num_occ_constr.
    erewrite (proj1 prop_rename_all). apply He.
    eapply smg_trans.
    apply remove_set_2.
    apply disjoint_singletons.
    auto.
    apply proper_set.
    apply remove_empty.
    rewrite num_occur_arl. auto.
    auto.
  - unfold rename.
    simpl.
    eapply num_occur_n.
    constructor.
    constructor.
    simpl. destruct (var_dec x v).
    + subst.
      erewrite apply_r_some by apply M.gss.
      destruct (cps_util.var_dec v y).
      exfalso; auto.
      auto.
    + rewrite apply_r_none.
      destruct (cps_util.var_dec x v). 
      exfalso; auto.
      auto.
      rewrite M.gso by auto. apply M.gempty.
  - rewrite bound_var_Ecase_cons in H1.
    assert (He := Disjoint_Union_l _ _ _ H1).
    assert (Hv := Disjoint_Union_r _ _ _ H1).
    apply H in He.
    apply H0 in Hv.
    unfold rename in *. simpl in *.
    inv Hv.
    eapply num_occur_n.
    constructor.
    constructor.
    apply He.
    apply H5.
    simpl.
    reflexivity.    
  - rewrite bound_var_Eproj in H0.
    assert (He := Disjoint_Union_l _ _ _ H0).
    assert (Hv := Disjoint_Union_r _ _ _ H0).
    apply disjoint_singletons in Hv.
    apply H in He. clear H.    
    unfold rename.
    simpl.
    eapply num_occur_n.
    constructor.
    erewrite (proj1 prop_rename_all). apply He.
    eapply smg_trans.
    apply remove_set_2; auto.
    apply proper_set.
    apply remove_empty.
    simpl.
    destruct (var_dec x v0).
    + subst.
      erewrite apply_r_some by apply M.gss.
      destruct (cps_util.var_dec v0 y).
      exfalso; auto.
      auto.
    + rewrite apply_r_none.
      destruct (cps_util.var_dec x v0). subst.
      exfalso; auto.
      auto.
      rewrite M.gso by auto. apply M.gempty.
  - rewrite bound_var_Efun in H1.
    assert (Hf := Disjoint_Union_l _ _ _ H1).
    assert (He := Disjoint_Union_r _ _ _ H1).
    apply H in Hf. clear H.
    apply H0 in He; clear H0.
    unfold rename.
    simpl.
    assert (Hfv := Disjoint_Union_l _ _ _ H1).
    assert (~ List.In  x (all_fun_name f2)).
    intro.
    inv Hfv.
    specialize (H0 x).
    apply H0. split.
    apply name_in_fundefs_bound_var_fundefs.
    apply name_fds_same.
    auto.
    constructor.
    eapply num_occur_n. constructor.
    erewrite (proj1 prop_rename_all).
    apply He. 
    eapply smg_trans.
    apply remove_all_not_in. auto. apply proper_set.
    apply remove_all_empty.
    erewrite (proj2 prop_rename_all).
    apply Hf.
    eapply smg_trans.
    apply remove_all_not_in. auto.
    apply proper_set.
    apply remove_all_empty.
    auto.
  - unfold rename.
    simpl.
    eapply num_occur_n.
    apply Num_occ_app.
    simpl.
    destruct (var_dec x v).
    + subst.
      erewrite apply_r_some by apply M.gss.
      destruct (cps_util.var_dec v y).
      exfalso; auto.
      apply num_occur_arl. auto.
    + rewrite apply_r_none.
      destruct (cps_util.var_dec x v). subst.
      exfalso; auto.
      apply num_occur_arl. auto.
      rewrite M.gso by auto. apply M.gempty.
  - rewrite bound_var_Eprim in H0.
    assert (He := Disjoint_Union_l _ _ _ H0).
    assert (Hv := Disjoint_Union_r _ _ _ H0).
    apply disjoint_singletons in Hv.
    unfold rename; subst.
    simpl.
    eapply num_occur_n. constructor.
    erewrite (proj1 prop_rename_all). apply H. auto.
    eapply smg_trans. apply remove_set_2.
    auto.
    apply proper_set.
    apply remove_empty.
    rewrite num_occur_arl. auto. auto.    
  - unfold rename.
    simpl.
    eapply num_occur_n.
    apply Num_occ_halt.
    simpl.
    destruct (var_dec x v).
    + subst.
      erewrite apply_r_some by apply M.gss.
      destruct (cps_util.var_dec v y). exfalso; auto.
      auto.
    + rewrite apply_r_none.
      destruct (cps_util.var_dec x v). exfalso; auto.
      auto.
      rewrite M.gso by auto.
      apply M.gempty.
  - simpl.
    rewrite bound_var_fundefs_Fcons in H1.
    assert (Hf := Disjoint_Union_l _ _ _ H1).
    assert (He := Disjoint_Union_r _ _ _ H1).
    clear H1.
    assert (Hl := Disjoint_Union_l _ _ _ He).
    assert (Hef5 := Disjoint_Union_r _ _ _ He).
    clear He.
    assert (He := Disjoint_Union_l _ _ _ Hef5).
    assert (Hf5 := Disjoint_Union_r _ _ _ Hef5).
    clear Hef5.
    apply H in He. clear H.
    apply H0 in Hf5. clear H0.
    eapply num_occur_fds_n.
    constructor.
    unfold rename in He.
    erewrite <- (proj1 prop_rename_all).
    apply He.
    apply smg_sym.
    eapply smg_trans.
    apply remove_all_not_in.
    intro.
    inv Hl. specialize (H0 x).
    apply H0.
    split; auto.
    apply proper_set. apply remove_all_empty.
    apply Hf5.
    auto.    
  - simpl. constructor.
Qed.


Theorem bound_var_rename_loc:
  forall x y e e',
    rename_loc x y e e' ->
    Same_set _ (bound_var e) (bound_var e').
Proof.
  intros.
  inv H.
  - do 2 (rewrite bound_var_Econstr). reflexivity.
  - induction cl.
    do 2 (rewrite bound_var_Ecase_nil).
    reflexivity.
    destruct a.
    do 2 (rewrite bound_var_Ecase_cons).
    apply Same_set_Union_compat.
    reflexivity.
    auto.
  - do 2 (rewrite bound_var_Eproj). reflexivity.
  - do 2 (rewrite bound_var_Eprim). reflexivity.
  - do 2 (rewrite bound_var_Eapp). reflexivity.
  - do 2 (rewrite bound_var_Eapp). reflexivity.
  - do 2 (rewrite bound_var_Ehalt). reflexivity.
Qed.

Theorem bound_var_rename:
  forall x y e e',
    rename_clos x y e e' ->
    Same_set _ (bound_var e) (bound_var e').
Proof.
  intros. induction H.
  -  inv H.
     apply bound_var_rename_loc in H0.
     apply bound_var_comp. apply H0.
  - reflexivity.
  - etransitivity; eauto.
Qed.  

Theorem bound_var_rename_fds:
  forall x y f f',
    rename_fds_clos x y f f' ->
    Same_set _ (bound_var_fundefs f) (bound_var_fundefs f').
Proof.
  intros.
  induction H.
  - inv H.
    apply bound_var_rename_loc in H0.
    apply bound_var_fundefs_comp. auto.
  -   reflexivity.
  - etransitivity; eauto.
Qed.    

Theorem rename_glob_loc:
  forall x y e e',
   rename_loc x y e e' ->
   rename_glob x y e e'. 
Proof.
  intros.
  rewrite inv_app_Hole.
  rewrite inv_app_Hole with (e := e).
  constructor; auto.
Qed.

Theorem rename_glob_s_loc:
  forall x y e e',
   rename_loc x y e e' ->
   rename_glob_s x y e e'. 
Proof.
  intros.
  rewrite inv_app_Hole.
  rewrite inv_app_Hole with (e := e).
  constructor; auto. intro. inv H0.
Qed.
 About rename_all_fun. 

Transparent rename.
  Theorem rename_corresp: forall y x,
                            (forall e,
                               Disjoint _ (bound_var e) (FromList [y]) ->
                               rename_clos_s x y e (rename y x e)) /\
                            (forall fds,
                                Disjoint _ (bound_var_fundefs fds) (FromList [y]) ->
                                ~ name_in_fundefs fds x ->
                               rename_fds_clos_s x y fds (rename_all_fun (M.set x y (M.empty var)) fds)).
  Proof.
    intros y x. eapply exp_def_mutual_ind; intros; simpl.
    -  unfold rename.
      simpl.
      eapply rt_trans.
      apply rename_clos_s_constr_l.      

      destruct (var_dec v x).
       + subst.         
         replace (rename_all (M.remove x (M.set x y (M.empty var))) e) with (rename_all (M.empty var) e).
         rewrite <- (proj1 rename_all_empty).
         apply rt_refl.
         auto.
         apply prop_rename_all.
         eapply smg_sym.
         eapply smg_trans.
         apply remove_set_1; auto.
         apply remove_empty.
       + do 2 (rewrite inv_app_Econstr).
         apply rename_context_clos_s.                  
         replace (rename_all (M.remove v (M.set x y (M.empty var))) e) with (rename_all (M.set x y (M.empty var)) e).
         apply H; auto.
         rewrite bound_var_Econstr in H0.
         assert (Hde := Disjoint_Union_l _ _ _ H0). auto.      
         apply prop_rename_all.
         apply smg_sym.
         apply remove_none.
         rewrite M.gso; auto. apply M.gempty.
         intro. inv H1; auto. inv H7.
    - unfold rename. simpl. unfold apply_r.
      destruct (var_dec v x).
      + subst. rewrite M.gss. apply rt_step.
        rewrite inv_app_Hole.
      rewrite inv_app_Hole at 1.
      constructor.
      constructor.
      intro. inv H0.
      + rewrite M.gso. rewrite M.gempty. apply rt_refl. auto.        
    - rewrite bound_var_Ecase_cons in H1.
      assert (Hde := Disjoint_Union_l _ _ _ H1).
      assert (Hdv := Disjoint_Union_r _ _ _ H1).
      specialize (H Hde).
      specialize (H0 Hdv).
      unfold rename.
      simpl.
      apply rt_trans with (y:= Ecase (apply_r (M.set x y (M.empty var)) v) ((c,e)::l)).
      unfold apply_r.
      destruct (var_dec x v).
      subst. rewrite M.gss. constructor.
      rewrite inv_app_Hole.
      rewrite inv_app_Hole at 1.
      constructor. constructor. intro. inv H2. 
      rewrite M.gso by auto. rewrite M.gempty.
      apply rt_refl.      
      eapply rename_clos_s_case.
      unfold rename in H0. simpl in H0.
      eapply rename_case_one_step_s.        
      apply H0. reflexivity. reflexivity.         
      apply H. 
    - unfold rename.
      simpl.
      rewrite bound_var_Eproj in H0.      
      assert (Hde := Disjoint_Union_l _ _ _ H0).
      assert (Hdv := Disjoint_Union_r _ _ _ H0).
      apply H in Hde; auto.     
      apply rt_trans with (y := (Eproj v t n (apply_r (M.set x y (M.empty var)) v0) e)).
      unfold apply_r. destruct (var_dec v0 x).
      subst. rewrite M.gss. apply rt_step.
      apply rename_glob_s_loc. constructor.
      rewrite M.gso; auto. rewrite M.gempty. apply rt_refl.
      destruct (var_dec v x).
      + subst.
        replace (rename_all (M.remove x (M.set x y (M.empty var))) e) with e. 
        apply rt_refl.
        etransitivity.
        apply rename_all_empty.
        apply prop_rename_all. apply smg_sym.
        eapply smg_trans.
        apply remove_set_1; auto.
        apply remove_empty.
      +  replace (rename_all (M.remove v (M.set x y (M.empty var))) e) with (rename_all (M.set x y (M.empty var)) e).
         rewrite inv_app_Eproj.
         rewrite inv_app_Eproj.
         apply rename_context_clos_s.
         apply H; auto.
         apply (Disjoint_Union_l _ _ _ H0).
         intro. inv H1. auto. inv H8.
         apply prop_rename_all.
         apply smg_sym.
         eapply smg_trans.
         apply remove_set_2; auto.
         apply proper_set.
         apply remove_empty.
    - unfold rename. simpl.
      rewrite bound_var_Efun in H1.
      assert (Hdf := (Disjoint_Union_l _ _ _ H1)).
      assert (Hde := Disjoint_Union_r _ _ _ H1).
      specialize (H Hdf).
      specialize (H0 Hde).
      assert (Hf2 := Decidable_name_in_fundefs f2).
      inv Hf2. specialize (Dec x). inv Dec.
      + assert (map_get_r var (remove_all (M.set x y (M.empty var)) (all_fun_name f2)) (M.empty var)).
        eapply smg_trans.
        apply remove_all_in. apply same_name_in_fun. auto.
        apply remove_all_empty.
        replace (rename_all_fun (remove_all (M.set x y (M.empty var)) (all_fun_name f2)) f2) with f2.
        replace (rename_all (remove_all (M.set x y (M.empty var)) (all_fun_name f2)) e) with e.
        apply rt_refl.
        etransitivity. apply rename_all_empty. symmetry.
        eapply prop_rename_all.
        apply H3.
        etransitivity. apply rename_all_empty. symmetry.
        eapply prop_rename_all.
        apply H3.
      + assert (map_get_r var (remove_all (M.set x y (M.empty var)) (all_fun_name f2)) (M.set x y (M.empty var))).
        {
          eapply smg_trans.
          apply remove_all_not_in.
          intro; apply H2.
          apply same_name_in_fun; auto.
          apply proper_set. apply remove_all_empty.
        }
        replace  (rename_all (remove_all (M.set x y (M.empty var)) (all_fun_name f2)) e) with
            (rename_all (M.set x y (M.empty var)) e).        
        
        rewrite inv_app_Efun1.
        eapply rt_trans.        
        apply rename_context_clos_s.
        apply H0.
        intro. inv H4. auto. inv H8.
        apply rename_fds_Efun_s.
        replace (rename_all_fun (remove_all (M.set x y (M.empty var)) (all_fun_name f2)) f2) with
            (rename_all_fun (M.set x y (M.empty var)) f2). apply H.
        auto.
        symmetry.
        apply prop_rename_all; auto. auto.
        symmetry.
        apply prop_rename_all; auto.
    - unfold rename. simpl.
      unfold apply_r.
      destruct (var_dec x v).
      + subst.
        rewrite M.gss.
        eapply rt_trans.
        apply rt_step.
        rewrite inv_app_Hole at 1.
        constructor. constructor.
        simpl. intro. inv H0.
        apply rename_clos_s_app_l.
      + rewrite M.gso by auto.
        rewrite M.gempty.
        apply rename_clos_s_app_l.
    - unfold rename.
      simpl.
      eapply rt_trans.
      apply rename_clos_s_prim_l.
      destruct (var_dec x v). subst.
      + replace  (rename_all (M.remove v (M.set v y (M.empty var))) e) with e.
        apply rt_refl.
        etransitivity.
        apply rename_all_empty.
        symmetry. apply prop_rename_all.
        eapply smg_trans. apply remove_set_1. apply remove_empty.
      + do 2 (rewrite inv_app_Eprim).
        apply rename_context_clos_s.
        replace (rename_all (M.remove v (M.set x y (M.empty var))) e) with (rename_all (M.set x y (M.empty var)) e).      
        rewrite bound_var_Eprim in H0.
        assert (Hde := Disjoint_Union_l _ _ _ H0).
        apply H; auto.
        apply prop_rename_all.
        apply smg_sym. eapply smg_trans. apply remove_set_2; auto.
        apply proper_set. apply remove_empty.
        intro. inv H1. auto. inv H7.
    - unfold rename.
      simpl. unfold apply_r. destruct (var_dec x v).
      subst. rewrite M.gss. constructor.
      rewrite inv_app_Hole.
      rewrite inv_app_Hole at 1.
      constructor. constructor. intro. inv H0.
      rewrite M.gso by auto.
      rewrite M.gempty.
      apply rt_refl.
    - rewrite bound_var_fundefs_Fcons in H1.
      assert (Hde := Disjoint_Union_l _ _ _ H1).
      assert (Hdv := Disjoint_Union_r _ _ _ H1).
      assert (Hdl := Disjoint_Union_l _ _ _ Hdv).
      assert (Hdef5 := Disjoint_Union_r _ _ _ Hdv).
      assert (Hdf5 := Disjoint_Union_r _ _ _ Hdef5).
      assert (Hdee := Disjoint_Union_l _ _ _ Hdef5).
      apply H0 in Hdf5.
      apply H in Hdee.
      eapply rt_trans with (y :=   (Fcons v t l e (rename_all_fun (M.set x y (M.empty var)) f5))).
      apply rename_fds_Fcons2_s. auto.       
      assert (Hl := Decidable_FromList l).
      inv Hl. specialize (Dec x). inv Dec.
      + replace (rename_all (remove_all (M.set x y (M.empty var)) l) e) with e.
        apply rt_refl.
        etransitivity. apply rename_all_empty.
        apply prop_rename_all.
        apply smg_sym.
        eapply smg_trans.
        apply remove_all_in. auto. apply remove_all_empty.
      + replace  (rename_all (remove_all (M.set x y (M.empty var)) l) e) with (rename y x e).
        do 2 (rewrite inv_app_Fcons1).
        apply rename_context_fds_clos_s. auto. intro.
        inv H4. auto. inv H11. 
        apply prop_rename_all.
        apply smg_sym.
        eapply smg_trans.
        apply remove_all_not_in. auto.
        apply proper_set.
        apply remove_all_empty.
      + intro. apply H2. constructor 2. auto.
    - apply rt_refl.
      Unshelve.
      auto.
  Qed.

  
      (* Special case of preord_env_P_getlist_l, leaving it here for now *)
  Lemma preord_env_P_getlist_app: forall rho1 rho2 x y l' l vs  k,
    preord_var_env pr cenv k rho1 rho2 x y ->
    preord_env_P pr cenv (FromList (l ++ (x :: l'))) k rho1
                 rho2 ->
  getlist (l ++ (x :: l')) rho1 = Some vs ->
  exists vs2 : list val,
    getlist (l ++ (y :: l')) rho2 = Some vs2 /\
    Forall2 (preord_val pr cenv k) vs vs2. 
  Proof.
    induction l; intros.
    - simpl app.
      simpl app in H1.
      simpl in H1.      destruct (M.get x rho1) eqn:gxr.
      apply H in gxr. destructAll.
      destruct (getlist l' rho1) eqn:glr.
      eapply preord_env_P_getlist_l in glr; eauto. destructAll.
      exists (x0::x1). split. simpl. rewrite H2. rewrite H4. reflexivity.
      inversion H1; subst. constructor; auto.
      simpl. rewrite FromList_cons.
      right; auto.
      inversion H1.
      inversion H1.
    - simpl in H1.
                               destruct (M.get a rho1) eqn:gar.
      destruct (getlist (l ++ x :: l') rho1) eqn:glrho1.
      rewrite <- glrho1 in IHl.
      assert (preord_env_P pr cenv (FromList (l ++ x :: l')) k rho1 rho2).
      eapply preord_env_P_antimon. apply H0. simpl. 
      rewrite FromList_cons.
      right. auto.
      specialize (IHl _ _ H H2 glrho1).
      destructAll.
      apply H0 in gar.
      destructAll.
      exists (x1::x0).
      split.
      simpl. rewrite H5. rewrite H3. reflexivity.
      inversion H1. subst.
      constructor. apply H6. auto.
      simpl. left; auto.      
      inversion H1.
      inversion H1.
  Qed.
  
  Theorem rename_loc_equiv: forall x y e e' k rho1 rho2,
                              preord_env_P pr cenv (occurs_free e) k  rho1 rho2 ->
                              preord_var_env pr cenv k rho1 rho2 x y ->
                              rename_loc x y e e' ->
                              preord_exp pr cenv k (e, rho1) (e', rho2).
  Proof.
    intros.
    inversion H1; subst.
    - intro; intros.
      inv H3.
      assert (exists vs2, getlist (l++y::l') rho2 = Some vs2 /\ Forall2 (preord_val pr cenv k) vs vs2).
      eapply preord_env_P_getlist_app; eauto.
      rewrite occurs_free_Econstr in H.
      eapply preord_env_P_antimon; eauto.
      left. auto.
      destructAll.
      eapply preord_exp_refl in H13; eauto.
      destructAll.
      eexists; eexists; eauto. split.
      eapply BStep_constr; eauto.
      apply H6.
      apply preord_env_P_extend.
      eapply preord_env_P_antimon; eauto.
      rewrite occurs_free_Econstr.
      right. auto.      
      rewrite preord_val_eq. simpl. split; auto.
      apply Forall2_Forall2_asym_included.
      auto.
    - intro; intros.
      inv H3.
      apply H0 in H6. destructAll.
      apply preord_val_constr in H4. destructAll.
      eapply preord_exp_refl in H12. destructAll.
      eexists. eexists.
      split.
      eapply BStep_case; eauto.
      apply H6.
      eapply preord_env_P_antimon.
      apply H.
      eapply occurs_free_Ecase_Included.
      apply findtag_In_patterns; eauto.
      auto.
    - intro; intros.
      inv H3.
      apply H0 in H12. destructAll.
      apply preord_val_constr in H4.
      destructAll.
      assert (Hh := Forall2_asym_nthN _ _ _ _ _ H5 H13). destructAll.
      eapply preord_exp_refl in H14. destructAll.
      exists x2, x3.
      split.
      eapply BStep_proj.
      apply H3.
      apply H4.
      apply H7. apply H8.
      rewrite occurs_free_Eproj in H.
      apply preord_env_P_extend.
      eapply preord_env_P_antimon.
      apply H.
      right. auto.
      auto.
      auto.
    - intro; intros.
      inv H3.
      assert (exists vs2, getlist (ys++y::ys') rho2 = Some vs2 /\ Forall2 (preord_val pr cenv k) vs vs2).
      eapply preord_env_P_getlist_app; eauto.
      rewrite occurs_free_Eprim in H.
      eapply preord_env_P_antimon; eauto.
      left. auto.
      destructAll.
      assert (Hax := Prim_axiom _ _ _ _ _ H10 _ _ _ H4 H13).
      destructAll.
      eapply preord_exp_refl in H15; eauto.
      destructAll.
      eexists; eexists; eauto. split.
      eapply BStep_prim; eauto.
      apply H9.
      apply preord_env_P_extend.
      eapply preord_env_P_antimon; eauto.
      rewrite occurs_free_Eprim.
      right. auto.
      auto.
    - intro; intros.
      inv H3.
      apply H0 in H7.
      destructAll.
      rewrite preord_val_eq in H4.
      destruct x0.
      inversion H4.
      2: inversion H4.
      simpl in H4.
      assert (H8' := H8).
      eapply preord_env_P_getlist_l in H8; eauto.
      destructAll.      
      specialize (H4 vs x0 (k-1) t xs e rho''). 
      assert ( length vs = length x0).
      eapply Forall2_length; eauto.
      symmetry in H13.
      specialize (H4 H7 H10 H13).
      destructAll.
      apply H9 in H14.
      destructAll.
      exists x4, (x5+1). split.
      eapply BStep_app; eauto.
      replace (k-(c+1)) with (k-1-c) by omega.
      auto.
      omega.
      eapply Forall2_monotonic.
      2: apply H6.
      intros.      
      eapply preord_val_monotonic.
      apply H11.
      omega.
      omega.
      rewrite occurs_free_Eapp. left; auto.
    - intro; intros.
      inv H3.
      assert (H8' := H8).
      eapply preord_env_P_getlist_app in H8'.
      2: apply H0.
      destructAll.
      apply H in H7. destructAll.
      rewrite preord_val_eq in H6.
      destruct x1.  inversion H6.
      2: inversion H6.
      simpl in H6.
      assert (length vs = length x0).
      eapply Forall2_length; eauto.
      symmetry in H13.
      specialize (H6 vs x0 (k-1) t xs e rho'' H7 H10 H13).
      destructAll.
      apply H11 in H14.
      destructAll.
      exists x4, (x5+1). split.
      eapply BStep_app; eauto.
      replace (k-(c+1)) with (k-1-c) by omega. auto.
      omega.
      eapply Forall2_monotonic.
      2: apply H4. intros. eapply preord_val_monotonic; eauto.
      omega.
      omega.
      constructor.
      eapply preord_env_P_antimon.
      apply H.
      rewrite occurs_free_Eapp. left; auto.      
    - intro. intros. inversion H3; subst.
      apply H0 in H6.
      destructAll.
      eexists; eexists.
      split.
      apply BStep_halt.
      eauto. replace (k-0) with k by omega. apply H5.
  Qed.


  
  
  Theorem getlist_two: forall {A} {x y} {vx vy:A} {rho0},
   getlist [x; y] rho0 = Some [vx; vy] ->
   M.get  x rho0 = Some vx /\ M.get  y rho0 = Some vy.
  Proof.
    intros.
    simpl in *. destruct (M.get x rho0).
    destruct (M.get y rho0).
    inversion H; subst. split; auto.
    inversion H.
    inversion H.
  Qed.
  

  Theorem rw_proj1_equiv : forall  x x' t t' ys  y e e'  c c' n k rho1 rho2,
                             ~ bound_stem_ctx c x ->
                             ~ bound_stem_ctx c y ->
                             ~ bound_stem_ctx c' x' ->
                             ~ bound_var_ctx c' y  ->
                             x <> y ->
                             nthN ys n = Some y -> 
                             preord_env_P pr cenv (occurs_free (Econstr x t ys (c |[ Eproj x' t' n x (c' |[e]|) ]|))) k rho1 rho2 ->
                             rename_loc x' y e e' ->
                             preord_exp pr cenv k (Econstr x t ys (c |[ Eproj x' t' n x (c' |[e]|) ]|) , rho1 )
                                        (Econstr x t ys (c |[ Eproj x' t' n x (c' |[e']|) ]|), rho2).
  Proof.                                                           
    intros.
    destruct (var_dec x' y). subst.
    apply rename_loc_refl_x in H6. subst. apply preord_exp_refl; auto.
    intros; intro; intros.
    inversion H8;  subst.
    assert (Hys : Included var (FromList ys)
                           (occurs_free (Econstr x t ys (c |[ Eproj x' t' n x (c' |[ e ]|) ]|)))). {
      rewrite occurs_free_Econstr. left; auto.
    }
    assert (H11' := preord_env_P_getlist_l _ _ _ _ _ _ _  _ H5 Hys H16). destructAll.
    assert (Hyv := getlist_nth_get _ _ _ _ _ H16 H4).
    assert (Hyv' := getlist_nth_get _ _ _ _ _ H9 H4).
    destructAll.
    eapply preord_exp_compat_stem_vals with (xs := x::y::nil) in H18; eauto.
    destructAll. eexists; eexists.
    split. eapply BStep_constr; eauto.
    eauto. 
    Focus 3.
    simpl. rewrite M.gss. rewrite M.gso by auto. rewrite H14. reflexivity.
    Focus 3.
    simpl. rewrite M.gss. rewrite M.gso by auto. rewrite H12. reflexivity.
    + intros.
      intro. intros. inv H21.
      assert (Hg := getlist_two H17).
      assert (Hg' := getlist_two H19).
      destructAll. rewrite H30 in H23. inv H23.      
      eapply preord_exp_compat_stem_vals with (xs := x'::y::nil) in H32; eauto.
      destructAll. eexists; eexists. split.
      eapply BStep_proj.
      eauto.
      eauto.
      apply H23.
      auto.
      Focus 3.
      simpl. rewrite M.gss. rewrite M.gso; auto. rewrite H24. reflexivity.
      Focus 3.
      simpl. rewrite M.gss. rewrite M.gso; auto. rewrite H22. reflexivity.
      intros. 
      assert (Hg := getlist_two H25).
      assert (Hg' := getlist_two H26).
      destructAll.
      eapply rename_loc_equiv; eauto.
      intro. intros.
      rewrite H34 in H29.
      inv H29.
      exists x1. split; auto.
      specialize (H23 x').
      apply H23 in H34. destructAll.
      rewrite H29 in H27. inv H27. auto.
      eapply rename_loc_occurs_free; eauto.
      {
        split. intros. intro.
        inv H23.
        inv H26.
        apply H1. auto.
        inv H23.
        apply H2. apply bound_stem_var. auto.
        inv H26.
      }
      apply preord_env_P_extend. rewrite occurs_free_Eproj in H15.
      eapply preord_env_P_antimon. apply H15. right; auto.
      specialize (H15 x). apply H15 in H30. destructAll.
      rewrite H23 in H21. inv H21.
      rewrite preord_val_eq in H25. simpl in H25. destruct H25.
      apply (Forall2_asym_nthN _ _ _ _ _ H25) in H31. destructAll.
      rewrite H26 in H11. inv H11; auto.
      apply occurs_free_Eproj.
      left; auto.      
    + split. intros.
      intro. inv H15.
      inv H19.
      * apply H. apply H17.
      * inv H15.
        apply H0. apply H17.
        inversion H19.
    + apply preord_env_P_extend.
      eapply preord_env_P_antimon.
      apply H5. intro. intros.
      rewrite occurs_free_Econstr. right; auto.
      rewrite preord_val_eq. simpl. split; auto.

      apply Forall2_Forall2_asym_included.
      auto.
  Qed.


 
  Theorem rw_proj_clos_equiv : forall  x x' t t' ys  y e e'  c n ,
                             ~ bound_stem_ctx c x ->
                             ~ bound_stem_ctx c y ->
(*                             ~ bound_var e x' ->  *)
                             ~ bound_var e y  ->
                             x <> y ->
                             rename_clos_s x' y e e' ->
                             nthN ys n = Some y ->
                             forall k rho1 rho2,
                             preord_env_P pr cenv (occurs_free (Econstr x t ys (c |[ Eproj x' t' n x e ]|))) k rho1 rho2 ->
                             preord_exp pr cenv k (Econstr x t ys (c |[ Eproj x' t' n x e ]|) , rho1 )
                                        (Econstr x t ys (c |[ Eproj x' t' n x e' ]|), rho2).
  Proof.
    intros x x' t t' ys y e e' c n Hs_cx Hs_cy Hbv_ey Hxy Hrcs Hnth k rho1 rho2 Hpreord.
    revert k rho1 rho2 Hpreord. 
    induction Hrcs.
    - inversion H; subst.
      intros.
      eapply rw_proj1_equiv; eauto.
      intro. apply Hbv_ey. apply bound_var_app_ctx. left; auto. 
    - intros. apply preord_exp_refl. auto.
    - intros.
      eapply preord_exp_trans.
      apply IHHrcs1.
      auto.
      eauto.
      intro.
      apply IHHrcs2.
      apply rename_clos_s_included in Hrcs1.
      intro. apply Hbv_ey.
      eapply bound_var_rename; eauto.
      apply preord_env_P_refl.
  Qed.

Definition Range_map {A:Type} sig:  Ensemble A:=
  (fun x => exists y, M.get y sig = Some x).

Definition Dom_map {A:Type} sig : Ensemble (M.elt):=
  (fun x => exists (y:A), M.get x sig = Some y).

Theorem Dom_map_remove {A:Type} : forall sigma v,
  Same_set _ (Dom_map (@M.remove A v sigma))
                        (Setminus _ (Dom_map sigma) (Singleton _ v)).
Proof.
  split; intros; intro; intros.
  inv H.
  split.
  exists x0.
  eapply gr_some.  
  apply H0.
  intro. inv H.
  rewrite M.grs in H0; auto. inv H0.
  inv H.
  inv H0.
  exists x0.
  rewrite M.gro; auto.
  intro; apply H1. subst.
  constructor.
Qed.


(* todo: move *)
Theorem not_in_remove_all: forall x l sigma,
  ~ (FromList l x) ->
  M.get x sigma = M.get x (remove_all sigma l).
Proof.
  induction l; intros.
  reflexivity.
  simpl. 
  assert (~ (a = x) /\ ~ (FromList l x)).
  split; intro. apply H. constructor; auto.
  apply H. constructor 2; auto.
  destruct H0.
  rewrite <- IHl; auto.
  symmetry.
  rewrite M.gro; auto.
Qed.  

Theorem remove_all_some:
  forall x y l sigma,
    M.get x (remove_all sigma l) = Some y ->
    ~ (FromList l x).
Proof.
  induction l.
  intros. intro. inv H0.
  simpl.
  intros.
  intro. inv H0.
  rewrite remove_all_none in H. inv H.
  rewrite M.grs; auto.
  eapply IHl; eauto.
Qed.  

Theorem Dom_map_empty {A}:
  Same_set _ (Dom_map (M.empty A)) (Empty_set _).
Proof.
  split; intro. intro. inv H. rewrite M.gempty in H0. inv H0.
  intro. inv H.
Qed.

Theorem Dom_map_set:
  forall (sig:M.t var) x y,
    Same_set _ (Dom_map (M.set x y sig)) (Union _ [set x] (Dom_map sig)).
Proof.
  intros. split. intro. intro. inv H. destruct (var_dec x0 x).
  subst; auto.
  rewrite M.gso in H0 by auto.
  right. exists x1; auto.
  intro. intro. inv H. exists y. inv H0. rewrite M.gss.
  auto.
  destruct (var_dec x x0). subst. exists y.
  rewrite M.gss. auto.
  inv H0. exists x1. rewrite M.gso; auto.
Qed.  

Theorem Dom_map_set_list:
  forall (sig: M.t var) lx ly,
  length lx = length ly ->
  Same_set _ (Dom_map (set_list (combine lx ly) sig)) (Union _ (FromList lx) (Dom_map sig)).
Proof.
  induction lx.
  - intros. destruct ly.
    simpl. rewrite FromList_nil. auto with Ensembles_DB.
    inv H.
  - intros. destruct ly; inv H.
    simpl. rewrite FromList_cons.
    rewrite Dom_map_set.
    apply IHlx in H1. rewrite H1.  auto 25 with Ensembles_DB.
Qed.    


Theorem Dom_map_remove_all: forall l sigma ,
  Same_set _ (Dom_map (remove_all sigma l))
           (Setminus _ (Dom_map sigma) (FromList l)).
Proof.
  split; intro; intro.
  inv H.
  assert (~ (FromList l x)) by apply (remove_all_some _ _ _ _ H0).
  split; auto.
  rewrite <- not_in_remove_all in H0; auto.
  exists x0; auto.  
  inv H.
  inv H0.
  exists x0.
  rewrite <- not_in_remove_all; auto.
Qed.


Theorem Range_map_remove {A:Type}: forall sigma v,
  Included _ (Range_map (@M.remove A v sigma))
                        (Range_map sigma).
Proof.
  intros. intro. intros. inv H.
  exists x0.
  eapply gr_some.
  apply H0.
Qed.

Theorem Range_map_remove_all : forall l sigma ,
  Included _ (Range_map (remove_all sigma l))
                        (Range_map sigma).
Proof.
  induction l; intros.
  simpl. reflexivity.
  simpl. eapply Included_trans.
  apply IHl.
  apply Range_map_remove.
Qed.

Theorem apply_r_sigma_in:
  forall sigma a,
  In _ (Union _ (Setminus _ (Singleton _ a) (Dom_map sigma)) (Range_map sigma)) (apply_r sigma a).
Proof.
  unfold apply_r.
  intros.
  destruct (Maps.PTree.get a sigma) eqn:gas.
  right. exists a. auto.
  left.
  split.
  constructor.
  intro. inv H. rewrite gas in H0. inv H0.
Qed.  
  
Theorem FromList_apply_r_list:
  forall sigma l,
  Included _ (FromList (apply_r_list sigma l))
           (Union _ (Setminus var (FromList l) (Dom_map sigma)) (Range_map sigma)).
  Proof.
    induction l.
    - simpl. intro. intro.
      inv H.
    - simpl.
      rewrite FromList_cons.
      rewrite FromList_cons.
      apply Union_Included.
      intro. intros.
      inv H.
      assert (Hrs := apply_r_sigma_in sigma a).
      inv Hrs. left.
      inv H.
      split; auto.
      right; auto.
      intro; intro.
      apply IHl in H.
      inv H.
      left. inv H0.
      split; auto.
      right; auto.
  Qed.

  Theorem Dom_map_setlist: forall xs vs,
    Included _  (Dom_map (set_list (combine xs vs) (M.empty var)))
                (FromList xs).
  Proof.
    induction xs.
    - intros.
      simpl.
      intro. intro. inv H.
      rewrite M.gempty in H0. inv H0.
    - intro. simpl. destruct vs. simpl.
      intro. intro. inv H.
      rewrite M.gempty in H0. inv H0.
      simpl.
      rewrite FromList_cons.
      intro. intro.
      destruct (var_dec a x).
      subst. left; auto.
      right.
      specialize (IHxs vs).
      apply IHxs.
      inv H. rewrite M.gso in H0 by auto.
      exists x0.
      apply H0.
  Qed.      

  Theorem Dom_map_setlist_ss: forall xs vs,
                             length xs = length vs -> 
    Same_set _  (Dom_map (set_list (combine xs vs) (M.empty var)))
                (FromList xs).
  Proof.
    induction xs.
    - intros. split.
      simpl.
      intro. intro. inv H.
      inv H0. 
      rewrite M.gempty in H. inv H.
      intro. intro. inv H0.
    - intros. simpl. simpl in H. destruct vs.
      inv H.
      simpl in H.
      inv H. apply IHxs in H1.
      split.
      intro. intro. inv H.
      rewrite FromList_cons.
      simpl in H0.
      destruct (var_dec a x).
      subst. left; auto.
      right.
      apply H1.
      rewrite M.gso in H0 by auto.
      exists x0.
      apply H0.
      intro. intros.
      destruct (var_dec a x).
      subst.
      simpl. exists v. apply M.gss.
      inv H.
      exfalso; auto.
      apply H1 in H0. simpl.
      inv H0.
      exists x0. rewrite M.gso; auto.
  Qed.      

  
  Theorem Range_map_setlist: forall xs vs, 
    Included _  (Range_map (set_list (combine xs vs) (M.empty var)))
                (FromList vs).
  Proof.
    induction xs; intros.
    - simpl. intro.
      intro. inv H. rewrite M.gempty in H0. inv H0.
    - simpl. specialize IHxs. destruct vs. simpl.
      intro; intro; inv H. rewrite M.gempty in H0. inv H0.
      simpl.
      rewrite FromList_cons.
      intro. intro.
      inv H. destruct (var_dec x0 a).
      subst.      
      rewrite M.gss in H0.
      left. inv H0.
      constructor.
      right. 
      apply IHxs.
      rewrite M.gso in H0 by auto.
      exists x0. auto.
Qed.

  (* todo: move to identifiers? *)
Theorem name_not_free_in_fds: 
forall fds, Disjoint var (occurs_free_fundefs fds) (name_in_fundefs fds).
Proof.
  induction fds.
  - simpl. rewrite occurs_free_fundefs_Fcons.
    eauto 25 with Ensembles_DB.
  - simpl. eauto with Ensembles_DB.
Qed.


Theorem of_rename_all_mut: 
(forall e sigma, (occurs_free (rename_all sigma e)) \subset
                                    Union _ (Setminus _ (occurs_free e) (Dom_map sigma)) (Range_map sigma))
/\
(forall fds sigma, (occurs_free_fundefs (rename_all_fun sigma fds)) \subset
                                    Union _ (Setminus _ (occurs_free_fundefs fds) (Dom_map sigma)) (Range_map sigma)).
Proof.
  apply exp_def_mutual_ind; intros.
  - simpl.
    repeat normalize_occurs_free.
    apply Union_Included.
    + eapply Included_trans.
      apply FromList_apply_r_list.
      eauto with Ensembles_DB.
    + apply Setminus_Included_Included_Union.
      eapply Included_trans.
      apply H.
      assert (Hd := Dom_map_remove sigma v).
      assert (Hr := Range_map_remove sigma v).
      intro.
      intros. inv H0.
      destruct (var_dec x v).
      * subst. right. constructor.
      * inv H1.
        left. left. split.
        right. split; auto.
        intro. apply n; inv H1.
        auto.
        intro.
        apply H2.
        inv H1.
        exists x0.
        rewrite M.gro by auto. auto.
      * apply Hr in H1.
        eauto.        
  - simpl.
    repeat normalize_occurs_free.
    intro. intros.
    inv H.
    apply apply_r_sigma_in.
  - simpl.
    repeat normalize_occurs_free.
    specialize (H sigma).
    specialize (H0 sigma).
    repeat (apply Union_Included).
    + eapply Included_trans.
      intro; intro.
      inv H1.
      apply apply_r_sigma_in.
      eauto with Ensembles_DB.
    + eapply Included_trans.
      apply H.
      eauto with Ensembles_DB.
    + eapply Included_trans.
      apply H0.
      eauto with Ensembles_DB.
  - simpl.
    repeat normalize_occurs_free.
        apply Union_Included.
    + eapply Included_trans.
      intro. intro. inv H0.
      apply apply_r_sigma_in.
      eauto with Ensembles_DB.
    + apply Setminus_Included_Included_Union.
      eapply Included_trans.
      apply H.
      assert (Hd := @Dom_map_remove var sigma v).
      assert (Hr := Range_map_remove sigma v).
      intro.
      intros. inv H0.
      destruct (var_dec x v).
      * subst. right. constructor.
      * inv H1.
        left. left. split.
        right. split; auto.
        intro. apply n0; inv H1.
        auto.
        intro.
        apply H2.
        inv H1.
        exists x0.
        rewrite M.gro by auto. auto.
      * apply Hr in H1.
        eauto.
  - simpl.
    repeat normalize_occurs_free.
    apply Union_Included.
    + eapply Included_trans.
      apply H.
      apply Union_Included.
      * intro.  intro. inv H1.
        left. split. left.  auto.
        intro.
        apply H3.
        apply Dom_map_remove_all.
        split. auto.
        assert (Hnf := name_not_free_in_fds).
        specialize (Hnf f2).
        inv Hnf. specialize (H4 x). intro; apply H4.
        split; auto.
        apply name_fds_same.
        auto.        
      * right.
        eapply Range_map_remove_all.
        apply H1.
    + apply Setminus_Included_Included_Union.
      eapply Included_trans.
      apply H0.
      apply Union_Included.
      * intro. intro.
        inv H1.
        assert (Hh := Decidable_name_in_fundefs f2).
        inv Hh. specialize (Dec x).
        destruct Dec.
        right. apply rename_all_fun_name. auto.       
        left.  left. split. right. split; auto.
        intro; apply H3. 
        apply Dom_map_remove_all.
        split; auto.
        intro; apply H1.
        apply name_fds_same. auto.
      * left; right.
        eapply Range_map_remove_all. apply H1.
  - simpl.
    repeat normalize_occurs_free.
    apply Union_Included.
    eapply Included_trans.
    apply FromList_apply_r_list.
    eauto with Ensembles_DB.
    eapply Included_trans.
    intro. intro. inv H.
    apply apply_r_sigma_in.
    eauto with Ensembles_DB.
  -  simpl.
    repeat normalize_occurs_free.
        apply Union_Included.
    + eapply Included_trans.
      apply FromList_apply_r_list.
      eauto with Ensembles_DB.
    + apply Setminus_Included_Included_Union.
      eapply Included_trans.
      apply H.
      assert (Hd := Dom_map_remove sigma v).
      assert (Hr := Range_map_remove sigma v).
      intro.
      intros. inv H0.
      destruct (var_dec x v).
      * subst. right. constructor.
      * inv H1.
        left. left. split.
        right. split; auto.
        intro. apply n; inv H1.
        auto.
        intro.
        apply H2.
        inv H1.
        exists x0.
        rewrite M.gro by auto. auto.
      * apply Hr in H1.
        eauto.
  - simpl.
    rewrite occurs_free_Ehalt.
    rewrite occurs_free_Ehalt.
    intro. intro. inv H. apply apply_r_sigma_in.
  - simpl.
    repeat normalize_occurs_free.
    apply Union_Included.
    + intro. intro. inv H1. apply H in H2.
      inv H2.
      left. inv H1.
      split.
      left. split; auto.
      intro.
      inv H1. apply H3; auto.
      rewrite rename_all_fun_name in H3.
      apply H3; auto.
      intro; apply H4.
      apply Dom_map_remove_all.
      split. auto.
      intro; apply H3; auto.      
      right.
      eapply Range_map_remove_all.
      apply H1.
    + intro. intro. inv H1.
      apply H0 in H2.
      inv H2.
      inv H1. left.
      split; auto.
      right. split; auto.
      auto.
  - simpl.
    intro. intro. inv H.
Qed.


Corollary rename_not_occurs_free:
  forall e a fb,
    e <> a ->
    Disjoint var (occurs_free (rename e a fb)) [set a].
Proof.
  intros.
  eapply Disjoint_Included_l.
  apply of_rename_all_mut.
  split. intro. intro. inv H0. inv H2. inv H1.
  - inv H0. apply H2.
    rewrite Dom_map_set. auto.
  - inv H0. destruct (var_dec x0 x).
    subst. rewrite M.gss in H1. inv H1. auto.
    rewrite M.gso in H1 by auto. rewrite M.gempty in H1. inv H1.
Qed.

  
  (* rw rule for proj *)
  Corollary rw_proj_equiv : forall  x x' t t' ys  y e c n k rho1 rho2,
                             ~ bound_stem_ctx c x ->
                             ~ bound_stem_ctx c y ->
                             ~ bound_var e y  ->
                             x <> y ->
                             x' <> y ->
                             nthN ys n = Some y ->                        
                             preord_env_P pr cenv (occurs_free (Econstr x t ys (c |[ Eproj x' t' n x e ]|))) k rho1 rho2 ->
                             preord_exp pr cenv k (Econstr x t ys (c |[ Eproj x' t' n x e ]|) , rho1 )
                                        (Econstr x t ys (c |[ rename y x' e ]|), rho2).
  Proof.                                                           
    intros.
    assert (rename_clos_s x' y e (rename y x' e)).
    apply rename_corresp.
    split.
    intros.
    intro. inversion H6. subst. inv H8. auto.
    inv H9.
    eapply preord_exp_trans.
    eapply rw_proj_clos_equiv; eauto.
    intros.
    do 2 (rewrite inv_app_Econstr).
    do 2 (rewrite app_ctx_f_fuse). 
    apply preord_exp_compat.
    intros.
    apply rm_proj.
    assert (y <> x') by auto.
    apply rename_not_occurs_free with (fb := e) in H8.  intro. inv H8. specialize (H10 x').
    apply H10. split; auto with Ensembles_DB.
    2: apply preord_env_P_refl.
    eapply preord_env_P_antimon.
    apply H7.
    apply reflexivity.
  Qed.


  
  Lemma preord_var_apply_list: forall x z rho1 rho2 l vs k,  
     preord_env_P pr cenv
     (Setminus _ (Ensembles_util.FromList l)     
               (Singleton var x)) k rho1 rho2 ->
     preord_var_env pr cenv k rho1 rho2 x z ->
     getlist l rho1 = Some vs ->
     exists vs' : list val,
       getlist (apply_r_list (M.set x z (M.empty var)) l) rho2 = Some vs' /\
       Forall2 (preord_val pr cenv k) vs vs'.
  Proof.
    induction l; intros.
    inversion H1. subst. 
    exists [].
    split; auto.        
    simpl in H1.
    destruct (M.get a rho1) eqn:ga1.
    destruct (getlist l rho1) eqn:gll1.
    { inversion H1; subst.
      specialize (IHl l0 k).
      assert (preord_env_P pr cenv
          (Setminus var (Ensembles_util.FromList l) (Singleton var x)) k rho1
          rho2 ).
      eapply preord_env_P_antimon.
      apply H.
      rewrite Ensembles_util.FromList_cons.
      eauto 10 with Ensembles_DB.
      apply IHl in H2; auto. destructAll.
      destruct (var_dec a x).
      - subst.
        simpl. unfold apply_r.
        rewrite M.gss. apply H0 in ga1. destructAll.
        rewrite H4. rewrite H2.
        exists (x1::x0).
        split; auto.
      - simpl. unfold apply_r.
        rewrite M.gso; auto.
        rewrite M.gempty. apply H in ga1. destructAll.
        rewrite H4.
        rewrite H2. exists (x1::x0). auto.
        unfold Setminus.
        split. constructor. auto.
        intro. inversion H4. apply n.
        auto.       
     }    
     inversion H1.
    inversion H1.
  Qed.



  

  (* move this  *)
  Theorem ub_in_fundefs:
    forall e xs v t fds ,
      unique_bindings_fundefs fds ->
      find_def v fds = Some (t, xs, e) -> 
      unique_bindings e.
  Proof.
    induction fds; intros.
    - simpl in H0. destruct (M.elt_eq v v0).
      + inversion H0; subst.
        inversion H; subst; auto.
      + inversion H; subst.
        apply IHfds; auto.
    - inversion H0.
  Qed.

  Theorem preord_var_env_monotonic: forall k rho1 rho2 j z x ,
    preord_var_env pr cenv k rho1 rho2 x z ->
    j <= k ->
     preord_var_env pr cenv j rho1 rho2 x z.
  Proof.
    intros. intro. intros. apply H in H1. destructAll. exists x0; split; auto.
    eapply preord_val_monotonic; eauto.
  Qed.

    

  
  
  Theorem fun_inline_rw:
    forall f rho1 rho'  f' fl t xs e rho2 rho2' ys vs vs'  k,
    M.get f rho1 = Some (Vfun rho' fl f') ->
    find_def f' fl = Some (t,xs,e) ->
    getlist ys rho1 = Some vs ->
    getlist ys rho2 = Some vs' ->
    Forall2 (preord_val pr cenv k) vs vs' ->                        
    (* show that rho2 will have the same binding for free variables of f(xs) = e *)
    preord_env_P pr cenv (occurs_free_fundefs fl) k rho' rho2 ->

    (setlist xs vs' (def_funs fl fl rho2 rho2)) = Some rho2' ->
    (* next step is to show that (e, rho2') ~= (rename xs ys e, rho2) *)
    preord_exp pr cenv (k+1) (Eapp f t ys, rho1) (e, rho2').
  Proof.
    intros. intro. intros.
    inversion H7; subst.
    rewrite H in H11; inv H11.
    rewrite H0 in H14; inv H14.
    rewrite H1 in H12; inv H12.
    eapply preord_exp_refl in H18. replace (k+1 - (c+1)) with (k - c) by omega.
    apply H18.
    eapply preord_env_P_setlist_l.
    4: apply H17.
    4: apply H5.
    3: auto.
    3: omega.
    apply preord_env_P_def_funs_cor with (S1 :=  (Union var (name_in_fundefs fl0) (occurs_free_fundefs fl0))).
    eapply preord_env_P_antimon. apply H4.
    eauto 10 with Ensembles_DB.
    apply find_def_correct in H0.
    apply occurs_free_in_fun in H0.
    intros.
    apply H0 in H9.
    destruct H9. exfalso; apply H8; auto. apply H9.
  Qed.


  Theorem fun_inline_compat_clos: forall k fl e rho1 rho2 c e',
                                    (forall (k' : nat) (rho1' rho2' : env),
                                       k' <= k ->
                                       preord_env_P pr cenv (occurs_free e) k' rho1' rho2' ->
                                       eq_env_P (Union _ (occurs_free_fundefs fl) (name_in_fundefs fl)) (def_funs fl fl rho1 rho1) rho1' ->
                                       eq_env_P (Union _ (occurs_free_fundefs fl) (name_in_fundefs fl)) (def_funs fl fl rho2 rho2) rho2' ->
                                       preord_exp pr cenv k' (e, rho1') (e', rho2')) ->
    preord_env_P pr cenv (occurs_free (Efun fl (c|[e]|))) k rho1 rho2 ->
    Disjoint var (bound_stem_ctx c) (occurs_free_fundefs fl)  ->
    Disjoint var (bound_stem_ctx c) (name_in_fundefs fl)  -> 
    preord_exp pr cenv k (Efun fl (c |[ e ]|) , rho1) (Efun fl (c|[ e' ]|), rho2).
Proof.
  intros. intro. intros.
  inv H4.
  eapply preord_exp_compat_vals_stem_set in H10; eauto.
  destructAll.
  eexists. eexists.
  split.
  constructor. eauto. auto.
  - apply Union_Disjoint_r; auto.
  -    
  eapply preord_env_P_def_funs_cor.
  rewrite occurs_free_Efun in H0.
  rewrite Union_commut in H0.
  apply H0.
Qed.

(* shadowed version of preord_rename_clos *)
Theorem preord_rename_clos_s: forall fb fb' v a e t,
  (Disjoint _ (bound_var fb) (Singleton _ e)) ->
  rename_clos_s a e fb fb' ->
  M.get e (M.set a v t) = Some v ->
 forall k, 
  preord_exp pr cenv k (fb, M.set a v t) (fb', M.set a v t).
Proof.
  intros fb fb' v a e t Hde Hrc Hg.
  induction Hrc.
  - intros.
    destruct (var_dec a e). subst.
    inv H.
    apply rename_loc_refl_x in H0. subst.
    apply preord_exp_refl. apply preord_env_P_refl.
    inv H.
    assert ( getlist [a; e] (M.set a v t) = Some (v::v::nil)).
    simpl. rewrite M.gss. rewrite Hg.  reflexivity.
    eapply preord_exp_compat_stem_vals with (xs := a::e::nil); eauto.
    intros.
    eapply rename_loc_equiv; eauto.
    intro. intros. simpl in H3.  simpl in H4.
    destruct (M.get a rho1).
    destruct (M.get e rho1).
    inv H3. 
    inv H5.
    destruct (M.get a rho2).
    destruct (M.get e rho2).
    inv H4. exists v1. split.
    reflexivity.
    apply preord_val_refl.
    inv H4.
    inv H4.
    inv H3.
    inv H3.    
    split. intro. intro. inv H2. inv H4.
    auto. inv H2. inv Hde.
    specialize (H2 x). apply H2.
    split; auto. rewrite bound_var_app_ctx; auto.
    left. apply bound_stem_var. auto.
    inv H4.
    apply preord_env_P_refl.
  - intros. apply preord_exp_refl. apply preord_env_P_refl.
  - intros.
    eapply preord_exp_trans.
    apply IHHrc1. auto.
    intro.
    apply IHHrc2.
    apply rename_clos_s_included in Hrc1. 
    apply bound_var_rename in Hrc1.
    rewrite <- Hrc1. auto.
Qed.


Theorem preord_rename_clos: forall fb fb' v a e t,
  (Disjoint _ (bound_var fb) (Singleton _ a)) ->
  (Disjoint _ (bound_var fb) (Singleton _ e)) ->
  rename_clos a e fb fb' ->
  M.get e (M.set a v t) = Some v ->
 forall k, 
  preord_exp pr cenv k (fb, M.set a v t) (fb', M.set a v t).
Proof.
  intros fb fb' v a e t Hda Hde Hrc Hg.
  induction Hrc.
  - intros.
    destruct (var_dec a e). subst.
    inv H.
    apply rename_loc_refl_x in H0. subst.
    apply preord_exp_refl. apply preord_env_P_refl.
    inv H.
    assert ( getlist [a; e] (M.set a v t) = Some (v::v::nil)).
    simpl. rewrite M.gss. rewrite Hg.  reflexivity.
    eapply preord_exp_compat_vals with (xs := a::e::nil); eauto.
    intros.
    eapply rename_loc_equiv; eauto.
    intro. intros. simpl in H2.  simpl in H3.
    destruct (M.get a rho1).
    destruct (M.get e rho1).
    inv H2. 
    inv H4.
    destruct (M.get a rho2).
    destruct (M.get e rho2).
    inv H3. exists v1. split.
    reflexivity.
    apply preord_val_refl.
    inv H3.
    inv H3.
    inv H2.
    inv H2.    
    split. intro. intro. inv H1. inv H3.
    inv Hda. specialize (H1 x). apply H1.
    split; auto.
    rewrite bound_var_app_ctx.
    left. auto.
    inv H1.
    inv Hde. specialize (H1 x). apply H1.
    split; auto. rewrite bound_var_app_ctx; auto.
    inv H3.
    apply preord_env_P_refl.
  - intros. apply preord_exp_refl. apply preord_env_P_refl.
  - intros.
    eapply preord_exp_trans.
    apply IHHrc1. auto. auto.
    intro.
    apply IHHrc2.
    apply bound_var_rename in Hrc1. 
    eapply Proper_Disjoint_l. symmetry. eauto.
    reflexivity. auto.
    apply bound_var_rename in Hrc1. 
    eapply Proper_Disjoint_l. symmetry. eauto.
    reflexivity. auto.
Qed.


(*todo: move to set_util? *)
Theorem Disjoint_FromList_r :
        forall A S l x,
          Disjoint A S (FromList l) ->
 List.In x l ->
 Disjoint A S (Singleton A x).
Proof.
  intros.
  split. intros.
  intro.
  inv H.
  inv H1.
  inv H3.
  specialize (H2 x0).
  apply H2.
  split; auto.
Qed.  

Theorem Disjoint_FromList_cons:
  forall A S a xs,
    Disjoint A S (FromList (a :: xs)) ->
                  Disjoint A S (FromList xs).
Proof.
  intros. inv H.
  split. intro; intro.
  specialize (H0 x).
  apply H0.
  inv H.
  split; auto.
  constructor 2; auto.
Qed.


Theorem set_list_eqn: forall l,
  set_list l (M.empty var)  = 
  fold_right
    (fun (xv : M.elt * M.elt) (cmap : M.t M.elt) =>
       M.set (fst xv) (snd xv) cmap) (M.empty var) l.
Proof.
  induction l. simpl. auto.
  destruct a. simpl. reflexivity.
Qed.


Theorem setlist_empty_not_in:
  forall a xs ys,
  ~ List.In a xs ->
  M.get a  (fold_right
       (fun (xv : M.elt * var) (cmap : M.t var) =>
        M.set (fst xv) (snd xv) cmap) (M.empty var) 
       (combine xs ys)) = None.
Proof.
  induction xs; intros.
  -  simpl. apply M.gempty.
  - simpl.
    assert (H' := H).
    apply not_in_cons in H.
    destruct H.
    destruct ys.
    simpl. apply M.gempty.
    simpl. rewrite M.gso by auto.
    specialize (IHxs ys H0).
    apply IHxs.
Qed.    

Theorem setlist_Disjoint_not:
  forall A a xs ys, 
  Disjoint _ (FromList ys) (Singleton _ a) ->
  ~ (exists z : M.elt,
     M.get z
       (fold_right
          (fun (xv : M.elt * A) (cmap : M.t A) =>
           M.set (fst xv) (snd xv) cmap) (M.empty A) 
          (combine xs ys)) = Some a).
Proof.
  induction xs.
  - intros.
    intro.
    destruct H0. simpl in H0. rewrite M.gempty in H0.
    inv H0.
  -   intros. intro.
      destruct H0.
      destruct ys.
      simpl in H0. rewrite M.gempty in H0. inv H0.
      simpl in H0.
      destruct (var_dec x a0).
      subst.
      rewrite M.gss in H0. inv H0.
      inv H.
      specialize (H0 a).
      apply H0.
      split. constructor; auto.
      auto.
      rewrite M.gso in H0 by auto.
      apply Disjoint_sym in H.
      apply Disjoint_FromList_cons in H.
      apply Disjoint_sym in H.
      apply IHxs in H.
      apply H. exists x; auto.
Qed.    



(* setlist_rename_all now without Disjoint _ (bound_var fb) (FromList xs) *)
Theorem setlist_rename_all:
  forall xs ys vs rho2 rho2',
    NoDup xs ->
    getlist ys rho2 = Some vs ->
    setlist xs vs rho2 = Some rho2'  ->
    forall fb,
      (Disjoint _ (bound_var fb) (FromList ys)) ->
    (Disjoint _ (FromList ys) (FromList xs)) ->
    forall k,
    preord_exp pr cenv k (fb, rho2')
               (rename_all (set_list (combine xs ys) (M.empty var)) fb, rho2).
Proof.
  induction xs; intros ys vs rho2 rho2' Nb; intros.
  - inv H0. destruct vs; inv H4.
    rewrite <- (proj1 rename_all_empty).
    apply preord_exp_refl. apply preord_env_P_refl.    
  - assert (length (a::xs) = length vs).
    eapply setlist_length_eq. apply H0.
    destruct vs; simpl in H3.
    inv H3.
    simpl in H0.
    assert (length ys = length (v::vs)).
    eapply getlist_length_eq. apply H.
    destruct ys; simpl in H3. inv H4.
    simpl in H.
    destruct (M.get e rho2) eqn:ger2.
    destruct (getlist ys rho2) eqn:glyr2.
    destruct (setlist xs vs rho2) eqn:slxr2.
    Focus 2. inv H0.
    Focus 2. inv H.
    Focus 2. inv H.
    simpl set_list.
    inv H.
    inversion Nb; subst.
    specialize (IHxs _ _ _ _  H7 glyr2 slxr2).
    clear H7 H6.
    inv H0.
    
    assert (rename_clos_s a e fb (rename e a fb)).
    {
      apply (proj1 (rename_corresp e a)).
      eapply Disjoint_Included_r; eauto.
      intro. intro. constructor. inv H. auto.
      inv H0.
    }            
    eapply preord_exp_trans.
    eapply preord_exp_trans.
    eapply preord_rename_clos_s. 2: apply H.     
    eapply Disjoint_FromList_r. apply H1.
    constructor; auto.
    destruct (var_dec e a). subst.
    rewrite M.gss. auto. 
    rewrite M.gso by auto.
    erewrite <- setlist_not_In.
    apply ger2.
    apply slxr2.
    intro. inv H2. 
    specialize (H5 e).
    apply H5.
    split. constructor. auto.
    constructor 2. apply H0.
    intros.
    assert (e <> a). intro. inv H2. specialize (H5 a). apply H5; split; constructor; auto.
    eapply preord_exp_refl.
    apply preord_env_P_set_not_in_P_l.
    apply preord_env_P_refl.
    apply rename_not_occurs_free. auto.
    intro.
    eapply preord_exp_trans.
    apply IHxs.
    apply rename_clos_s_included in H. 
    rewrite <- bound_var_rename; eauto.
    eapply Disjoint_FromList_cons. eauto.    
    eapply Disjoint_FromList_cons.
    apply Disjoint_sym.
    eapply Disjoint_FromList_cons.
    apply Disjoint_sym.
    eauto.
    rewrite  (proj1 (one_rename_all' e a)).
    intro.
    rewrite set_list_eqn.
    apply preord_exp_refl.
    apply preord_env_P_refl.
    apply setlist_empty_not_in.
    intro.
    inv H2. specialize (H5 e).
    apply H5. split; auto.
    constructor; auto.
    constructor 2; auto.
Qed.


Theorem Disjoint_bindings_find_def: forall f t xs fb fds,
 unique_bindings_fundefs fds ->
  find_def f fds = Some (t, xs, fb) ->
  Disjoint var (bound_var fb) (FromList xs).
Proof.
  induction fds; intros.
  simpl in H0. destruct (M.elt_eq f v).
  - inv H0.
    inv H. auto.
  - inv H.
    apply IHfds; eauto.
  - inv H0.
Qed.

Theorem find_def_free_included:
  forall f t xs fb fds,
  find_def f fds = Some (t, xs, fb) -> 
  Included  _
          (Setminus var (Setminus var (occurs_free fb) (FromList xs))
             (name_in_fundefs fds))
          (occurs_free_fundefs fds).
Proof.
  induction fds.
  - intros.
    simpl in H.
    rewrite occurs_free_fundefs_Fcons.
    destruct (M.elt_eq f v).    
    + subst. inv H.
      simpl.
      eauto 20 with Ensembles_DB.
    + apply IHfds in H.
      simpl.      
      intro. intros.
      right.
      
      assert (In var (occurs_free_fundefs fds) x).
      apply H. inv H0.
      constructor. auto. intro. apply H2. right; auto.
      constructor. auto.
      inv H0. intro.
      apply H3. left. auto.
  -   intros. inv H.
Qed.


(* Main lemma for function inlining *)
Theorem rw_fun_corr:
  forall f fds t xs fb vs c rho1 rho2 k,
  find_def f fds = Some (t, xs, fb) ->
  (* next few can be deduced from unique_binding and closed top level *)
  Disjoint _ (Union _ (FromList xs) (bound_var fb)) (FromList vs) ->
  unique_name_fundefs fds -> 
  Disjoint var (bound_stem_ctx c) (occurs_free_fundefs fds)  ->
  Disjoint var (bound_stem_ctx c) (name_in_fundefs fds)  -> 
  List.NoDup xs ->
  preord_env_P pr cenv (occurs_free (Efun fds (c |[ Eapp f t vs ]|))) k rho1 rho2 ->
  preord_exp pr cenv k (Efun fds (c |[ Eapp f t vs ]|), rho1)
                             (Efun fds (c |[ (rename_all (set_list (combine xs vs) (M.empty var)) fb)]|), rho2).
Proof.
  intros f fds t xs fb vs c rho1 rho2 k H H0 Hub H1 H2 H3 H4.
  apply fun_inline_compat_clos; auto.
  (* probably want this compat clos to also show that fds is already bound to the right things in rho2' *)
  intros.

  destruct k'.
  intro. intros. inv H9. inv H10. exfalso; omega.
  destruct (M.get f rho1') eqn:gfr'.
  Focus 2. intro; intros. inv H10. rewrite H14 in gfr'. inv gfr'.
  destruct v.
  intro; intros. inv H10. rewrite H14 in gfr'. inv gfr'.
  Focus 2. intro; intros. inv H10. rewrite H14 in gfr'. inv gfr'.
  destruct (getlist vs rho1') eqn:gvsr1'.
  Focus 2. intro; intros. inv H10. rewrite H15 in gvsr1'. inv gvsr1'.
  destruct (find_def v f0) eqn:fdffl. destruct p.
  Focus 2. intro. intros. inv H10. rewrite H14 in gfr'. inv gfr'. rewrite fdffl in H17. inv H17.
  destruct p.
  destruct (setlist l0 l (def_funs f0 f0 t0 t0)) eqn:Hr1'.
  Focus 2. intro. intros. inv H10. rewrite H14 in gfr'. inv gfr'. rewrite fdffl in H17. inv H17.
  rewrite gvsr1' in H15. inv H15.
  rewrite Hr1' in H20. inv H20.
  assert (v = f /\ f1 = t /\ l0 = xs /\ f0 = fds /\ e = fb /\ t0 = rho1).
  rewrite <- H7 in gfr'.
  rewrite def_funs_eq in gfr'. inv gfr'; subst.
  rewrite H in fdffl. inv fdffl. split; auto.
  eapply find_def_name_in_fundefs.
  eauto.
  right.
  eapply find_def_name_in_fundefs.
  eauto.
  destructAll.
  clear fdffl.
  assert (Included var (FromList vs) (occurs_free (Eapp f t vs))). rewrite occurs_free_Eapp. left. auto.
  assert (gvsr2' := preord_env_P_getlist_l _ _ _ _ _ _ _ _ H6 H9 gvsr1').
  destructAll. 
  assert (length xs = length x).  
  apply setlist_length_eq in Hr1'.
  apply getlist_length_eq in H10.
  apply getlist_length_eq in gvsr1'.
  rewrite <- H10.
  rewrite gvsr1'. apply Hr1'.
  assert (Hsr2' := setlist_length3 rho2' _ _ H12).
  assert (Hsr2'' := setlist_length3 (def_funs fds fds rho2' rho2')  _ _ H12).
  destructAll.
  (* setup done *)
  
  eapply preord_exp_trans.
  Focus 2.
  intro.
  eapply setlist_rename_all; eauto.
  
  eapply Disjoint_Included_l; eauto. right. auto.
  apply Disjoint_sym.
  eapply Disjoint_Included_l; eauto. left; auto.
  eapply preord_exp_trans. 
  (* App -> body *)
  replace (S k') with (k' + 1) by omega.
  eapply fun_inline_rw; eauto.
  eapply Forall2_monotonic.
  2: apply H11. intros.
  eapply preord_val_monotonic. apply H15. auto.
  eapply preord_env_P_trans. Focus 2.
  intro.
  eapply preord_env_P_antimon.
  eapply eq_env_preord.
  apply H8.
  left; auto.
  apply preord_env_P_def_funs_not_in_P_r. rewrite occurs_free_Efun in H4.
  eapply preord_env_P_antimon.
  eapply preord_env_P_monotonic.
  2: apply H4. omega.
  left; auto.
  apply name_not_free_in_fds.

 (* fb =~ fb w/o def_funs fds*) 
  intro.
  apply preord_exp_refl.
  eapply preord_env_P_setlist_l with (P1 := Setminus _ (occurs_free fb) (FromList xs)).
  5: apply H14.
  4: apply H13.
  Focus 3. apply Forall2_refl. apply preord_val_refl.
  Focus 2. intros. split; auto.
  eapply preord_env_P_trans.
  {
  apply preord_env_P_def_funs_cor with (rho' := rho2).
  intro. intros.
  assert (Hv := Decidable_name_in_fundefs fds).
  destruct Hv. specialize (Dec x2). destruct Dec.
  inv H15. inv H17. exfalso. apply H18; auto.
  exfalso. assert (Disjoint var (occurs_free_fundefs fds) (name_in_fundefs fds)) by  apply name_not_free_in_fds.
  inv H15. specialize (H18 x2). apply H18. split; auto.
  intro.   intros.
  rewrite <- H8 in H17.
  Focus 2. left. inv H15.
  eapply find_def_free_included. apply H. apply H18.
  auto.
  rewrite def_funs_neq in H17. exists v1. split; auto. apply preord_val_refl. auto.
  }
  intros. eapply preord_env_P_antimon. 
  apply eq_env_preord.  apply H8.
  {
    intro. intros.
    assert (Hv := Decidable_name_in_fundefs fds).
    destruct Hv. specialize (Dec x2). destruct Dec.
    right. auto.
    left. eapply find_def_free_included. apply H.
    split; auto.
  }  
Qed.


  

(* can be restricted to bound_var on the path to hole in c *)
Theorem occurs_free_app_bound_var x e:        
  occurs_free e x ->
  ( forall c,
  ~ occurs_free (c |[e]|) x ->
  bound_var_ctx c x) /\
( forall fds,
  ~ occurs_free_fundefs (fds <[e]>) x ->
  bound_var_fundefs_ctx fds x).
Proof.
  intro H.
  apply exp_fundefs_ctx_mutual_ind; intros.
  + exfalso. apply H0. apply H.
  + simpl in H1.
    destruct (var_dec v x).
    subst. constructor.
    constructor 2. apply H0. intro. apply H1.
    apply occurs_free_Econstr.
    right.
    split; auto.
  + simpl in H1.
    destruct (var_dec v x).
    subst. constructor.
    constructor. apply H0. intro. apply H1.
    apply occurs_free_Eproj.
    right.
    split; auto.
  + simpl in H1.
    destruct (var_dec v x).
    subst. constructor.
    constructor. apply H0. intro. apply H1.
    apply occurs_free_Eprim.
    right.
    split; auto.
  + constructor. apply H0.
    intro.
    apply H1.
    simpl.
    eapply occurs_free_Ecase_Included.
    2: apply H2.
    apply in_app. right. constructor; auto.
  + simpl in H1.
    assert (Hv := Decidable_name_in_fundefs f4).
    destruct Hv. specialize (Dec x). destruct Dec.
    constructor.
    apply name_in_fundefs_bound_var_fundefs.
    auto.
    apply Bound_Fun12_c. apply H0. intro.
    apply H1.
    apply Free_Efun1; auto.
  + simpl in H1.
    constructor.
    apply H0. intro.
    apply H1.
    apply Free_Efun2.
    auto.
  + simpl in H1.
    assert (Hv := Decidable_name_in_fundefs (Fcons v t l (e0 |[ e ]|) f6)).
    destruct Hv. specialize (Dec x). destruct Dec.
    inv H2.
    inv H3. 
    constructor. 
    constructor 4.
    apply name_in_fundefs_bound_var_fundefs. auto.
    assert (Hl := Decidable_FromList l).
    destruct Hl. specialize (Dec x). destruct Dec.
    constructor 2. auto.
    constructor 3. apply H0. intro. apply H1. constructor; auto.
    intro. apply H2. subst. constructor. auto.
    intro. apply H2. constructor 2. auto.
  + simpl in H1.
    assert (Hv := Decidable_name_in_fundefs (Fcons v t l e0 (f7 <[ e ]>))).
    destruct Hv. specialize (Dec x). destruct Dec.
    inv H2.
    inv H3. 
    constructor.
    apply Bound_Fcons24_c.
    eapply name_boundvar_ctx. apply H3.
    apply Bound_Fcons24_c.
    apply H0. intro. apply H1.
    constructor 2. apply H3.
    intro; apply H2. subst.
    constructor. auto.
Qed.

      Lemma ub_find_def_nodup: forall t xs fb f fds,
        unique_bindings_fundefs fds ->
        find_def f fds = Some (t,xs,fb) ->
        NoDup xs. 
      Proof.
        induction fds; intros.
        - simpl in H0. 
          inv H.
          destruct (M.elt_eq f v).
          inv H0; auto.
          apply IHfds; auto.
        -           inv H0.
      Qed.

      Theorem Disjoint_bindings_fundefs: forall t f xs fb fds, 
                                           unique_bindings_fundefs fds ->
                                           find_def f fds = Some (t, xs, fb) ->
                                           Disjoint _ (name_in_fundefs fds) (Union _ (FromList xs) (bound_var fb)).
      Proof.
        induction fds; intros.
        - simpl in H0.
          destruct (M.elt_eq f v).
          + subst.
            inv H0.
            simpl.
            inv H.
            split. intro. intro. inv H.
            inv H0.
            inv H.
            inv H1.
            apply H10; auto.
            apply H5; auto.
            inv H1.
            inv H8. specialize (H1 x). apply H1. split; auto.
            apply name_in_fundefs_bound_var_fundefs. auto.
            inv H9. specialize (H1 x). apply H1. split; auto.
            apply name_in_fundefs_bound_var_fundefs. auto.
          + inv H. simpl. specialize (IHfds H14 H0).
            apply Union_Disjoint_l; auto.
            split. intro. intro. destruct H. inv H.
            inv H1.
            apply H7.
            eapply name_boundvar_arg.
            apply H. apply H0.
            apply H7.
            eapply bv_in_find_def.
            apply H0. apply H.
        - inv H0.
      Qed.        


Lemma rw_correct e e' :
  gr_clos e e' ->
  forall rho rho' k, 
  preord_env_P pr cenv (occurs_free e) k rho rho'->
  preord_exp pr cenv k (e, rho) (e', rho'). 
Proof with now eauto.
  intros H.
  induction H; intros.
  - intros.
    inv H.
    inv H1.
    + apply preord_exp_compat; auto.
      intros.
      apply rm_constr; auto.
    + apply preord_exp_compat; auto.
      intros.
      apply rm_prim; auto.
    + apply preord_exp_compat; auto.
      intros.
      apply rm_proj; auto.
    + apply preord_exp_compat; auto. 
      intros.
      apply rm_fundefs_of; auto.
    + eapply preord_exp_compat; auto.
      intros.
      eapply rm_any_fundefs; auto.
    + eapply preord_exp_compat; auto.
      intros.
      apply rw_case_equiv; auto.

    + eapply preord_exp_compat; auto.
      intros.
      apply rw_proj_equiv; auto.
    + eapply preord_exp_compat; auto.
      intros.
      
      apply rw_fun_corr; auto.
  - apply preord_exp_refl; auto.
  - eapply preord_exp_trans; eauto.
    intros.
    eapply IHclos_refl_trans2.
    apply preord_env_P_refl.    
Qed.

End Shrink_correct.





Theorem bound_var_rename_all:
    (forall e sigma,
       Same_set _ (bound_var e) (bound_var (rename_all sigma e))) /\
    (forall fds sigma,
     Same_set _ (bound_var_fundefs fds) (bound_var_fundefs (rename_all_fun sigma fds))).
Proof.
  apply exp_def_mutual_ind; intros; simpl.
  - do 2 (rewrite bound_var_Econstr).
    rewrite H. reflexivity.
  - do 2 (rewrite bound_var_Ecase_nil). reflexivity.
  - do 2 (rewrite bound_var_Ecase_cons). rewrite <- H. simpl in H0. rewrite <- H0. reflexivity.
  - do 2 (rewrite bound_var_Eproj). rewrite <- H. reflexivity.
  - do 2 (rewrite bound_var_Efun). rewrite <- H. rewrite <- H0. reflexivity.
  - do 2 (rewrite bound_var_Eapp).
    reflexivity.
  - do 2 (rewrite bound_var_Eprim).
    rewrite <- H.
    reflexivity.
  - do 2 (rewrite bound_var_Ehalt).
    reflexivity.
  - do 2 (rewrite bound_var_fundefs_Fcons).
    rewrite <- H.
    rewrite <- H0.
    reflexivity.
  - rewrite bound_var_fundefs_Fnil.
    reflexivity.
Qed.

Theorem bound_var_rename_all_ns_mut:
  forall sigma, 
    (forall (e : exp),
       bound_var e <--> bound_var (rename_all_ns sigma e)) /\
    (forall (fds : fundefs),
       bound_var_fundefs fds <--> bound_var_fundefs (rename_all_fun_ns sigma fds)).
Proof.
  intro sig.
  apply exp_def_mutual_ind; intros; simpl; repeat (normalize_bound_var); split; try (rewrite H); try (rewrite H0); auto with Ensembles_DB.
Qed.

Theorem bound_var_rename_all_ns:
    (forall (e : exp) sigma,
       bound_var e <--> bound_var (rename_all_ns sigma e)).
Proof.
  intros. apply bound_var_rename_all_ns_mut.
Qed.

Theorem bound_var_rename_all_ns_fundefs:
    (forall (fds : fundefs) sigma,
       bound_var_fundefs fds <--> bound_var_fundefs (rename_all_fun_ns sigma fds)).
Proof.
  intros. apply bound_var_rename_all_ns_mut.
Qed.


(* could prove <-> *)
Theorem unique_bindings_rename_all:
  (forall e sigma,
     unique_bindings e -> unique_bindings (rename_all sigma e)) /\
  (forall fds sigma,
     unique_bindings_fundefs fds -> unique_bindings_fundefs (rename_all_fun sigma fds)).
Proof.
  apply exp_def_mutual_ind; intros; simpl.
  - inv H0. eapply H in H6.
    constructor; eauto.
    intro. apply H3.
    eapply (proj1 bound_var_rename_all).
    apply H0.
  - constructor.
  - inv H1.
    constructor.
    eapply H0 in H5.
    simpl in H5. apply H5.
    apply H. auto.
    rewrite <- (proj1 bound_var_rename_all).
    rewrite (proj1 bound_var_rename_all) with (e := (Ecase v l)) in H8.
    simpl in H8.
    apply H8.
  - inv H0.
    constructor; auto.
    intro; apply H3.
    eapply (proj1 bound_var_rename_all).
    eauto.
  - inv H1.
    constructor.
    apply H0. auto.
    apply H; auto.
    rewrite <- (proj1 bound_var_rename_all).
    rewrite <- (proj2 bound_var_rename_all).
    auto. 
  - constructor.
  - inv H0; constructor.
    intro; apply H3.
    eapply (proj1 bound_var_rename_all).
    apply H0.
    apply H.
    auto.
  - constructor.
  - inv H1.
    constructor; auto.
    intro; apply H7.
    eapply (proj1 bound_var_rename_all).
    eauto.
    intro; apply H8.
    eapply (proj2 bound_var_rename_all).
    eauto.
    rewrite <- (proj1 bound_var_rename_all). auto.
    rewrite <- (proj2 bound_var_rename_all). auto.
    rewrite <- (proj1 bound_var_rename_all).
    rewrite <- (proj2 bound_var_rename_all).
    auto.
  - constructor.
Qed.

Theorem unique_bindings_rename_all_ns:
  (forall e sigma,
     unique_bindings e -> unique_bindings (rename_all_ns sigma e)) /\
  (forall fds sigma,
     unique_bindings_fundefs fds -> unique_bindings_fundefs (rename_all_fun_ns sigma fds)).
Proof.
  apply exp_def_mutual_ind; intros; simpl.
  - inv H0. eapply H in H6.
    constructor; eauto.
    intro. apply H3.
    eapply (bound_var_rename_all_ns).
    apply H0.
  - constructor.
  - inv H1.
    constructor.
    eapply H0 in H5.
    simpl in H5. apply H5.
    apply H. auto.
    rewrite <- (bound_var_rename_all_ns).
    rewrite (bound_var_rename_all_ns) with (e := (Ecase v l)) in H8.
    simpl in H8.
    apply H8.
  - inv H0.
    constructor; auto.
    intro; apply H3.
    eapply (bound_var_rename_all_ns).
    eauto.
  - inv H1.
    constructor.
    apply H0. auto.
    apply H; auto.
    rewrite <- (bound_var_rename_all_ns).
    rewrite <- (bound_var_rename_all_ns_fundefs).
    auto. 
  - constructor.
  - inv H0; constructor.
    intro; apply H3.
    eapply (bound_var_rename_all_ns).
    apply H0.
    apply H.
    auto.
  - constructor.
  - inv H1.
    constructor; auto.
    intro; apply H7.
    eapply (bound_var_rename_all_ns).
    eauto.
    intro; apply H8.
    eapply (bound_var_rename_all_ns_fundefs).
    eauto.
    rewrite <- (bound_var_rename_all_ns). auto.
    rewrite <- (bound_var_rename_all_ns_fundefs). auto.
    rewrite <- (bound_var_rename_all_ns).
    rewrite <- (bound_var_rename_all_ns_fundefs).
    auto.
  - constructor.
Qed.

Theorem ub_fun_inlining: forall B1   xs fb B2 c f t vs c',
  unique_bindings (c' |[ Efun (fundefs_append B1 (Fcons f t xs fb B2)) (c |[ Eapp f t vs ]|) ]|)  ->
  unique_bindings (c' |[ Efun (fundefs_append B1 B2) (c |[ (rename_all_ns (set_list (combine xs vs) (M.empty var)) fb) ]|) ]|).
Proof.
  intros.
  apply ub_app_ctx_f.
  apply ub_app_ctx_f in H.
  destructAll.
  split; auto.
  rewrite inv_app_Efun1 in H0. rewrite app_ctx_f_fuse in H0.
  apply ub_app_ctx_f in H0.
  destructAll.
  split.

  rewrite inv_app_Efun1. rewrite app_ctx_f_fuse.
  apply ub_app_ctx_f.
  split.
  
  {
  simpl.
  simpl in H0. inv H0.
  constructor; eauto.
  eapply fundefs_append_unique_bindings_l in H7.
  2: reflexivity.
  destructAll.
  eapply fundefs_append_unique_bindings_r; eauto. inv H4. auto.
  eapply Disjoint_Included_r. 2: apply H5.
  rewrite bound_var_fundefs_Fcons. right; right; right;  auto.
  eapply Disjoint_Included_r. 2: apply H8.
  rewrite fundefs_append_bound_vars.
  2: reflexivity.
  intro. intros.
  rewrite fundefs_append_bound_vars.  2: reflexivity.
  inv H0. left; auto.
  right.
  rewrite bound_var_fundefs_Fcons.
  right; right; right; auto.
  }
  split.

  apply unique_bindings_rename_all_ns.
  simpl in H0. inv H0.
  eapply fundefs_append_unique_bindings_l in H7. 2: reflexivity. destructAll.
  inv H4. auto.
  
  simpl. rewrite bound_var_Fun1_c.
  rewrite <- bound_var_rename_all_ns.
  simpl in H0. inv H0. 
  apply Union_Disjoint_l.

  rewrite fundefs_append_bound_vars.
  2: reflexivity.
  apply Union_Disjoint_l.
  
  eapply fundefs_append_unique_bindings_l in H7.
  2: apply reflexivity.
  destructAll.
  eapply Disjoint_Included_r. 2: apply H5. rewrite bound_var_fundefs_Fcons. right; right; left; auto.
  eapply fundefs_append_unique_bindings_l in H7.
  2: apply reflexivity.
  destructAll.
  inv H4. apply Disjoint_sym.
  auto.

  eapply Disjoint_Included_r.
  2: apply H8.
  rewrite fundefs_append_bound_vars.
  2: reflexivity.
  right. constructor 3. auto.

  eapply Disjoint_Included_r.
  2: apply H1.
  do 2 (rewrite bound_var_Efun).
  do 2 (rewrite bound_var_app_ctx).
  erewrite fundefs_append_bound_vars. 2: reflexivity.
  intro. intros.
  erewrite fundefs_append_bound_vars. 2: reflexivity.
  rewrite bound_var_fundefs_Fcons.
  inv H4. inv H5. eauto with Ensembles_DB.
  left; right; right; right; right. auto.
  inv H5.
  right. left; auto.
  left; right; right; right; left. rewrite <- bound_var_rename_all_ns in H4.  auto. 
Qed.

Theorem ub_constr_dead: forall c x t ys e,
    unique_bindings (c |[ Econstr x t ys e]|)  ->
    unique_bindings (c |[e]|).
Proof.
  intros.
  apply ub_app_ctx_f in H.
  apply ub_app_ctx_f.
  destructAll.
  split; auto.
  inv H0.
  split; auto.
  eapply Disjoint_Included_r.
  2: apply H1.
  rewrite bound_var_Econstr.
  left; auto.
Qed.

Theorem ub_prim_dead: forall c x t ys e,
    unique_bindings (c |[ Eprim x t ys e]|)  ->
    unique_bindings (c |[e]|).
Proof.
  intros.
  apply ub_app_ctx_f in H.
  apply ub_app_ctx_f.
  destructAll.
  split; auto.
  inv H0.
  split; auto.
  eapply Disjoint_Included_r.
  2: apply H1.
  rewrite bound_var_Eprim.
  left; auto.
Qed.

Theorem ub_proj_dead: forall c x t n y e,
    unique_bindings (c |[ Eproj x t n y e]|)  ->
    unique_bindings (c |[e]|).
Proof.
  intros.
  apply ub_app_ctx_f in H.
  apply ub_app_ctx_f.
  destructAll.
  split; auto.
  inv H0.
  split; auto.
  eapply Disjoint_Included_r.
  2: apply H1.
  rewrite bound_var_Eproj.
  left; auto.
Qed.

Theorem ub_fun_dead: forall c fds e,
    unique_bindings (c |[ Efun fds e]|)  ->
    unique_bindings (c |[e]|).
Proof.
  intros.
  apply ub_app_ctx_f in H.
  apply ub_app_ctx_f.
  destructAll.
  split; auto.
  inv H0.
  split; auto.
  eapply Disjoint_Included_r.
  2: apply H1.
  rewrite bound_var_Efun.
  right; auto.
Qed.

Theorem ub_case_inl: forall c x cl e,
                       (exists co, findtag cl co = Some e) ->
                       unique_bindings (c |[ Ecase x cl ]|) ->
                       unique_bindings (c |[ e]|).
Proof.
  intros.
  apply ub_app_ctx_f.
  apply ub_app_ctx_f in H0.
  destructAll.
  apply findtag_In in H.
  apply in_split in H.
  destructAll.
  rewrite bound_var_Ecase_app in H2.
  rewrite bound_var_Ecase_cons in H2.
  apply unique_bindings_Ecase_l in H1.
  destructAll.
  split; auto.
  split; auto.
  eapply Disjoint_Included_r.
  2: apply H2.
  right; left; auto.
Qed.


Section occurs_free_rw.
  (* for each rw e e', OF e' \subset OF e *)
  
(* restricted form of occurs_free_ctx_mut to inclusion *)
Theorem occurs_free_ctx_mut_included:
  (forall c e e',
  Included _ (occurs_free e) (occurs_free e') ->
  Included _ (occurs_free (c|[ e]|)) (occurs_free (c|[ e']|))) /\
  (forall fds e e',
  Included _ (occurs_free e) (occurs_free e') ->
  Included _ (occurs_free_fundefs (fds <[ e]>)) (occurs_free_fundefs (fds<[ e']>))).
Proof with eauto with Ensembles_DB.
  exp_fundefs_ctx_induction IHc IHf; eauto; simpl;
  intros; repeat normalize_occurs_free;
  try (rewrite IHc; [| eassumption ]); try (rewrite IHB; [| eassumption ]);
  eauto with Ensembles_DB.
  rewrite name_in_fundefs_ctx...
  rewrite name_in_fundefs_ctx...  
Qed.

Theorem occurs_free_exp_ctx_included:
  forall c e e',
    Included _ (occurs_free e) (occurs_free e') ->
    Included _ (occurs_free (c|[ e]|)) (occurs_free (c|[ e']|)).
Proof.
  apply (proj1 occurs_free_ctx_mut_included).
Qed.

Theorem occurs_free_fundefs_ctx_included:
  forall fds e e',
    Included _ (occurs_free e) (occurs_free e') ->
    Included _ (occurs_free_fundefs (fds <[ e]>)) (occurs_free_fundefs (fds<[ e']>)).
Proof.
  apply (proj2 occurs_free_ctx_mut_included).
Qed.



Theorem of_constr_dead: forall c x t ys e,
                          num_occur e x 0 ->
                          Included _ (occurs_free (c |[ e ]|)) (occurs_free (c |[ Econstr x t ys e ]|)).
Proof.
  intros. 
  apply occurs_free_exp_ctx_included.
  rewrite occurs_free_Econstr.
  apply not_occurs_not_free in H.
  eauto with Ensembles_DB.
Qed.

Theorem of_prim_dead: forall c x t ys e,
                          num_occur e x 0 ->
                          Included _ (occurs_free (c |[ e ]|)) (occurs_free (c |[ Eprim x t ys e ]|)).
Proof.
  intros. 
  apply occurs_free_exp_ctx_included.
  rewrite occurs_free_Eprim.
  apply not_occurs_not_free in H.
  eauto with Ensembles_DB.
Qed.


Theorem of_proj_dead: forall c x t n y e,
                          num_occur e x 0 ->
                          Included _ (occurs_free (c |[ e ]|)) (occurs_free (c |[ Eproj x t n y e ]|)).
Proof.
  intros. 
  apply occurs_free_exp_ctx_included.
  rewrite occurs_free_Eproj.
  apply not_occurs_not_free in H.
  eauto with Ensembles_DB.
Qed.

Theorem of_fun_dead: forall c fds e,
                       Forall (fun v => num_occur e v 0) (all_fun_name fds) ->
                          Included _ (occurs_free (c |[ e ]|)) (occurs_free (c |[ Efun fds e]|)).
Proof.
  intros. 
  apply occurs_free_exp_ctx_included.
  rewrite occurs_free_Efun.
  apply disjoint_not_occurs_fun in H.
  eauto with Ensembles_DB.
Qed.


Theorem included_of_fundefs_append_r: forall B2 B2' B1, 
                                        Included _ (occurs_free_fundefs B2) (occurs_free_fundefs B2') ->
                                        Included _ (name_in_fundefs B2') (name_in_fundefs B2) ->
                                      Included _ (occurs_free_fundefs (fundefs_append B1 B2)) (occurs_free_fundefs (fundefs_append B1 B2')).
  Proof.
    induction B1; intros.
    - simpl.
      repeat normalize_occurs_free.
      specialize (IHB1 H H0).      
      apply Included_Union_compat.
      + apply Included_Setminus_compat.
        reflexivity.
        apply Included_Union_compat. reflexivity.
        apply Included_Union_compat. reflexivity.
        intro.
        intros.
        eapply fundefs_append_name_in_fundefs in H1.
        2: reflexivity.
        eapply fundefs_append_name_in_fundefs.
        reflexivity.
        inv H1. left; auto.
        right.
        apply H0. auto.
      + eauto with Ensembles_DB.
    - simpl. auto.
  Qed.

  
         (* local version *)         
Theorem of_fun_rm': forall f t xs fb B1 B2 e,
                       unique_bindings_fundefs (fundefs_append B1 (Fcons f t xs fb B2)) ->
                       num_occur (Efun (fundefs_append B1 (Fcons f t xs fb B2)) e) f 0 -> 
                          Included _ (occurs_free (Efun (fundefs_append B1 B2) e )) (occurs_free (Efun (fundefs_append B1 (Fcons f t xs fb B2)) e)). 
Proof.
  intros.
  repeat normalize_occurs_free.
  rewrite fundefs_append_name_in_fundefs.
  2: reflexivity.  
  rewrite fundefs_append_name_in_fundefs with (B3 := (fundefs_append B1 (Fcons f t xs fb B2))).
  2: reflexivity.
  simpl.

  inv H0. apply plus_is_O in H3. destruct H3. subst.
  apply fundefs_append_num_occur' in H6.
  destructAll.
  apply plus_is_O in H2. destructAll.


  inv H1. apply plus_is_O in H10.
  destructAll.
  apply not_occurs_not_free in H5.
  apply not_occurs_not_free in H11.
  apply not_occurs_not_free in H9.
  
  apply Included_Union_compat.

  {
    clear H.
    induction B1.
    + inv H0; pi0.
      specialize (IHB1 H10).
      simpl.
      repeat normalize_occurs_free.
      apply Included_Union_compat.
      rewrite fundefs_append_name_in_fundefs.
      2: reflexivity.  
      rewrite fundefs_append_name_in_fundefs with (B3 := (fundefs_append B1 (Fcons f t xs fb B2))).
      2: reflexivity.
      simpl.
      apply not_occurs_not_free in H7.
      repeat (rewrite <- Setminus_Union).
      apply Included_Setminus_compat.
      apply Included_Setminus.
      apply Setminus_Disjoint_preserv_l.
      apply Setminus_Disjoint_preserv_l.
      apply Setminus_Disjoint_preserv_l.
      eauto with Ensembles_DB.
      reflexivity.
      reflexivity.
      eauto with Ensembles_DB.
    + simpl.
      normalize_occurs_free.
      eauto with Ensembles_DB.      
  }  

  apply not_occurs_not_free in H0.  
  eauto 25 with Ensembles_DB.    
Qed.

Theorem of_fun_rm:  forall c f t xs fb B1 B2 e,
                       unique_bindings_fundefs (fundefs_append B1 (Fcons f t xs fb B2)) ->
                       num_occur (Efun (fundefs_append B1 (Fcons f t xs fb B2)) e) f 0 -> 
                          Included _ (occurs_free (c |[ Efun (fundefs_append B1 B2) e  ]| )) (occurs_free (c |[ (Efun (fundefs_append B1 (Fcons f t xs fb B2)) e) ]|)). 
Proof.
  intros.
  apply occurs_free_exp_ctx_included.
  apply of_fun_rm'; auto.
Qed.  

Theorem of_case_fold': forall x cl co e,
  findtag cl co = Some e ->
  Included _ (occurs_free e) (occurs_free (Ecase x cl)).
Proof.
  intros.
  eapply occurs_free_Ecase_Included.
  apply findtag_In_patterns.
  eauto.
Qed.  



    
  
Theorem name_in_fundefs_rename_all_ns:
  forall sig f,
    name_in_fundefs f <--> name_in_fundefs (rename_all_fun_ns sig f).
Proof.
  induction f; simpl; eauto with Ensembles_DB.
Qed.

Theorem not_Range_map_eq {A}:
  forall sig (x:A),
  ~ Range_map sig x ->
  ~ (exists z, M.get z sig = Some x).
Proof.
  intros. intro. apply H. inv H0. exists x0; auto.
Qed.

Theorem not_Dom_map_eq {A}:
  forall (sig:M.t A) x,
    ~ Dom_map sig x ->
    M.get x sig = None.
Proof.
  intro. intros.
  destruct (M.get x sig) eqn:gxs.
  exfalso; apply H. exists a; auto.
  auto.
Qed.

Hint Resolve not_Range_map_eq not_Dom_map_eq.

Theorem one_rename_all_ns_mut: forall y x sig,
                                 ~ Range_map sig x  ->
                                 ~ Dom_map sig x ->
                          ( forall e,
                           rename_all_ns (M.set x y (M.empty var)) (rename_all_ns sig e) =  rename_all_ns (M.set x y sig) e  ) /\
                          ( forall f,
                          rename_all_fun_ns (M.set x y (M.empty var)) (rename_all_fun_ns sig f) =  rename_all_fun_ns (M.set x y sig) f).
Proof.
  intros y x sig Hr Hd.
  eapply exp_def_mutual_ind; intros; simpl.
  - rewrite H.
    rewrite <- one_rename_all_list; auto. 
  - rewrite <- one_rename_all_ar; auto.
  - simpl in H0. inv H0.
    rewrite H. auto.
  - rewrite <- one_rename_all_ar; auto.
    rewrite H. auto.
  - rewrite H. rewrite H0. reflexivity.
  - rewrite <- one_rename_all_ar; auto.
    rewrite <- one_rename_all_list; auto.
  - rewrite <- one_rename_all_list; auto.
    rewrite H. auto.
  - rewrite <- one_rename_all_ar; auto.
  - rewrite H; rewrite H0; auto.
  - auto.
Qed.

Theorem one_rename_all_ns:
  forall y x sig,
    ( forall e,
        ~ Range_map sig x  ->
        ~ Dom_map sig x ->
        rename_all_ns (M.set x y (M.empty var)) (rename_all_ns sig e) =  rename_all_ns (M.set x y sig) e  ).
Proof.
  intros. apply one_rename_all_ns_mut; auto.
Qed. 

Theorem one_rename_all_fun_ns: forall y x sig,
                                 ( forall f,
                                                                      ~ Range_map sig x  ->
                                 ~ Dom_map sig x ->
                          rename_all_fun_ns (M.set x y (M.empty var)) (rename_all_fun_ns sig f) =  rename_all_fun_ns (M.set x y sig) f).
Proof.
  intros. apply one_rename_all_ns_mut; auto.
Qed. 



Theorem of_rename_all_ns_mut: 
(forall e sigma, (occurs_free (rename_all_ns sigma e)) \subset
                                    Union _ (Setminus _ (occurs_free e) (Dom_map sigma)) (Range_map sigma))
/\
(forall fds sigma, (occurs_free_fundefs (rename_all_fun_ns sigma fds)) \subset
                                    Union _ (Setminus _ (occurs_free_fundefs fds) (Dom_map sigma)) (Range_map sigma)).
Proof.
  apply exp_def_mutual_ind; intros.
  - simpl.
    repeat normalize_occurs_free.
    apply Union_Included.
    + eapply Included_trans.
      apply FromList_apply_r_list.
      eauto with Ensembles_DB.
    + apply Setminus_Included_Included_Union.
      eapply Included_trans.
      apply H.
      intro.
      intros. inv H0.
      destruct (var_dec x v).
      * subst. right. constructor.
      * inv H1.
        left. left. split.
        right. split; auto.
        intro. apply n; inv H1.
        auto.
        auto.
      * auto.         
  - simpl.
    repeat normalize_occurs_free.
    intro. intros.
    inv H.
    apply apply_r_sigma_in.
  - simpl.
    repeat normalize_occurs_free.
    specialize (H sigma).
    specialize (H0 sigma).
    repeat (apply Union_Included).
    + eapply Included_trans.
      intro; intro.
      inv H1.
      apply apply_r_sigma_in.
      eauto with Ensembles_DB.
    + eapply Included_trans.
      apply H.
      eauto with Ensembles_DB.
    + eapply Included_trans.
      apply H0.
      eauto with Ensembles_DB.
  - simpl.
    repeat normalize_occurs_free.
        apply Union_Included.
    + eapply Included_trans.
      intro. intro. inv H0.
      apply apply_r_sigma_in.
      eauto with Ensembles_DB.
    + apply Setminus_Included_Included_Union.
      eapply Included_trans.
      apply H.
      intro.
      intros. inv H0.
      destruct (var_dec x v).
      * subst. right. constructor.
      * inv H1.
        left. left. split.
        right. split; auto.
        intro. apply n0; inv H1.
        auto.
        auto.
      * eauto.
  - simpl.
    repeat normalize_occurs_free.
    apply Union_Included.
    + eapply Included_trans.
      apply H.
      eauto with Ensembles_DB.
    + apply Setminus_Included_Included_Union.
      eapply Included_trans.
      apply H0.
      apply Union_Included.      
      * intro. intro.
        inv H1.
        assert (Hh := Decidable_name_in_fundefs f2).
        inv Hh. specialize (Dec x).
        destruct Dec.
        right.
        apply name_in_fundefs_rename_all_ns. auto. 
        left.  left. split. right. split; auto.
        intro; apply H3. 
        auto.
      * left; right.
        auto.
  - simpl.
    repeat normalize_occurs_free.
    apply Union_Included.
    eapply Included_trans.
    apply FromList_apply_r_list.
    eauto with Ensembles_DB.
    eapply Included_trans.
    intro. intro. inv H.
    apply apply_r_sigma_in.
    eauto with Ensembles_DB.
  -  simpl.
    repeat normalize_occurs_free.
        apply Union_Included.
    + eapply Included_trans.
      apply FromList_apply_r_list.
      eauto with Ensembles_DB.
    + apply Setminus_Included_Included_Union.
      eapply Included_trans.
      apply H.
      intro.
      intros. inv H0.
      destruct (var_dec x v).
      * subst. right. constructor.
      * inv H1.
        left. left. split.
        right. split; auto.
        intro. apply n; inv H1.
        auto.
        intro.
        apply H2.
        auto.
      * eauto.
  - simpl.
    rewrite occurs_free_Ehalt.
    rewrite occurs_free_Ehalt.
    intro. intro. inv H. apply apply_r_sigma_in.
  - simpl.
    repeat normalize_occurs_free.

    apply Union_Included.
    + intro. intro. inv H1. apply H in H2.
      inv H2.
      left. inv H1.
      split.
      left. split; auto.
      intro.
      inv H1. apply H3; auto.
      rewrite <- name_in_fundefs_rename_all_ns in H3. 
      apply H3; auto.
      auto.
      right.
      auto.
    + intro. intro. inv H1.
      apply H0 in H2.
      inv H2.
      inv H1. left.
      split; auto.
      right. split; auto.
      auto.
  - simpl.
    intro. intro. inv H.
Qed.


        
Theorem of_fun_inline':
  forall f fds t xs fb vs,
    find_def f fds = Some (t, xs, fb) ->
    length xs = length vs ->
  (Setminus var
            (occurs_free
               (rename_all_ns (set_list (combine xs vs) (M.empty var)) fb))
            (name_in_fundefs fds)) \subset
  Union var (occurs_free_fundefs fds)
  (Setminus var (occurs_free ( Eapp f t vs)) (name_in_fundefs fds)).
Proof.
  intros.
  eapply Included_trans.
  eapply Included_Setminus_compat.
  apply of_rename_all_ns_mut.
  reflexivity.
  eapply Included_trans.
  apply Setminus_Union_distr.
  apply find_def_free_included in H.
  apply Union_Included.
  - eapply Included_trans.
    rewrite Dom_map_setlist_ss; auto.
    apply H.
    left; auto.
  - apply Setminus_Included_Included_Union.
    eapply Included_trans.
    apply Range_map_setlist.
    rewrite occurs_free_Eapp.
    intro. intro.
    assert (Hh := Decidable_name_in_fundefs fds).
    destruct Hh.
    specialize (Dec x).
    destruct Dec.
    right; auto.
    left. right.
    split.
    left; auto.
    apply H2.
Qed.


Theorem of_fun_inline'':
  forall f fds t xs fb vs,
    find_def f fds = Some (t, xs, fb) ->
    length xs = length vs ->
    Union var 
          (occurs_free
             (rename_all_ns (set_list (combine xs vs) (M.empty var)) fb))
          (Union var 
                 (name_in_fundefs fds)
                 (occurs_free_fundefs fds))
          \subset
  Union var (occurs_free ( Eapp f t vs))
  (Union var (name_in_fundefs fds)
             (occurs_free_fundefs fds))
.
Proof.
  intros.
  assert (Hofi := of_fun_inline' f fds t xs fb vs H H0).
  rewrite Union_assoc.
  rewrite Union_assoc.
  apply Union_Included.
  - rewrite Union_Setminus.
    apply Union_Included.
    eapply Included_trans. apply Hofi.
    eauto with Ensembles_DB.
    eauto with Ensembles_DB.
    apply Decidable_name_in_fundefs.
  - right; auto.
Qed.              


  

Theorem occurs_free_ctx_mut_included_u:
  forall S,
    Decidable S ->
  (forall c e e',
  Included _ (Union _ (occurs_free e) S) (Union _ (occurs_free e') S) ->
  Included _ (Union _ (occurs_free (c|[ e]|)) S)  (Union _ (occurs_free (c|[ e']|)) S)) /\
  (forall fds e e',
  Included _ (Union _ (occurs_free e) S) (Union _ (occurs_free e') S) ->
  Included _ (Union _ (occurs_free_fundefs (fds <[ e]>)) S)  (Union _ (occurs_free_fundefs (fds<[ e']>)) S)).
Proof with eauto with Ensembles_DB.
  intros S Hds.
  exp_fundefs_ctx_induction IHc IHf; eauto; simpl;
  intros; repeat normalize_occurs_free;
  try (rewrite IHc; [| eassumption ]); try (rewrite IHB; [| eassumption ]);
  try (
        apply IHc in H;
        rewrite <- Union_assoc;
        rewrite <- Union_assoc;
        rewrite Union_Setminus_Setminus_Union; [|auto];
        rewrite Union_Setminus_Setminus_Union; [|auto];
        eauto with Ensembles_DB).
  {
    apply IHc in H.
    repeat (rewrite <- Union_assoc).
    apply Included_Union_compat; [reflexivity|].
    apply Included_Union_compat; [reflexivity|].
    intro. intro. inv H0.
    eapply Included_Union_l in H1. apply H in H1.
    inv H1. auto. auto.
    inv H1.
    auto.
    eapply Included_Union_r in H0. apply H in H0.
    inv H0; auto.
  }    
  {
    apply IHf in H.
    rewrite name_in_fundefs_ctx with (e2 := e').
    do 2 (rewrite Union_commut with (s2 := S)).
    do 2 (rewrite  Union_assoc).
    do 2 (rewrite Union_commut with (s1 := S)).
    eauto with Ensembles_DB.
  }
  {
    apply IHc in H.
    do 2 (rewrite Union_commut with (s2 := S)).
    rewrite Union_assoc.
    rewrite Union_assoc with (s1 := S).
    
    rewrite Union_commut with (s1 := S).
    rewrite Union_commut with (s1 := S).
    rewrite Union_Setminus_Setminus_Union.
    rewrite Union_Setminus_Setminus_Union with (s3 := S).
    eauto with Ensembles_DB.
    auto.
    auto.
  }    
  {
    apply IHf in H.
    rewrite name_in_fundefs_ctx with (e2 := e').
    
    
    do 2 (rewrite Union_commut with (s2 := S)).
    do 2 (rewrite Union_commut with (s1 := (Setminus var (occurs_free e)
          (Union var [set v]
                 (Union var (FromList l) (name_in_fundefs (f7 <[ e' ]>))))))).
    rewrite Union_assoc.
    rewrite Union_assoc with (s1 := S).
    rewrite Union_commut with (s1 := S).
    rewrite Union_commut with (s1 := S).
    rewrite Union_Setminus_Setminus_Union.
    rewrite Union_Setminus_Setminus_Union with (s3 := S).
    eauto with Ensembles_DB.
    auto.
    auto.
  }
Qed.

(* todo: move *)
Theorem nthN_FromList:
  forall {A} k ys n,
  nthN ys n = Some k ->
  @FromList A ys k.
Proof.
  induction ys; intros.
  inv H.
  simpl in H.
  destruct n. inv H. constructor; auto.
  apply IHys in H.
  constructor 2. auto.
Qed.  

Theorem occurs_free_exp_ctx_included_u:
  forall c e e' S,
    Decidable S -> 
    Included _ (Union _ (occurs_free e) S) (Union _ (occurs_free e') S) ->
    Included _ (Union _ (occurs_free (c|[ e]|)) S) (Union _ (occurs_free (c|[ e']|)) S).
Proof.
  intros.
  apply occurs_free_ctx_mut_included_u; auto.
Qed.

Theorem of_case_fold: forall c' c x cl  e ys co,
  findtag cl co = Some e ->
  Included _ (occurs_free (c' |[ Econstr x co ys (c |[ e ]|) ]|)) (occurs_free (c' |[Econstr x co ys (c |[Ecase x cl]|) ]|)) .
Proof.
  intros.
  apply occurs_free_exp_ctx_included.
  do 2 (rewrite inv_app_Econstr).
  do 2 (rewrite app_ctx_f_fuse).
  apply occurs_free_exp_ctx_included.
  eapply occurs_free_Ecase_Included.
  apply findtag_In_patterns. apply H.
Qed.

  
  
  


Theorem of_fun_inline''':
  forall xs vs fb t c f fds,
    find_def f fds = Some (t, xs, fb) ->
    length xs = length vs ->
    Included _ (occurs_free (Efun fds (c |[ (rename_all_ns (set_list (combine xs vs) (M.empty var)) fb)]|)))
             (occurs_free (Efun fds (c |[ Eapp f t vs ]|))).
Proof.
  intros.
  repeat normalize_occurs_free.
  apply Union_Included.
  - left; auto.
  - assert (Hofi := of_fun_inline'' f fds t xs fb vs H H0).
    eapply occurs_free_exp_ctx_included_u with (c  := c) in Hofi.
    intro. intro.
    inv H1.
    assert (In var (Union var
           (occurs_free
              (c |[ rename_all_ns (set_list (combine xs vs) (M.empty var)) fb ]|))
           (Union var (name_in_fundefs fds) (occurs_free_fundefs fds))) x).
    left. auto.
    apply Hofi in H1.
    inv H1. right. split; auto.
    inv H4.
    exfalso; auto.
    left; auto.
    apply Decidable_Union.
    apply Decidable_name_in_fundefs.
    apply occurs_free_dec.    
Qed.



Theorem of_constr_proj':
  forall x t ys c k v e n t',
    nthN ys n = Some k  ->
  Included _
           (occurs_free (Econstr x t ys (c |[rename_all_ns (M.set v k (M.empty var)) e]|)))
           (occurs_free (Econstr x t ys (c |[Eproj v t' n x e]|))).
Proof.
  intros.
  repeat normalize_occurs_free.
  assert (Included _ (Union _ (occurs_free (c |[ rename_all_ns (M.set v k (M.empty var)) e ]|)) [set k])
                     (Union _ (occurs_free (c |[ Eproj v t' n x e ]|)) [set k])).
  eapply occurs_free_exp_ctx_included_u with (c  := c).
  split. intro. destruct (var_dec k x0); subst.
  left; constructor. right.
  intro; apply n0; auto. inv H0; auto.
  normalize_occurs_free.
  unfold rename.
  apply Union_Included.
  eapply Included_trans.

  apply of_rename_all_ns_mut.
  intro.
  intro. inv H0.
  inv H1.
  left.
  right.
  split.
  auto.
  intro.
  apply H2.
  inv H1.
  exists k.
  rewrite M.gss.
  auto.
  inv H1.
  destruct (var_dec x1 v).
  subst.
  rewrite M.gss in H0. inv H0.
  right. auto.
  rewrite M.gso in H0.
  rewrite M.gempty in H0.
  inv H0.
  auto.
  right; auto.
  intro.
  intro. inv H1.
  left; auto.
  destruct (var_dec x0 k).
  - subst. left. eapply nthN_FromList. eauto. 
  - inv H2.
    right.
    split; auto.
    eapply Included_Union_l in H1.
    apply H0 in H1.
    inv H1. auto.
    exfalso.
    apply n0. inv H2. auto.
Qed.


           
End occurs_free_rw.

Section Shrink_Rewrites.
 
(* shrink rewrites  *)
Inductive sr_rw: relation exp :=
  (* Rules about dead var elimination *)
| Constr_dead_s: forall x t ys e, 
                 num_occur e x 0 ->
                 sr_rw (Econstr x t ys e) e
| Prim_dead_s: forall x p ys e,
               num_occur e x 0 ->
               sr_rw (Eprim x p ys e) e
| Proj_dead_s: forall x t n y e,
               num_occur e x 0 ->
               sr_rw (Eproj x t n y e) e
| Fun_dead_s: forall e fds,
              Forall (fun v => num_occur e v 0) (all_fun_name fds) ->
              sr_rw (Efun fds e) e 
| Fun_rem_s: forall f t xs fb B1 B2 e,
             num_occur (Efun (fundefs_append B1 (Fcons f t xs fb B2)) e) f 0 -> 
               sr_rw (Efun (fundefs_append B1 (Fcons f t xs fb B2)) e) (Efun (fundefs_append B1 B2) e)
(* Rules about inlining/constant-folding *)
| Constr_case_s: forall x c cl co e ys,
      findtag cl co = Some e ->
      sr_rw (Econstr x co ys (c |[ Ecase x cl ]|)) (Econstr x co ys (c |[e]|))
| Constr_proj_s: forall v  t t' n x e k ys c, 
                 nthN ys n = Some k -> 
                 sr_rw (Econstr x t ys (c |[Eproj v t' n x e]|)) (Econstr x t ys (c |[ rename_all_ns (M.set v k (M.empty var)) e]|))
| Fun_inline_s: forall c  vs f  t xs fb  B1 B2,
                length xs = length vs ->
                num_occur (Efun (fundefs_append B1 (Fcons f t xs fb B2)) (c |[ Eapp f t vs ]|)) f 1 ->
                sr_rw (Efun (fundefs_append B1 (Fcons f t xs fb B2)) (c |[ Eapp f t vs ]|))
                   (Efun (fundefs_append B1 B2) (c |[ (rename_all_ns (set_list (combine xs vs) (M.empty var)) fb)]|)).                     


Inductive gen_sr_rw : relation exp :=
| Ctx_sr_rw : forall c e e',
             sr_rw e e' ->
             gen_sr_rw (c |[ e ]|) (c |[ e' ]|)
.


Definition gsr_clos := clos_refl_trans exp gen_sr_rw.


Local Hint Constructors rw.

Theorem Disjoint_dom_map :
  forall (sig:M.t M.elt) S,
  Disjoint _ (Dom_map sig) S ->
  forall (x:M.elt), In _ S x ->
    M.get x sig  = None.
Proof.
  intros. inv H. destruct (M.get x sig) eqn:gxs.
  exfalso. specialize (H1 x). apply H1. split; eauto.
  exists e. auto.
  auto.
Qed.

Notation "A =mg= B" := (map_get_r _ A B) (at level 81). 

Theorem Disjoint_dom_remove_all:
  forall l sig,
    Disjoint _ (Dom_map sig) (FromList l) -> 
    remove_all sig l =mg= sig.
Proof.
  induction l; simpl; intros.
  - apply smg_refl.
  - eapply smg_trans.
    apply IHl. 
    split. intro. intro. inv H0. inv H1.
    destruct (var_dec x a). subst. rewrite M.grs in H0; inv H0.
    rewrite M.gro in H0 by auto.
    inv H. specialize (H1 x).
    apply H1. split; eauto.
    exists x0; auto. constructor 2; auto.
    apply remove_none.
    eapply Disjoint_dom_map; eauto with Ensembles_DB.
    constructor 1; auto.
Qed.

(** If the substitution is not shadowed in e, we can replace rename_all by
     rename_all_ns which does not consider variable captures *) 
Theorem Disjoint_dom_rename_all_eq:
  forall sig,
    (forall e,
       Disjoint _ (Dom_map sig) (bound_var e) ->
       rename_all sig e = rename_all_ns sig e) /\
    (forall fds,
       Disjoint _ (Dom_map sig) (bound_var_fundefs fds) ->
           rename_all_fun sig fds = rename_all_fun_ns sig fds).        
Proof with (eauto with Ensembles_DB).
  intro sig.
  apply exp_def_mutual_ind; intros; repeat normalize_bound_var_in_ctx; simpl.
  - rewrite <- H.
    erewrite (proj1 prop_rename_all). 
    reflexivity.
    apply remove_none.
    eapply Disjoint_dom_map. apply H0. auto.
    eapply Disjoint_Included_r...
  - reflexivity.
  - rewrite H.
    assert ( Disjoint M.elt (Dom_map sig) (bound_var (Ecase v l)))...
    apply H0 in H2. simpl in H2.
    inv H2. reflexivity.
    eapply Disjoint_Included_r...
  - rewrite <- H.
    erewrite (proj1 prop_rename_all). 
    reflexivity.
    apply remove_none.
    eapply Disjoint_dom_map...
    eapply Disjoint_Included_r...
  - rewrite <- H0...
    rewrite <- H...
    erewrite (proj1 prop_rename_all).
    erewrite (proj2 prop_rename_all).
    reflexivity.
    apply Disjoint_dom_remove_all. rewrite <- same_name_in_fun. eapply Disjoint_Included_r.
    apply name_in_fundefs_bound_var_fundefs. auto...
    apply Disjoint_dom_remove_all. rewrite <- same_name_in_fun. eapply Disjoint_Included_r.
    apply name_in_fundefs_bound_var_fundefs. auto...
  - reflexivity.
  - rewrite <- H...
    erewrite (proj1 prop_rename_all).
    reflexivity.
    apply remove_none.
    eapply Disjoint_dom_map...
  - reflexivity.
  - rewrite <- H...
    rewrite <- H0...    
    erewrite (proj1 prop_rename_all).
    reflexivity.
    apply Disjoint_dom_remove_all...
  - reflexivity.
Qed.


Lemma occurs_free_ctx_not_bound:
  forall (x : var) (e : exp),
  occurs_free e x ->
  (forall c : exp_ctx, ~ bound_var_ctx c x ->  occurs_free (c |[ e ]|) x).
Proof.
  intros.
  destruct ((proj1 occurs_free_dec) (c |[ e ]|)).
  specialize (Dec x).
  inv Dec; auto.
  exfalso.
  apply H0.
  eapply occurs_free_app_bound_var; eauto.
Qed.  

Theorem occurs_free_fundefs_ctx_not_bound:
    forall (x : var) (e : exp),
      occurs_free e x ->
  (forall fds : fundefs_ctx,
   ~ bound_var_fundefs_ctx fds x -> occurs_free_fundefs (fds <[ e ]>) x).
Proof.
  intros.
  destruct ((proj2 occurs_free_dec) (fds <[ e ]>)).
  specialize (Dec x).
  inv Dec; auto.
  exfalso.
  apply H0.
  eapply occurs_free_app_bound_var; eauto.
Qed.  

Theorem Disjoint_bv_of_ctx:
  forall c e,
  unique_bindings (c |[ e]|) ->
  Disjoint _ (bound_var (c |[ e]|)) (occurs_free (c |[ e]|)) ->
  Disjoint _ (bound_var e) (occurs_free e).
Proof.
  intros.
  split. intro. intro.
  destruct H1.
  destruct (bound_var_ctx_dec c).
  specialize (Dec x).
  destruct Dec.
  apply ub_app_ctx_f in H; destructAll.
  inv H5. specialize (H6 x). auto.
  inv H0. specialize (H4 x).
  apply H4.
  split. apply bound_var_app_ctx; auto.
  apply occurs_free_ctx_not_bound; auto.
Qed.


Theorem num_occur_list_not_dom: forall f sigma,
                                    ~ (Dom_map sigma f) ->
                                    forall l,
     num_occur_list l f <= num_occur_list (apply_r_list sigma l) f.
Proof.
  induction l; auto.
  simpl.
  destruct (cps_util.var_dec f a).
  unfold apply_r.
  subst.
  destruct (M.get a sigma) eqn:gas.
  exfalso.
  apply H. exists e; auto.
  destruct (cps_util.var_dec a a). omega.
  exfalso; apply n. auto.
  destruct (cps_util.var_dec f (apply_r sigma a)); omega.
Qed.  

Theorem num_occur_list_not_range: forall f sigma,
                                    ~ (Range_map sigma f) ->
                                    forall l,
   num_occur_list (apply_r_list sigma l) f  <= num_occur_list l f.
Proof.
  induction l.
  - simpl. reflexivity.
  - simpl.
    destruct (cps_util.var_dec f a).
    + subst.
      destruct (cps_util.var_dec a (apply_r sigma a)); omega.
    + destruct (cps_util.var_dec f (apply_r sigma a)).
      * exfalso. apply H.
        exists a.
        unfold apply_r in e.
        destruct  (Maps.PTree.get a sigma).
        subst; auto.
        exfalso; apply n; auto.
      * omega.
Qed.

Local Hint Constructors num_occur num_occur_fds num_occur_case num_occur_ec num_occur_fdc.

(** If a variable is not in the range of a substitution, applying the 
substitution to a term cannot increase the occurence count for that variable. *)
  Theorem num_occur_rename_all_not_range_mut:
  forall f,
  ( forall e m n sigma,
      num_occur e f m ->
       num_occur (rename_all sigma e) f n  ->
       ~ Range_map sigma f ->
      n <= m) /\
  ( forall fds m n sigma,
      num_occur_fds fds f m ->
      num_occur_fds (rename_all_fun sigma fds) f n  ->
      ~ Range_map sigma f ->
      n <= m). 
Proof.
  intro f.
  apply exp_def_mutual_ind; intros.
  - simpl in H1. inv H1.
    inv H0. 
    specialize (H _ _ _  H8 H9).
    apply plus_le_compat.
    apply H. intro. apply H2.
    apply Range_map_remove in H0. auto.
    apply num_occur_list_not_range. auto.
  - simpl in H0. inv H0.
    inv H6. inv H.
    inv H5.
    apply plus_le_compat.
    assert (Hll := num_occur_list_not_range _ _ H1 ([v])).
simpl in Hll.    auto.
    auto.
  - simpl in H2. inv H1. inv H2. inv H8. inv H7.
    replace (num_occur_list [v] f + (n + m)) with
    (n + (num_occur_list [v] f + m)) by omega.
    unfold var.
    replace (num_occur_list [apply_r sigma v] f + (n0 + m0)) with  
    (n0 + (num_occur_list [apply_r sigma v] f + m0)) by omega.
    apply plus_le_compat.
    eapply H; eauto.
    eapply H0; eauto.
    simpl. constructor.
    auto.
    
  - simpl in H1. inv H1.
    inv H0.
    specialize (H _ _ _ H9 H10).
    apply plus_le_compat.
    assert (Hll := num_occur_list_not_range _ _ H2 ([v0])).
    simpl in Hll.    auto.
    apply H. intro; apply H2.
    apply Range_map_remove in H0.
    auto.
  - inv H1.
    simpl in H2. inv H2.
    apply plus_le_compat.
    eapply H0; eauto.
    intro; apply H3.
    apply Range_map_remove_all in H1.
    auto.
    eapply H; eauto.
    intro.
    apply H3.
    apply Range_map_remove_all in H1.
    auto.
  - inv H. inv H0.
    assert (Hll := num_occur_list_not_range _ _ H1 (v::l)).
    auto.    
  - inv H0; inv H1.
    apply plus_le_compat.
    eapply H; eauto.
    intro; apply H2.
    apply (@Range_map_remove var) in H0. auto.
    apply num_occur_list_not_range; auto.
  - inv H; inv H0.
    assert (Hll := num_occur_list_not_range _ _ H1 ([v])).
    auto.
  - inv H1; inv H2.
    apply plus_le_compat.
    eapply H; eauto.
    intro; apply H3.
    apply Range_map_remove_all in H1. auto.
    eapply H0; eauto.
  - inv H; inv H0. auto.
Qed.

  Theorem num_occur_rename_all_not_range:
  forall f,
  ( forall e m n sigma,
      num_occur e f m ->
       num_occur (rename_all sigma e) f n  ->
       ~ Range_map sigma f ->
      n <= m). 
  Proof.
    apply num_occur_rename_all_not_range_mut.
  Qed.


  
  Theorem num_occur_rename_all_ns_not_range_mut:
    forall f sigma,
      ~ Range_map sigma f ->
      ( forall e m n,
          num_occur e f m ->
          num_occur (rename_all_ns sigma e) f n  ->
          n <= m) /\
      ( forall fds m n,
          num_occur_fds fds f m ->
          num_occur_fds (rename_all_fun_ns sigma fds) f n  ->
          n <= m). 
  Proof.
    intros f sig Hs.
    apply exp_def_mutual_ind; simpl; intros.
    - inv H0; inv H1.
      specialize (H _ _ H8 H7).
      assert (Hnn := num_occur_list_not_range _ _ Hs l).
      omega.
    - inv H; inv H0.
      inv H5; inv H4.
      rewrite plus_0_r.
      rewrite plus_0_r.
      apply (num_occur_list_not_range _ _ Hs [v]).
    - inv H1. inv H2.
      inv H7. inv H6.
      specialize (H _ _ H8 H7).
      assert (  num_occur_list [apply_r sig v] f + m0 <=
                num_occur_list [v] f + m).
      eapply H0. constructor; auto. constructor; auto.
      simpl in *. omega.
    - inv H0; inv H1.
      specialize (H _ _ H9 H8).
      assert (Hnn := num_occur_list_not_range _ _ Hs [v0]).
      simpl in *. omega.
    - inv H1; inv H2.
      specialize (H _ _ H8 H9).
      specialize (H0 _ _ H5 H4).
      omega.
    - inv H; inv H0.
      apply (num_occur_list_not_range _ _ Hs (v::l)).
    - inv H0; inv H1.
      specialize (H _ _ H8 H7).
      assert (Hnn := num_occur_list_not_range _ _ Hs l).
      omega.
    - inv H; inv H0.
      apply (num_occur_list_not_range _ _ Hs [v]).
    - inv H1; inv H2.
      specialize (H _ _ H10 H9).
      specialize (H0 _ _ H11 H12).
      omega.
    - inv H; inv H0; auto.
  Qed.

  Theorem num_occur_rename_all_ns_not_range:
    forall f sigma,
      ( forall e m n,
          num_occur e f m ->
          num_occur (rename_all_ns sigma e) f n  ->
          ~ Range_map sigma f ->
          n <= m).
  Proof.
    intros. eapply (proj1 (num_occur_rename_all_ns_not_range_mut _ _ H1)); eauto.
  Qed.

  Theorem num_occur_rename_all_fun_ns_not_range:
     forall f sigma fds m n,
          num_occur_fds fds f m ->
          num_occur_fds (rename_all_fun_ns sigma fds) f n  ->
          ~ Range_map sigma f ->
          n <= m. 
  Proof.
    intros. eapply (proj2 (num_occur_rename_all_ns_not_range_mut _ _ H1)); eauto.
  Qed.

  
    Theorem num_occur_rename_all_not_dom_mut:
  forall f,
  ( forall e m n sigma,
      num_occur e f m ->
       num_occur (rename_all_ns sigma e) f n  ->
       ~ Dom_map sigma f ->
      m <= n) /\
  ( forall fds m n sigma,
      num_occur_fds fds f m ->
      num_occur_fds (rename_all_fun_ns sigma fds) f n  ->
      ~ Dom_map sigma f ->
      m <= n). 
Proof.
  intro f.
  apply exp_def_mutual_ind; intros.
  - simpl in H1. inv H1.
    inv H0. 
    specialize (H _ _ _  H8 H9).
    apply plus_le_compat.
    apply H. intro. apply H2.
    auto.
    apply num_occur_list_not_dom. auto.
  - simpl in H0. inv H0.
    inv H6. inv H.
    inv H5.
    apply plus_le_compat.
    apply (num_occur_list_not_dom _ _ H1 ([v])).
    auto.
  - simpl in H2. inv H1. inv H2. inv H8. inv H7.
    replace (num_occur_list [v] f + (n + m)) with
    (n + (num_occur_list [v] f + m)) by omega.
    unfold var.
    replace (num_occur_list [apply_r sigma v] f + (n0 + m0)) with  
    (n0 + (num_occur_list [apply_r sigma v] f + m0)) by omega.
    apply plus_le_compat.
    eapply H; eauto.
    eapply H0; eauto.
    simpl. constructor.
    auto.    
  - simpl in H1. inv H1.
    inv H0.
    specialize (H _ _ _ H9 H10).
    apply plus_le_compat.
    assert (Hll := num_occur_list_not_dom _ _ H2 ([v0])).
    simpl in Hll.    auto.
    apply H. intro; apply H2.
    auto.
  - inv H1.
    simpl in H2. inv H2.
    apply plus_le_compat.
    eapply H0; eauto.
    eapply H; eauto.
  - inv H. inv H0.
    assert (Hll := num_occur_list_not_dom _ _ H1 (v::l)).
    simpl in Hll.
    auto.
  - inv H0; inv H1.
    apply plus_le_compat.
    eapply H; eauto.
    apply num_occur_list_not_dom.
    auto.
  - inv H; inv H0.    
    assert (Hll := num_occur_list_not_dom _ _ H1 ([v])).
    auto.
  - inv H1; inv H2.
    apply plus_le_compat.
    eapply H; eauto.

    eapply H0; eauto.
  - inv H; inv H0. auto.
Qed.


  
  
Theorem apply_r_set1:
  forall x y sig,
    apply_r (M.set x y sig) x = y.
Proof.
  intros.
  unfold apply_r.
  rewrite M.gss. auto.
Qed.

Theorem num_occur_list_set:
  forall f y x sigma,
    f <> y ->
    forall l,
  num_occur_list (apply_r_list (M.set x y sigma) l) f  <=
   num_occur_list (apply_r_list sigma l) f. 
Proof.
  induction l; intros; simpl; auto.
  destruct (var_dec x a).
  - subst.
    rewrite apply_r_set1.
    destruct (cps_util.var_dec f y).
    exfalso; auto.
    destruct (cps_util.var_dec f (apply_r sigma a)); omega.
  - rewrite apply_r_set2  by auto.
    destruct (cps_util.var_dec f (apply_r sigma a)); omega.
Qed.
    
Theorem num_occur_rename_all_ns_set:
  forall f x y,
    f <> y -> 
  ( forall e m n sigma,
      num_occur (rename_all_ns sigma e) f m ->
      num_occur (rename_all_ns (M.set x y sigma) e) f n  ->
      n <= m) /\
  ( forall fds m n sigma,
      num_occur_fds (rename_all_fun_ns sigma fds) f m ->
      num_occur_fds (rename_all_fun_ns (M.set x y sigma) fds) f n  -> 
      n <= m). 
Proof.
  intros f x y Hfy; apply exp_def_mutual_ind; intros; simpl in *; try (inv H0; inv H1).
  - assert (Hl := num_occur_list_set _ _ x sigma Hfy l).
    specialize (H _ _ _ H8 H7).
    apply plus_le_compat; eauto.
  - inv H; inv H0.
    inv H5; inv H4.
    assert (Hl := num_occur_list_set).
    specialize (Hl _ _ x sigma Hfy [v]).    
    simpl in Hl.
    simpl.
    do 2 (rewrite plus_0_r).
    auto.
  - inv H1; inv H2.    
    inv H7; inv H6.
    rewrite OrdersEx.Nat_as_OT.add_shuffle3.
    rewrite  OrdersEx.Nat_as_OT.add_shuffle3 with (p := m).
    apply plus_le_compat; eauto.    
  - assert (Hl := num_occur_list_set).
    specialize (Hl _ _ x sigma Hfy [v0]).    
    specialize (H _ _ _ H9 H8).
    simpl; simpl in Hl.
    apply plus_le_compat; eauto.
  - inv H1; inv H2.
    apply plus_le_compat; eauto.
  - inv H; inv H0.
    assert (Hl := num_occur_list_set).
    specialize (Hl _ _ x sigma Hfy (v::l)).    
    auto. 
  - assert (Hl := num_occur_list_set _ _ x sigma Hfy l).
    apply plus_le_compat; eauto.
  - inv H; inv H0.
    assert (Hl := num_occur_list_set _ _ x sigma Hfy [v]).
    auto.
  - inv H1; inv H2.
    apply plus_le_compat; eauto.
  - inv H; inv H0; auto.
Qed.



Theorem num_occur_list_set_not_x:
  forall f y x sigma,
    ~ Dom_map sigma x ->
    f <> x ->
    forall l,
      num_occur_list (apply_r_list sigma l) f  <=
    num_occur_list (apply_r_list (M.set x y sigma) l) f.
Proof.
  induction l; intros; simpl; auto.
  destruct (var_dec x a).
  - subst.
    rewrite apply_r_set1.
    destruct (cps_util.var_dec f y). subst.
    destruct (cps_util.var_dec y (apply_r sigma a)); omega.
    destruct (cps_util.var_dec f (apply_r sigma a)).
    exfalso. unfold apply_r  in e. 
    destruct (Maps.PTree.get a sigma) eqn:gas.
    apply H. exists e0; auto.
    auto.
    auto.
  -     rewrite apply_r_set2; auto.
     destruct (cps_util.var_dec f (apply_r sigma a)); omega.    
Qed.
    
    

Theorem num_occur_rename_all_ns_set_not_x:
  forall f x y sigma,
    ~ Dom_map sigma x ->
    f <> x -> 
  ( forall e m n,
      num_occur (rename_all_ns sigma e) f m ->
      num_occur (rename_all_ns (M.set x y sigma) e) f n  ->
      m <= n) /\
  ( forall fds m n,
      num_occur_fds (rename_all_fun_ns sigma fds) f m ->
      num_occur_fds (rename_all_fun_ns (M.set x y sigma) fds) f n  -> 
      m <= n). 
Proof.
  intros f x y sigma Hdom Hfy; apply exp_def_mutual_ind; intros; simpl in *; try (inv H0; inv H1).
  - assert (Hl := num_occur_list_set_not_x f y x _ Hdom Hfy l).    
    specialize (H _ _ H8 H7).
    apply plus_le_compat; eauto.
  - inv H; inv H0.
    inv H5; inv H4.
    assert (Hl := num_occur_list_set_not_x).
    specialize (Hl f y x _ Hdom Hfy [v]).
    simpl in Hl.
    simpl.
    do 2 (rewrite plus_0_r).
    auto.
  - inv H1; inv H2.    
    inv H7; inv H6.
    rewrite OrdersEx.Nat_as_OT.add_shuffle3.
    rewrite  OrdersEx.Nat_as_OT.add_shuffle3 with (p := m0).
    apply plus_le_compat; eauto.
  -     assert (Hl := num_occur_list_set_not_x).
    specialize (Hl f y x _ Hdom Hfy [v0]).    
    specialize (H _ _ H9 H8).
    simpl; simpl in Hl.
    apply plus_le_compat; eauto.
  - inv H1; inv H2.
    apply plus_le_compat; eauto.
  - inv H; inv H0.
    assert (Hl := num_occur_list_set_not_x).
    specialize (Hl f y x _ Hdom Hfy (v::l)).    
    auto. 
  -  assert (Hl := num_occur_list_set_not_x f y x _ Hdom Hfy l). 
    apply plus_le_compat; eauto.
  - inv H; inv H0.
     assert (Hl := num_occur_list_set_not_x f y x _ Hdom Hfy [v]).    
    auto.
  - inv H1; inv H2.
    apply plus_le_compat; eauto.
  - inv H; inv H0; auto.
Qed.

Theorem num_occur_rename_all_ns_set_unchanged:
  forall f x y sigma e m n,
    ~ Dom_map sigma x ->
    f <> x ->
    f <> y ->
    num_occur (rename_all_ns sigma e) f m ->
    num_occur (rename_all_ns (M.set x y sigma) e) f n  ->
    m = n.
Proof.
  intros.
  assert (n <= m). eapply (proj1 (num_occur_rename_all_ns_set _ _ _ H1)); eauto.
  assert (m <= n). eapply (proj1 (num_occur_rename_all_ns_set_not_x _ _ _ _ H H0)); eauto.
  omega.  
Qed.

Theorem not_occur_rename_not_dom:
  forall sig v e,
  ~ Dom_map sig v ->
  num_occur (rename_all_ns sig e) v 0 ->
  num_occur e v 0.
Proof.
  intros.
  assert (exists n, num_occur e v n) by apply e_num_occur.
  inv H1.
  assert (Hn0 := proj1 (num_occur_rename_all_not_dom_mut v) _ _ _ _ H2 H0 H).
  apply le_n_0_eq in Hn0. subst; auto.
Qed.

Definition rename_all_case sigma cl := (List.map (fun (p:var*exp) => let (k, e) := p in
                                                                     (k, rename_all_ns sigma e)) cl).


Theorem num_occur_case_rename_all_ns_not_dom:
  forall f,
  forall cl sig n m,
    num_occur_case cl f n ->
    num_occur_case (rename_all_case sig cl) f m ->
    ~ Dom_map sig f ->
    n <= m.
Proof.
  induction cl; intros.
  - inv H; inv H0; auto.
  - inv H; inv H0.
    apply plus_le_compat.
    eapply (proj1 (num_occur_rename_all_not_dom_mut _)); eauto. 
    eauto.
Qed.



Theorem num_occur_sig_unaffected:
  forall x sig n m e,
    ~ Dom_map sig x ->
    ~ Range_map sig x ->
    num_occur e x n ->
    num_occur (rename_all_ns sig e) x m ->
    n = m.
Proof.
  intros.
  assert (n <= m).
  eapply (proj1 (num_occur_rename_all_not_dom_mut _)); eauto.
  assert (m <= n).
  eapply (proj1 (num_occur_rename_all_ns_not_range_mut _ _ H0)); eauto.
  omega.
Qed.

Theorem num_occur_set_arl:
  forall x y,
    x <> y ->
    forall l,
  num_occur_list (apply_r_list (M.set x y (M.empty var)) l) y =
  num_occur_list l y + num_occur_list l x.
Proof.
  intros x y Hxy. induction l.
  auto.
  simpl. destruct (cps_util.var_dec x a).
  - subst. rewrite apply_r_set1.
    destruct (cps_util.var_dec y a).
    exfalso; auto.
    destruct (cps_util.var_dec y y). 2: exfalso; auto.
    omega.
  - rewrite apply_r_set2 by auto.
    rewrite apply_r_empty.
    destruct (cps_util.var_dec y a); omega.
Qed.  

Theorem num_occur_arl_kill:
  forall x sig,
  ~ Range_map sig x ->
    Dom_map sig x ->
    forall l,
      num_occur_list (apply_r_list sig l) x = 0.
Proof.
  induction l.
  auto.
  simpl. destruct (cps_util.var_dec x (apply_r sig a)).
  - exfalso. unfold apply_r in e.
    destruct (Maps.PTree.get a sig) eqn:gas.
    subst.
    apply H. exists a; auto.
    subst.
    inv H0. rewrite H1 in gas. inv gas.
  - auto.
Qed.

Theorem num_occur_rename_all_ns_kill:
  forall x sig,
    ~ Range_map sig x ->
    Dom_map sig x ->
  (forall e,
     num_occur (rename_all_ns sig e) x 0 )/\
  (forall fds,
     num_occur_fds (rename_all_fun_ns sig fds) x 0).
Proof.
  intros x sig Hrx Hdx.
  apply exp_def_mutual_ind; intros; simpl in *.
  - eapply num_occur_n. constructor. eauto.
    rewrite num_occur_arl_kill; auto.
  - eapply num_occur_n. constructor. constructor.
    assert (Hn := num_occur_arl_kill _ _ Hrx Hdx [v]).
    simpl in Hn. simpl. omega.
  - eapply num_occur_n. constructor. constructor. eauto.
    inv H0; pi0; eauto. simpl.
    inv H0; pi0.  auto.
  - eapply num_occur_n. constructor; eauto.
    assert (Hn := num_occur_arl_kill _ _ Hrx Hdx [v0]).
    simpl in *; omega.
  - eapply num_occur_n. constructor; eauto.
    auto.
  - eapply num_occur_n. constructor; eauto.
    assert (Hn := num_occur_arl_kill _ _ Hrx Hdx (v::l)).
    simpl in *. omega.
  - eapply num_occur_n. constructor; eauto.
    rewrite num_occur_arl_kill; auto.
  - eapply num_occur_n. constructor; auto.
    assert (Hn := num_occur_arl_kill _ _ Hrx Hdx [v]).
    simpl in *; omega.
  - eapply num_occur_fds_n.  constructor; eauto.
    auto.
  - constructor.
Qed.
    
Theorem num_occur_rename_mut:
  forall x y,
  x <> y ->
  (forall e n m,
     num_occur e x n ->
     num_occur e y m ->
     num_occur (rename_all_ns (M.set x y (M.empty var)) e) x 0 /\
     num_occur (rename_all_ns (M.set x y (M.empty var)) e) y (n+m)) /\
  (forall fds n m,
     num_occur_fds fds x n ->
     num_occur_fds fds y m ->
     num_occur_fds (rename_all_fun_ns (M.set x y (M.empty var)) fds) x 0 /\
     num_occur_fds (rename_all_fun_ns (M.set x y (M.empty var)) fds) y (n+m)).
Proof.
  intros x y Hxy.
  apply exp_def_mutual_ind; intros; simpl in *; try (inv H0; inv H1).
  - specialize (H _ _ H8 H7).
    destruct H. split.
    eapply num_occur_n.
    constructor. eauto.
    rewrite num_occur_arl; auto.
    eapply num_occur_n.
    constructor; eauto.
    rewrite num_occur_set_arl; auto. omega.
  - inv H; inv H0.
    inv H5; inv H4.
    split.
    eapply num_occur_n. constructor; eauto.
    assert (Hn := num_occur_arl _ _ [v] Hxy).
    simpl in Hn. simpl.  rewrite plus_0_r. auto. 
    eapply num_occur_n. constructor. auto.
    assert (Hnn := num_occur_set_arl _ _ Hxy [v]).
    simpl. simpl in Hnn. do 3 (rewrite plus_0_r). rewrite plus_comm. auto.
  - inv H1; inv H2. inv H7; inv H6.
    specialize (H _ _ H8 H7).
    assert (num_occur (Ecase v l) x ( num_occur_list [v] x + m)).
    constructor; auto.
    assert (num_occur (Ecase v l) y ( num_occur_list [v] y + m0)).
    constructor; auto.
    specialize (H0 _ _ H1 H2).
    destruct H. destruct H0.
    inv H0; inv H4. 
    split.
    + eapply num_occur_n.
      constructor. constructor; eauto.
      simpl. auto.
    + eapply num_occur_n.
      constructor. constructor; eauto.
      simpl. omega.      
  - specialize (H _ _ H9 H8).
    destruct H.
    split.
    eapply num_occur_n. constructor; eauto. 
    assert (Hn := num_occur_arl _ _ [v0] Hxy).
    simpl in Hn. simpl. rewrite plus_0_r. auto.
    eapply num_occur_n. constructor; eauto.
    assert (Hnn := num_occur_set_arl _ _ Hxy [v0]).
    simpl. simpl in Hnn. unfold var in *. unfold M.elt in *. rewrite Hnn. omega.
  - inv H1; inv H2.
    specialize (H _ _ H8 H9).
    specialize (H0 _ _ H5 H4).
    destructAll. split; eapply num_occur_n; eauto.
    omega.
  - inv H; inv H0. split; eapply num_occur_n; eauto.    
    assert (Hn := num_occur_arl _ _ (v::l) Hxy).
    simpl in Hn. simpl.
    unfold var in *. unfold M.elt in *. omega.
    assert (Hnn := num_occur_set_arl _ _ Hxy (v::l)).
    simpl. simpl in Hnn. unfold var in *. unfold M.elt in *. omega.
  - specialize (H _ _ H8 H7).
    destruct H.
    split; eapply num_occur_n; eauto.
    rewrite num_occur_arl; auto.
    rewrite num_occur_set_arl; auto. omega.
  - inv H; inv H0.
    split; eapply num_occur_n; eauto.
    assert (Hn := num_occur_arl _ _ [v] Hxy).
    simpl in Hn. simpl. unfold var in *.
    unfold M.elt in *. 
    omega.
    assert (Hnn := num_occur_set_arl _ _ Hxy [v]).
    simpl. simpl in Hnn. unfold var in *.  unfold M.elt in *. omega.
  - inv H1; inv H2. specialize (H _ _ H10 H9).
    specialize (H0 _ _ H11 H12).
    destruct H; destruct H0.
    split.
    eapply num_occur_fds_n. constructor; eauto.  auto.
    eapply num_occur_fds_n. constructor; eauto.  omega.
  - inv H; inv H0. split; auto.
Qed.    
    
    Theorem num_occur_rename_all_ctx_not_dom_mut:
  forall f,
  ( forall c m n sigma,
      num_occur_ec c f m ->
       num_occur_ec (rename_all_ctx_ns sigma c) f n  ->
       ~ Dom_map sigma f ->
      m <= n) /\
  ( forall fds m n sigma,
      num_occur_fdc fds f m ->
      num_occur_fdc (rename_all_fun_ctx_ns sigma fds) f n  ->
      ~ Dom_map sigma f ->
      m <= n). 
Proof.
  intro f.
  exp_fundefs_ctx_induction IHc IHfc; intros.
  - inv H0. inv H; auto.
  - simpl in H0. inv H0.
    inv H.  
    specialize (IHc _ _ _  H7 H8).
    apply plus_le_compat.
    apply num_occur_list_not_dom. auto.
    apply IHc. auto.
  - simpl in H0. inv H0.
    inv H. 
    apply plus_le_compat.
    apply (num_occur_list_not_dom _ _ H1 ([v0])).
    eauto.
  - simpl in H0. inv H0. inv H.
    apply plus_le_compat.
    apply num_occur_list_not_dom; auto.
    eauto.
  - simpl in H0. inv H0.
    inv H.
    repeat apply plus_le_compat.
    apply (num_occur_list_not_dom _ _ H1 ([v])).
    2: eauto.
    eapply num_occur_case_rename_all_ns_not_dom; eauto.
    eapply num_occur_case_rename_all_ns_not_dom; eauto.
  - inv H.
    simpl in H0. inv H0.
    apply plus_le_compat; eauto.
    eapply (proj2 (num_occur_rename_all_not_dom_mut _)); eauto. 
  - inv H. inv H0.
    apply plus_le_compat; eauto.
    eapply (proj1 (num_occur_rename_all_not_dom_mut _)); eauto.
  - inv H.
    simpl in H0. inv H0.
    apply plus_le_compat; eauto.
    eapply (proj2 (num_occur_rename_all_not_dom_mut _)); eauto. 
  - inv H. inv H0.
    apply plus_le_compat; eauto.
    eapply (proj1 (num_occur_rename_all_not_dom_mut _)); eauto. 
Qed.

(* move to cps_util *)
Theorem e_num_occur_ec:
  forall c v, exists n, num_occur_ec c v n.
Proof.
  intros.
  assert (exists n, num_occur (c |[ Ehalt v ]|) v n) by apply e_num_occur.
  destruct H.
  apply num_occur_app_ctx in H. destructAll.
  eauto.
Qed.

  
Theorem not_occur_rename_ctx_not_dom:
  forall sig v c,
  ~ Dom_map sig v ->
  num_occur_ec (rename_all_ctx_ns sig c) v 0 ->
  num_occur_ec c v 0.
Proof.
  intros.
  assert (exists n, num_occur_ec c v n) by apply e_num_occur_ec.
  inv H1.
  assert (Hn0 := proj1 (num_occur_rename_all_ctx_not_dom_mut v) _ _ _ _ H2 H0 H).
  apply le_n_0_eq in Hn0. subst; auto.
Qed.


  Theorem not_occur_list: forall v l,
  num_occur_list l v = 0 <->
  ~ FromList l v.
  Proof.
    induction l; split; intro.
    - intro.
      inv H0.
    - constructor.
    - intro.
      simpl in H.
      inv H0.
      destruct (cps_util.var_dec v v). inv H. apply n; auto.
      destruct (cps_util.var_dec v a). inv H. apply IHl in H.
      auto.
    - simpl.
      destruct (cps_util.var_dec v a).
      exfalso; apply H.
      constructor. auto.
      apply IHl.
      intro; apply H.
      constructor 2. auto.
  Qed.

Theorem of_fun_inline:
  forall xs vs fb t c f B1 B2 c',
    unique_bindings (c' |[ Efun (fundefs_append B1 (Fcons f t xs fb B2)) (c |[ Eapp f t vs ]|) ]|) ->
     num_occur
         (Efun (fundefs_append B1 (Fcons f t xs fb B2))
               (c |[ Eapp f t vs ]|)) f 1 ->
    length xs = length vs ->
    Included _ (occurs_free (c' |[Efun (fundefs_append B1 B2) (c |[ (rename_all_ns (set_list (combine xs vs) (M.empty var)) fb)]|) ]|))
             (occurs_free (c' |[ Efun (fundefs_append B1 (Fcons f t xs fb B2)) (c |[ Eapp f t vs ]|) ]|)).
Proof.
  intros xs vs fb t c f B1 B2 c' H Hnoc H0.
  eapply Included_trans.
  Focus 2.
  apply occurs_free_exp_ctx_included.
  apply of_fun_inline''' with (f := f) (fds := (fundefs_append B1 (Fcons f t xs fb B2))).
  2: apply H0.
  erewrite find_def_fundefs_append_r.
  simpl. destruct (M.elt_eq f f).
  reflexivity.
  exfalso. apply n. auto.
  simpl. destruct (M.elt_eq f f).
  reflexivity.
  exfalso. apply n. auto.
  apply ub_app_ctx_f in H.
  destructAll.
  inv H1.
  apply name_not_in_fundefs_find_def_None.
  eapply fundefs_append_unique_bindings_l in H6.
  2: reflexivity.
  destructAll.
  rewrite bound_var_fundefs_Fcons in H4.
  intro.
  apply name_in_fundefs_bound_var_fundefs in H6.
  inv H4.
  specialize (H8 f).
  apply H8.
  split; eauto.
  apply of_fun_rm.
  apply ub_app_ctx_f in H.
  destructAll.
  inv H1. auto.
  {
    inv Hnoc.
    apply num_occur_app_ctx in H5.
    destructAll.
    inv H2. simpl in H3.
    destruct (cps_util.var_dec f f).       
    2: (exfalso; apply n; auto).
    assert (x = 0 /\ num_occur_list vs f = 0 /\ m = 0).
    omega.
    clear H3.
    apply fundefs_append_num_occur' in H6.
    destructAll.
    pi0.
    inv H6; pi0.
    constructor.
    apply num_occur_app_ctx.
    exists 0, 0.
    split; auto.
    split; auto.
    assert (exists n, num_occur (rename_all_ns (set_list (combine xs vs) (M.empty var)) fb) f n) by apply e_num_occur.
    destruct H2.
    assert (x <= 0).
    eapply num_occur_rename_all_ns_not_range; eauto.
    intro.
    apply Range_map_setlist in H4.
    apply not_occur_list in H3. auto.
    apply le_n_0_eq in H4.
    subst. auto.
    rewrite <- plus_0_l.
    eapply fundefs_append_num_occur.
    reflexivity.
    auto.
    rewrite <- plus_0_l.
    constructor; auto.
  }
Qed.


Theorem sr_rw_in_rw: forall e e',
  unique_bindings e ->
  Disjoint _ (bound_var e) (occurs_free e) ->
  gen_sr_rw e e' ->
  gr_clos e e'.
Proof.
  intros;
  inv H1;
  inv H2;
  try (solve [constructor; constructor; constructor; try (apply (not_occurs_not_free)); auto]).
  -  constructor. constructor.     
     constructor.
     eapply Forall_impl. 2: apply H1.
     intros.
     apply not_occurs_not_free. auto.
  - do 2 (constructor).
    apply Fun_rem; auto.
    apply ub_app_ctx_f in H.
    destructAll.
    inv H2. apply unique_bind_has_unique_name.  auto. 
  -  constructor.
     constructor.
     constructor; auto.
    apply ub_app_ctx_f in H.
    destructAll.
    inv H2.
    intro.
    apply H6.
    apply bound_var_app_ctx.
    left.
    apply bound_stem_var. auto.
  - constructor.
    constructor.
    assert (H' := H).
    apply ub_app_ctx_f in H. destructAll.
    inv H2.
    apply ub_app_ctx_f in H9. destructAll.
    rewrite <- (proj1 (Disjoint_dom_rename_all_eq _)).
    Focus 2. inv H4.  rewrite Dom_map_set. rewrite Dom_map_empty.
    eauto with Ensembles_DB.
    constructor; auto.
    + intro; apply H6.
      apply bound_var_app_ctx. left. apply bound_stem_var; auto.
    + intro.
      destruct (bound_var_ctx_dec c).
      specialize (Dec k). inv Dec.
      * inv H3. specialize (H9 k).
        apply H9.
        split; auto.
        rewrite bound_var_Econstr. rewrite bound_var_app_ctx.
        left. left. apply bound_stem_var.
        auto.
      * inv H0. specialize (H9 k).
        apply H9.
        split.
        rewrite bound_var_app_ctx.
        rewrite bound_var_Econstr.
        rewrite bound_var_app_ctx. right. left. left.
        apply bound_stem_var. auto.
        apply occurs_free_ctx_not_bound; auto.
        apply nthN_FromList in H1. auto.
    + destruct (bound_var_ctx_dec c).
      specialize (Dec k). inv Dec.
      * intro.
        inv H3.
        specialize (H9 k).
        apply H9.
        split; auto.
        rewrite bound_var_Econstr. rewrite bound_var_app_ctx.
        rewrite bound_var_Eproj. auto.
      * intro. inv H0.
        specialize (H9 k).
        apply H9. split.
        rewrite bound_var_app_ctx.
        rewrite bound_var_Econstr. rewrite bound_var_app_ctx.
        rewrite bound_var_Eproj.  auto.
        apply occurs_free_ctx_not_bound; auto.
        apply nthN_FromList in H1. auto.
    + intro; subst.
      (* either k is in the bv of c and H2 is false, 
            or k isn't and k is in of (since it appears in ys re:H1) *)
      destruct (bound_var_ctx_dec c).
      specialize (Dec k). inv Dec.
      * inv H3.
        specialize (H8 k).
        apply H8.
        split; auto.
      * inv H0. 
        specialize (H8 k).
        apply H8. split; auto.        
        rewrite bound_var_app_ctx.
        rewrite bound_var_Econstr. auto.
        apply occurs_free_ctx_not_bound; auto.
        apply nthN_FromList in H1. auto.
    + intro; subst.
      (* either k is in the bv of c and H2 is false, 
            or k isn't and k is in of (since it appears in ys re:H1) *)
      destruct (bound_var_ctx_dec c).
      specialize (Dec k). inv Dec.
      * inv H3.
        specialize (H8 k).
        apply H8.
        split; auto.
        rewrite bound_var_Econstr. rewrite bound_var_app_ctx.
        auto.
      * inv H0. 
        specialize (H8 k).
        apply H8. split; auto.        
        rewrite bound_var_app_ctx.
        rewrite bound_var_Econstr.
        rewrite bound_var_app_ctx.
        auto.
        apply occurs_free_ctx_not_bound; auto.
        apply nthN_FromList in H1. auto.      
  - (* fun inline *)
    eapply rt_trans.
    + constructor.    
      constructor.
      apply Fun_inline.
      * erewrite find_def_fundefs_append_r. simpl.
        destruct (M.elt_eq f f). reflexivity. exfalso; auto.
        simpl.         destruct (M.elt_eq f f). reflexivity. exfalso; auto.
        apply name_not_in_fundefs_find_def_None.
        intro.
        apply ub_app_ctx_f in H. destructAll. inv H4.
        eapply fundefs_append_unique_bindings_l in H9.
        2: reflexivity.
        destructAll.
        inv H7.
        specialize (H9 f).
        apply H9. split.
        apply name_in_fundefs_bound_var_fundefs. auto.
        constructor. left. auto.
      * apply ub_app_ctx_f in H. destructAll.
        inv H2.
        split. intro. intro.
        inv H2. 
        assert (Hof := Decidable_occurs_free (c0 |[ Eapp f t vs ]|)).
        inv Hof. specialize (Dec x). 
        destruct Dec.
        {
          assert (Hnf:= Decidable_name_in_fundefs  (fundefs_append B1 (Fcons f t xs fb B2))).
          inv Hnf. specialize (Dec x).
          inv Dec.
          eapply fundefs_append_unique_bindings_l in H8. 2: reflexivity.
          destructAll.
          eapply fundefs_append_name_in_fundefs in H10. 2: reflexivity.
          inv H10. inv H12. specialize (H10 x).
          apply H10. split.
          apply name_in_fundefs_bound_var_fundefs.
          auto.
          apply bound_var_fundefs_Fcons. inv H5; auto.
          inv H11.  inv H13. 
          inv H10.
          inv H5; auto.
          apply name_in_fundefs_bound_var_fundefs in H10.
          inv H5; auto. inv H21. specialize (H5 x). apply H5; auto.
          inv H22. specialize (H5 x). apply H5; auto.
          assert (occurs_free (Efun (fundefs_append B1 (Fcons f t xs fb B2)) (c0 |[ Eapp f t vs ]|)) x).
          apply Free_Efun1; auto.          
          assert (Hc := bound_var_ctx_dec c). inv Hc.
          specialize (Dec x). inv Dec.
          inv H4. specialize (H13 x).
          apply H13. split. auto.
          constructor. 
          eapply fundefs_append_bound_vars. reflexivity.
          right.
          apply bound_var_fundefs_Fcons.
          inv H5; auto.
          assert ((occurs_free (c |[ Efun (fundefs_append B1 (Fcons f t xs fb B2)) (c0 |[ Eapp f t vs ]|) ]|) x)).          
          apply occurs_free_ctx_not_bound; auto.
          inv H0. specialize (H14 x).
          apply H14. split; auto.
          apply bound_var_app_ctx. right.
          rewrite bound_var_Efun.
          left.
          eapply fundefs_append_bound_vars. reflexivity.
          right. apply bound_var_fundefs_Fcons.
          inv H5; auto.
        }
        { assert (bound_var_ctx c0 x).         
          eapply occurs_free_app_bound_var.
          2: apply H2. constructor. auto.          
          inv H9. specialize (H11 x).
          apply H11. split.
          rewrite bound_var_app_ctx. left; auto.
          eapply fundefs_append_bound_vars.
          reflexivity. right.
          rewrite bound_var_fundefs_Fcons.
          inv H5; eauto.
        }
      * apply unique_bind_has_unique_name.
        apply ub_app_ctx_f in H. destructAll.
        inv H2.
        auto.
      * split; intro. intro. inv H2. 
        assert (Hc := bound_var_ctx_dec c).        
        inv Hc. specialize (Dec x).
        apply ub_app_ctx_f in H. destructAll.
        inv Dec.
        inv H6. specialize (H8 x). apply H8. split; auto.
        apply bound_var_Efun.
        right. apply bound_var_app_ctx. left.
        apply bound_stem_var; auto.
        assert (occurs_free ( Efun (fundefs_append B1 (Fcons f t xs fb B2)) (c0 |[ Eapp f t vs ]|)) x).
        apply Free_Efun2. auto.
        assert (occurs_free (c |[ Efun (fundefs_append B1 (Fcons f t xs fb B2)) (c0 |[ Eapp f t vs ]|) ]|) x).
        apply occurs_free_ctx_not_bound; auto.
        inv H0. specialize (H10 x). apply H10. split; auto.
        apply bound_var_app_ctx. right. apply bound_var_Efun.
        right. apply bound_var_app_ctx. left. apply bound_stem_var; auto.
      * apply ub_app_ctx_f in H. destructAll.
        inv H2.
        eapply Disjoint_Included_r.
        apply name_in_fundefs_bound_var_fundefs.        
        eapply Disjoint_Included_l.
        2: apply H9.
        etransitivity.
        apply bound_stem_var.
        rewrite bound_var_app_ctx.
        apply Included_Union_l.        
      * apply ub_app_ctx_f in H. destructAll.
        inv H2.
        eapply fundefs_append_unique_bindings_l in H8. 2: reflexivity.
        destructAll.
        inv H5; auto.
    + constructor.
      constructor.
      rewrite <- (proj1 (Disjoint_dom_rename_all_eq _)).
      Focus 2. rewrite Dom_map_set_list; auto. rewrite Dom_map_empty.
      apply ub_app_ctx_f in H. destructAll. inv H2.
      eapply fundefs_append_unique_bindings_l in H8. 2: reflexivity. destructAll. inv H5.
      rewrite Union_Empty_set_neut_r.
      split. intro. intro.  inv H5. inv H16. specialize (H5 x). apply H5; auto.
      apply Fun_rem.
      * apply ub_app_ctx_f in H. destructAll.
        inv H2.
        apply unique_bind_has_unique_name.
        auto.
      * inv H3. 
        apply num_occur_app_ctx in H7. destructAll.
        inv H3.
        simpl in H5.
        destruct (cps_util.var_dec f f); [       | exfalso; apply n; auto].
        replace (x + S (num_occur_list vs f) + m)  with  (S (x + (num_occur_list vs f) + m)) in H5 by omega.
        inv H5.
        rewrite H4.
        pi0.
        assert (H8' := H8).
        apply fundefs_append_num_occur' in H8. destructAll.
        pi0.
        inv H5; pi0.
        constructor; auto.
        apply num_occur_app_ctx. exists 0; exists 0.
        split; auto.
        split; auto.
        assert (exists n, num_occur (rename_all (set_list (combine xs vs) (M.empty var)) fb) f n).
        apply e_num_occur. 
        destruct H5.
        assert (x <= 0).
        eapply num_occur_rename_all_not_range; eauto.
        intro.
        apply Range_map_setlist in H6.
        revert H6.
        apply not_occur_list. auto.
        apply le_n_0_eq in H6; subst; auto.                 
Qed.

Theorem bound_var_rename_all_exp:
  forall e sigma,
  Same_set _ (bound_var e) (bound_var (rename_all sigma e)).
Proof.
  intro. intro. split.
  intro. intro. apply bound_var_rename_all. auto.
  intro. intro. eapply bound_var_rename_all. eauto.
Qed.
  
Theorem rw_preserves: forall e e',
  unique_bindings e ->
  Disjoint _ (bound_var e) (occurs_free e) ->
  gsr_clos e e' ->
  unique_bindings e' /\
  Disjoint _ (bound_var e') (occurs_free e').
Proof.
  intros e e' Hub Hdj H.
  induction H.
  - inv H. inv H0.
    + split.
      apply ub_app_ctx_f in Hub.
      apply ub_app_ctx_f. destructAll.
      inv H1.
      split; auto.
      split; auto.
      rewrite bound_var_Econstr in H2.
      eauto with Ensembles_DB.
      rewrite bound_var_app_ctx in Hdj.
      rewrite bound_var_Econstr in Hdj.
      rewrite bound_var_app_ctx.
      eapply Disjoint_Included_r.
      apply of_constr_dead. apply H.
      eapply Disjoint_Included_l; eauto.
      auto with Ensembles_DB.
    + split.
      apply ub_app_ctx_f in Hub.
      apply ub_app_ctx_f. destructAll.
      inv H1.
      split; auto.
      split; auto.
      rewrite bound_var_Eprim in H2.
      eauto with Ensembles_DB.
      rewrite bound_var_app_ctx in Hdj.
      rewrite bound_var_Eprim in Hdj.
      rewrite bound_var_app_ctx.
      eapply Disjoint_Included_r.
      apply of_prim_dead. apply H.
      eapply Disjoint_Included_l; eauto.
      auto with Ensembles_DB.
    + split.
      apply ub_app_ctx_f in Hub.
      apply ub_app_ctx_f. destructAll.
      inv H1.
      split; auto.
      split; auto.
      rewrite bound_var_Eproj in H2.
      eauto with Ensembles_DB.
      rewrite bound_var_app_ctx in Hdj.
      rewrite bound_var_Eproj in Hdj.
      rewrite bound_var_app_ctx.
      eapply Disjoint_Included_r.
      apply of_proj_dead. apply H.
      eapply Disjoint_Included_l; eauto.
      auto with Ensembles_DB.
    + split.
      apply ub_app_ctx_f in Hub.
      apply ub_app_ctx_f. destructAll.
      inv H1.
      split; auto.
      split; auto.
      rewrite bound_var_Efun in H2.
      eauto with Ensembles_DB.
      rewrite bound_var_app_ctx in Hdj.
      rewrite bound_var_Efun in Hdj.
      rewrite bound_var_app_ctx.
      eapply Disjoint_Included_r.
      apply of_fun_dead. apply H.
      eapply Disjoint_Included_l; eauto.
      auto with Ensembles_DB.
    + apply ub_app_ctx_f in Hub.
      destructAll.
      inv H1.
      rewrite bound_var_Efun in H2.
      rewrite fundefs_append_bound_vars in H2. 2: reflexivity.
      rewrite bound_var_fundefs_Fcons in H2.
      rewrite fundefs_append_bound_vars in H7. 2: reflexivity.
      rewrite bound_var_fundefs_Fcons in H7. 
      split.
      apply ub_app_ctx_f.
      split; auto.
      split.
      constructor; auto.
      {
        eapply fundefs_append_unique_bindings_l in H6.
        2: reflexivity.
        destructAll.
        inv H3.
        eapply fundefs_append_unique_bindings_r; auto.
        rewrite bound_var_fundefs_Fcons in H4.
        eapply Disjoint_Included_r.
        2: apply H4.
        eauto with Ensembles_DB.
      }      
      rewrite fundefs_append_bound_vars.
      2: reflexivity.
      eapply Disjoint_Included_r.
      2: apply H7.
      eauto with Ensembles_DB.
      rewrite bound_var_Efun.
      rewrite fundefs_append_bound_vars.
      2: reflexivity.
      eapply Disjoint_Included_r.
      2: apply H2.
      eauto with Ensembles_DB.
      
      eapply Disjoint_Included_r.
      eapply of_fun_rm.
      eauto.
      apply H.
      eapply Disjoint_Included_l.
      2: apply Hdj.
      do 2 (rewrite bound_var_app_ctx).
      do 2 (rewrite bound_var_Efun).
      rewrite fundefs_append_bound_vars.
      2: reflexivity.
      rewrite fundefs_append_bound_vars with (B3 := (fundefs_append B1 (Fcons f t xs fb B2))).
      2: reflexivity.
      rewrite bound_var_fundefs_Fcons.
      eauto 25 with Ensembles_DB.
    + split.
      {
        rewrite inv_app_Econstr.
        rewrite app_ctx_f_fuse.
        rewrite app_ctx_f_fuse.
        rewrite inv_app_Econstr in Hub.
        rewrite app_ctx_f_fuse in Hub.
        rewrite app_ctx_f_fuse in Hub.
        eapply ub_case_inl.
        2: apply Hub.
        eexists; eauto.
      }
      eapply Disjoint_Included_r.
      eapply of_case_fold. apply H.
      eapply Disjoint_Included_l.
      2: apply Hdj.
      do 2 (rewrite bound_var_app_ctx).
      do 2 (rewrite bound_var_Econstr).
      do 2 (rewrite bound_var_app_ctx).
      apply Included_Union_compat.
      reflexivity.
      apply Included_Union_compat.
      apply Included_Union_compat.
      reflexivity.
      intro.
      intro.
      eapply Bound_Ecase. apply H0.
      apply findtag_In_patterns.
      eauto.
      reflexivity.
    + split.
      {
        rewrite inv_app_Econstr.
        rewrite app_ctx_f_fuse.
        rewrite app_ctx_f_fuse.
        rewrite inv_app_Econstr in Hub.
        rewrite app_ctx_f_fuse in Hub.
        rewrite app_ctx_f_fuse in Hub.
        eapply ub_proj_dead in Hub.
        apply ub_app_ctx_f in Hub.
        destructAll.
        rewrite bound_var_rename_all_ns in H2.
        eapply unique_bindings_rename_all_ns in H1.
        apply ub_app_ctx_f; eauto.
      }
      eapply Disjoint_Included_r.
      apply occurs_free_exp_ctx_included.
      apply of_constr_proj'.
      apply H.
      eapply Disjoint_Included_l.
      2: apply Hdj.
      do 2 (rewrite bound_var_app_ctx).
      repeat (normalize_bound_var).
      do 2 (rewrite bound_var_app_ctx).
      repeat normalize_bound_var.
      unfold rename.
      rewrite <- bound_var_rename_all_ns.
      eauto with Ensembles_DB.      
    + split.

      eapply ub_fun_inlining; apply Hub.

      eapply Disjoint_Included_r.
      apply of_fun_inline; eauto.
      eapply Disjoint_Included_l.
      2: apply Hdj.
      do 2 (rewrite bound_var_app_ctx).
      repeat (normalize_bound_var).
      do 2 (rewrite bound_var_app_ctx).
      rewrite <- bound_var_rename_all_ns.
      rewrite fundefs_append_bound_vars.
      2: reflexivity.
      rewrite fundefs_append_bound_vars with (B3 := (fundefs_append B1 (Fcons f t xs fb B2))).
      2: reflexivity.
      repeat normalize_bound_var.
      eauto 25 with Ensembles_DB.      
  - split; auto.
  - specialize (IHclos_refl_trans1 Hub Hdj).
    destructAll.
    apply IHclos_refl_trans2; auto.
Qed.


Definition closed e: Prop:=
  Same_set _ (Empty_set var) (occurs_free e).
  
Theorem gsr_preserves_clos:
  forall e e',
  unique_bindings e ->
  closed e -> 
  gsr_clos e e' ->
  unique_bindings e' /\
  closed e'.
Proof.
  intros e e' Hub Hdj H.
  induction H.
  - inv H. inv H0.
    + split.
      apply ub_app_ctx_f in Hub.
      apply ub_app_ctx_f. destructAll.
      inv H1.
      split; auto.
      split; auto.
      rewrite bound_var_Econstr in H2.
      eauto with Ensembles_DB.
      apply Included_Empty_set_l.
      eapply Proper_Included_r.
      auto.
      apply Hdj.
      apply of_constr_dead. apply H.
    + split.
      apply ub_app_ctx_f in Hub.
      apply ub_app_ctx_f. destructAll.
      inv H1.
      split; auto.
      split; auto.
      rewrite bound_var_Eprim in H2.
      eauto with Ensembles_DB.
      apply Included_Empty_set_l.
      eapply Proper_Included_r.
      auto.
      apply Hdj.
      apply of_prim_dead. apply H.
    + split.
      apply ub_app_ctx_f in Hub.
      apply ub_app_ctx_f. destructAll.
      inv H1.
      split; auto.
      split; auto.
      rewrite bound_var_Eproj in H2.
      eauto with Ensembles_DB.
      apply Included_Empty_set_l.
      eapply Proper_Included_r.
      auto.
      apply Hdj.
      apply of_proj_dead. apply H.
    + split.
      apply ub_app_ctx_f in Hub.
      apply ub_app_ctx_f. destructAll.
      inv H1.
      split; auto.
      split; auto.
      rewrite bound_var_Efun in H2.
      eauto with Ensembles_DB.
      apply Included_Empty_set_l.
      eapply Proper_Included_r.
      auto.
      apply Hdj.
      apply of_fun_dead. apply H.
    + apply ub_app_ctx_f in Hub.
      destructAll.
      inv H1.
      rewrite bound_var_Efun in H2.
      rewrite fundefs_append_bound_vars in H2. 2: reflexivity.
      rewrite bound_var_fundefs_Fcons in H2.
      rewrite fundefs_append_bound_vars in H7. 2: reflexivity.
      rewrite bound_var_fundefs_Fcons in H7. 
      split.
      apply ub_app_ctx_f.
      split; auto.
      split.
      constructor; auto.
      {
        eapply fundefs_append_unique_bindings_l in H6.
        2: reflexivity.
        destructAll.
        inv H3.
        eapply fundefs_append_unique_bindings_r; auto.
        rewrite bound_var_fundefs_Fcons in H4.
        eapply Disjoint_Included_r.
        2: apply H4.
        eauto with Ensembles_DB.
      }      
      rewrite fundefs_append_bound_vars.
      2: reflexivity.
      eapply Disjoint_Included_r.
      2: apply H7.
      eauto with Ensembles_DB.
      rewrite bound_var_Efun.
      rewrite fundefs_append_bound_vars.
      2: reflexivity.
      eapply Disjoint_Included_r.
      2: apply H2.
      eauto with Ensembles_DB.
      apply Included_Empty_set_l.
      eapply Proper_Included_r.
      auto.
      apply Hdj.
      eapply of_fun_rm.
      auto.
      auto.
    + split.
      {
        rewrite inv_app_Econstr.
        rewrite app_ctx_f_fuse.
        rewrite app_ctx_f_fuse.
        rewrite inv_app_Econstr in Hub.
        rewrite app_ctx_f_fuse in Hub.
        rewrite app_ctx_f_fuse in Hub.
        eapply ub_case_inl.
        2: apply Hub.
        eexists; eauto.
      }
      apply Included_Empty_set_l.
      eapply Proper_Included_r.
      auto.
      apply Hdj.
      eapply of_case_fold. auto. 
    + split.
      {
        rewrite inv_app_Econstr.
        rewrite app_ctx_f_fuse.
        rewrite app_ctx_f_fuse.
        rewrite inv_app_Econstr in Hub.
        rewrite app_ctx_f_fuse in Hub.
        rewrite app_ctx_f_fuse in Hub.
        eapply ub_proj_dead in Hub.
        apply ub_app_ctx_f in Hub.
        destructAll.
        rewrite bound_var_rename_all_ns in H2.
        unfold rename.        
        eapply unique_bindings_rename_all_ns in H1.
        apply ub_app_ctx_f; eauto.
      }
      apply Included_Empty_set_l.
      eapply Proper_Included_r.
      auto.
      apply Hdj.
      apply occurs_free_exp_ctx_included.
      apply of_constr_proj'.
      auto.
    + split.

      eapply ub_fun_inlining; apply Hub.

      apply Included_Empty_set_l.
      eapply Proper_Included_r.
      auto.
      apply Hdj.
      apply of_fun_inline; eauto.
  - split; auto.
  - specialize (IHclos_refl_trans1 Hub Hdj).
    destructAll.
    apply IHclos_refl_trans2; auto.
Qed.  

Theorem grs_in_gr: forall e e',
  unique_bindings e ->
  Disjoint _ (bound_var e) (occurs_free e) ->
  gsr_clos e e' ->
  gr_clos e e'.
Proof.
  intros.
  induction H1.
  - apply sr_rw_in_rw; auto.
  - apply rt_refl.
  - eapply rt_trans; eauto.
    apply IHclos_refl_trans1; auto.
    apply rw_preserves in H1_ ; auto.
    destruct H1_.
    apply IHclos_refl_trans2; auto.
Qed.

Corollary sr_correct e e' :
  unique_bindings e ->
  Disjoint _ (bound_var e) (occurs_free e) ->
  gsr_clos e e' ->
  forall pr cenv rho rho' k, 
  preord_env_P pr cenv (occurs_free e) k rho rho'->
  preord_exp pr cenv k (e, rho) (e', rho'). 
Proof.
  intros.
  apply rw_correct.
  apply grs_in_gr; auto.
  auto.
Qed.

End Shrink_Rewrites.


Require Import Coq.Relations.Relations.
Require Import Coq.Relations.Relations.
Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.Morphisms.
Import RelationClasses.

Require Import ExtLib.Data.Bool.
Require Libraries.Maps.
Require Coq.funind.Recdef.
Import Nnat.
Require Import Coq.Arith.Arith Coq.NArith.BinNat ExtLib.Data.String ExtLib.Data.List Coq.omega.Omega Coq.Program.Program Coq.micromega.Psatz Coq.Sets.Ensembles Coq.Logic.Decidable Coq.Lists.ListDec.
Require Import Libraries.CpdtTactics Coq.Sorting.Permutation.
Require Import Libraries.HashMap.
Require Import Libraries.maps_util.
Require Import Libraries.Coqlib L6.Ensembles_util. 
Require Import L6.cps.
Require Import L6.ctx L6.logical_relations.
Require Import L6.cps_util L6.List_util L6.shrink_cps L6.eval L6.set_util L6.identifiers.

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

  (* rewrite rules that 
     - preserves semantics
     - produces a smaller exp
     - preserves the unique binding invariant 

  Fun_split separates a group of mutually recursive functions lrf into two (lf and rf) where the functions bound in rf do not appear in lf 
     Fun_inline replaces one occurence on f by its definition
     Fun_dead removes the definition of a set of functions if none of them occur in the rest of the program
     Constr_dead removes the binding of a datatype when it doesn't appear in the rest of the program 
     Constr_proj replaces a binding by the nth projection of a datatype when the datatype is known (in ctx) 
     Constr_case reduces a pattern match into an application of the right continuation on the datatype when the datatype is know (in ctx)
*)
  Inductive rw: relation exp :=
  (* Rules about dead function elimination *)
| Constr_dead: forall x t ys e, 
                 num_occur e x 0 ->
                 rw (Econstr x t ys e) e
| Prim_dead: forall x p ys e,
               num_occur e x 0 ->
               rw (Eprim x p ys e) e
| Proj_dead: forall x t n y e,
               num_occur e x 0 ->
               rw (Eproj x t n y e) e
| Fun_dead: forall e fds,
              Forall (fun v => num_occur e v 0) (all_fun_name fds) ->
              rw (Efun fds e) e 
| Fun_rem: forall f t xs fb B1 B2 e,
             unique_bindings_fundefs (fundefs_append B1 (Fcons f t xs fb B2)) ->
                                     (* ~  name_in_fundefs (fundefs_append B1 (Fcons f t xs fb B2)) f ->              (* see rm1_fundefs  on how this could be removed, would also need to change preord_env_P_Same_set_fun_in_fundefs *)  *)
               num_occur (Efun (fundefs_append B1 (Fcons f t xs fb B2)) e) f 0 -> 
               rw (Efun (fundefs_append B1 (Fcons f t xs fb B2)) e) (Efun (fundefs_append B1 B2) e)

(* Rules about inlining/constant-folding *)
| Constr_case: forall x c cl co e ys,
      findtag cl co = Some e ->
      ~bound_var_ctx c x ->
      rw (Econstr x co ys (c |[ Ecase x cl ]|)) (Econstr x co ys (c |[e]|))

| Constr_proj: forall v  t t' n x e k ys c, 
                 (* nothing shadows constructor x or var k in c *)
                 ~ bound_var_ctx c x ->
                 ~ bound_var_ctx c k ->
                 (* nothing rebinds the projection k or v in the rest of the term c' *) 
                 ~ bound_var e v ->
                 ~ bound_var e k ->
                 x <> k ->
                 v <> k ->
                 (* everything up could be reduced to ub & Disjoint like in Fun_Inline *) 
                 nthN ys n = Some k -> 
                 rw (Econstr x t ys (c |[Eproj v t' n x e]|)) (Econstr x t ys (c |[ rename k v e]|))
| Fun_inline: forall c  vs f  t xs fb  fds,
                (*  nothing rebinds vs's in c'e *)
                unique_bindings (Efun fds (c |[ Eapp f t vs ]|))  ->
                Disjoint var (occurs_free (Efun fds (c |[ Eapp f t vs ]|))) (bound_var (Efun fds (c |[ Eapp f t vs ]|))) ->
                get_fun f fds = Some (t, xs, fb) ->
                rw (Efun fds (c |[ Eapp f t vs ]|)) (Efun fds (c |[ (rename_all (set_list (combine xs vs) (M.empty var)) fb)]|))                     
(* Other rules *)                 
(*

        *)
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



Lemma not_occur_not_free:
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
  
  
(* this is  preord_env_P_set_not_in_P_l *)
  Lemma rm_set_p: forall P k rho rho' v m,
    ~ P v -> 
   preord_env_P pr cenv P k rho rho' ->
  preord_env_P pr cenv P k
    (M.set v m rho) rho'.
  Proof.
    intros; intro; intros.
    intro. intros. destruct (var_dec x v).
    + subst. exfalso; auto.
    + rewrite M.gso in H2 by auto.
      apply H0 in H2.
      auto. auto.
  Qed.

  Lemma rm_set_p': forall P k rho rho' v m,
    ~ P v -> 
   preord_env_P pr cenv P k rho rho' ->
  preord_env_P pr cenv P k
    rho (M.set v m rho').
  Proof.
    intros; intro; intros.
    intro. intros. destruct (var_dec x v).
    + subst. exfalso; auto.
    + rewrite M.gso  by auto.
      apply H0 in H2.
      auto. auto.
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
    - subst. exfalso. revert H2; apply not_occur_not_free. auto.
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
    apply not_occur_not_free in H.
    eapply rm_set_p in H0; eauto.
    eapply preord_exp_refl in H12; eauto.
  Qed.

  

  Corollary  rm_constr :
   forall k rho rho' e' v t l,
     num_occur e' v 0 ->
  preord_env_P pr cenv (occurs_free (Econstr v t l e')) k rho rho' ->
  preord_exp  pr cenv k (Econstr v t l e', rho) (e', rho').
  Proof.
    intros; intro; intros.
    inversion H2; subst.
    rewrite occurs_free_Econstr in H0.
    apply not_occur_not_free in H.
    assert (preord_env_P pr cenv
                         (occurs_free e') k rho rho').
    eapply preord_env_P_antimon.
    apply H0.
    right. split. auto. intro. inv H4. 
     apply H. auto.
    eapply rm_set_p in H3; eauto.
    eapply preord_exp_refl in H12; eauto.
  Qed.

  Corollary rm_prim:
    forall k rho rho' e x p l,
      num_occur e x 0 ->
      preord_env_P pr cenv (occurs_free (Eprim x p l e)) k rho rho' ->
      preord_exp pr cenv k (Eprim x p l e, rho) (e, rho').
  Proof.
        intros; intro; intros.
    inversion H2; subst.
    rewrite occurs_free_Eprim in H0.
    apply not_occur_not_free in H.
    assert (preord_env_P pr cenv
                         (occurs_free e) k rho rho').
    eapply preord_env_P_antimon.
    apply H0.
    right. split. auto. intro. inv H4. 
     apply H. auto.
    eapply rm_set_p in H3; eauto.
    eapply preord_exp_refl in H14; eauto.
  Qed.


  Corollary rm_proj:
    forall k rho rho' e x t n y,
      num_occur e x 0 ->
      preord_env_P pr cenv (occurs_free (Eproj x t n y e)) k rho rho' ->
      preord_exp pr cenv k (Eproj x t n y e, rho) (e, rho').
  Proof.
            intros; intro; intros.
    inversion H2; subst.
    rewrite occurs_free_Eproj in H0.
    apply not_occur_not_free in H.
    assert (preord_env_P pr cenv
                         (occurs_free e) k rho rho').
    eapply preord_env_P_antimon.
    apply H0.
    right. split. auto. intro. inv H4. 
     apply H. auto.
    eapply rm_set_p in H3; eauto.
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
    assert (Hof := (not_occur_not_free x)).
    destruct Hof.
    specialize (H3 e).
    apply H3; auto.
    rewrite Forall_forall in H.
    apply H.
    apply all_name_fundefs; auto.
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
       apply rm_set_p'.
       apply not_occur_not_free.
       rewrite Forall_forall in H.
       apply H.
       eapply fundefs_suffix_in.
       eauto.
       auto.
     -simpl. apply preord_env_P_refl.
   Qed.

   




     Inductive unique_name_fundefs: fundefs -> Prop :=
     | Uname_Fcons: forall f tau ys e defs,
                      ~ name_in_fundefs defs f ->
                      unique_name_fundefs defs ->
                      unique_name_fundefs (Fcons f tau ys e defs)
     | Uname_Fnil:
         unique_name_fundefs Fnil
     .


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


       
     Theorem unique_binding_split: forall fds,
                                     unique_name_fundefs fds ->
                                     forall fds' fds'',
                                       split_fds fds' fds'' fds ->
                                       unique_name_fundefs fds' /\ unique_name_fundefs fds''.
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
           auto. auto.
         + specialize (IHfds _ _ H5).
           destruct IHfds.
           split.  auto.
           constructor.
           intro.
           apply H3.
           eapply split_fds_name_in_fundefs.
           eauto.
           right; auto.
           auto.
       - apply split_fds_to_nil in H0.
         destruct H0; subst.
         split; constructor.
     Qed.


  Theorem rm_fundefs': forall k rho e fds,
    Forall (fun v => num_occur e v 0) (all_fun_name fds) ->
    preord_exp pr cenv k (Efun fds e, rho) (e, rho). 
  Proof.
    intros; intro; intros.
    inversion H1; subst.
    eapply preord_exp_refl in H7; eauto.
    eapply rm_fundefs_env.
    apply H. exists Fnil. simpl. auto.
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
         num_occur (Efun fds' e) f 0 ->
         ~ name_in_fundefs fds' f ->                  
         preord_env_P pr cenv (Union _ (occurs_free (Efun fds' e)) (name_in_fundefs fds')) k (def_funs (Fcons f t xs fb fds') (Fcons f t xs fb fds') rho1 rho1) (def_funs fds' fds' rho1 rho1).
  Proof.
    induction k as [ k IH' ] using lt_wf_rec1.
    intros. simpl. intro. intros.
    assert (Hxf: x <> f).
    {
      intro; subst.
      inv H1.
      revert H2.
      apply (proj1 (not_occur_not_free f)).
      auto.
      apply H0. auto.
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

  

  (* can remove ~name_in_fundefs assumption after showing that another f would always be shadowed so could be removed in the first place *)
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
      inv H; subst. apply plus_is_O in H3. destruct H3; subst. constructor; auto.
      inv H6. apply plus_is_O in H10. destruct H10; subst. simpl; auto.
      auto.
      rewrite occurs_free_Efun.
      intro. intros.
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
                            unique_bindings_fundefs B ->
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
    assert (Hub : unique_bindings_fundefs (fundefs_append (Fcons f t xs fb B1) B2)). {
      eapply fundefs_append_unique_bindings_l in H. 2: reflexivity.
      destructAll. inv H3. simpl. constructor; auto.
      rewrite bound_var_fundefs_Fcons in H4.
      intro.
      eapply fundefs_append_bound_vars in H3.
      2: reflexivity.
      inv H4. specialize (H5 f). 
      inv H3.
      apply H5. eauto with Ensembles_DB.
      apply H11. auto.
      rewrite bound_var_fundefs_Fcons in H4.
      erewrite fundefs_append_bound_vars.
      2: reflexivity.
      eauto with Ensembles_DB.
      rewrite bound_var_fundefs_Fcons in H4.
      erewrite fundefs_append_bound_vars.
      2: reflexivity.
      eauto with Ensembles_DB.
      eapply fundefs_append_unique_bindings_r.
      reflexivity.
      auto.
      auto.
      rewrite bound_var_fundefs_Fcons in H4.
      eauto with Ensembles_DB.
    }
    
    eapply preord_exp_trans.
    apply preord_exp_refl. apply H2.
    intros.
    eapply preord_exp_trans.
    -   intro. intros.
      inv H4. eapply preord_exp_refl in H10.
      Focus 2.
      
      eapply preord_env_P_Same_set_fun_in_fundefs.
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
      constructor. auto.
      apply fundefs_append_num_occur' in H9. destructAll.
      inv H4. apply plus_is_O in H5. destruct H5.
      apply plus_is_O in H5. destruct H5; subst. rewrite <- plus_0_l.
      eapply fundefs_append_num_occur. reflexivity.
      auto. auto.
      inv Hub.
      intro; apply H11.
      apply name_in_fundefs_bound_var_fundefs. auto.
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



(* move to ctx *)
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
      + edestruct setlist_length as [rho2' Hs']; eauto.
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
      + subst. edestruct setlist_length as [rho2' Hs']; eauto.
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
      + edestruct setlist_length as [rho2' Hs']; eauto.
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
      + subst. edestruct setlist_length as [rho2' Hs']; eauto.
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

Theorem Decidable_singleton_var: forall v, Decidable (Singleton var v).
Proof.
  intro.
  apply Build_Decidable.
  intro.
  destruct (var_dec v x).
  subst; left; constructor.
  right; intro.
  apply n; inversion H; auto.
Qed.

 


 Definition eq_env_P:  Ensemble var -> env -> env -> Prop :=
    fun S rho1 rho2 =>
      forall x, S x -> M.get x rho1 = M.get x rho2.

  Theorem eq_env_P_refl: forall S r, eq_env_P S r r.
  Proof.
    intros; intro; intros. reflexivity.
  Qed.

  Theorem eq_env_P_sym: forall S r r', eq_env_P S r r' -> eq_env_P S r' r.
  Proof.
    intros; intro. intro. apply H in H0. auto.
  Qed.
  
  Theorem eq_env_P_trans: forall S r1 r2 r3,
                            eq_env_P S r1 r2 -> eq_env_P S r2 r3 -> eq_env_P S r1 r3.
  Proof.
    intros. intro. intros.
    specialize (H x H1).
    specialize (H0 x H1).
    rewrite H. auto.
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

Theorem eq_env_P_getlist: forall S rho rho',
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
      + edestruct setlist_length as [rho2' Hs']; eauto.
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
      + subst. edestruct setlist_length as [rho2' Hs']; eauto.
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

(*This means that only bound variables in the context will modify the context *)
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
    revert S c rho1 rho2 e1 e2. induction k as [ k IH' ] using lt_wf_rec1.
    induction c; intros rho1 rho2 e1 e2 Hyp Hbv Hpre; eauto.
    - simpl. apply Hyp. auto.
      simpl in Hpre. apply Hpre.
      apply eq_env_P_refl.
      apply eq_env_P_refl.
    -         rewrite bound_var_Econstr_c in Hbv. 
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
      rewrite bound_var_Eproj_c in Hbv.
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
      rewrite bound_var_Eprim_c in Hbv.
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
      rewrite bound_var_Case_c in Hbv.
      eapply Disjoint_Included_l; eauto.
      right. left; auto.
      eapply preord_env_P_antimon; eauto.
      simpl. intros x0 H.
      eapply occurs_free_Ecase_Included; eauto.
      eapply in_or_app. right. left; eauto.
    - simpl.
      rewrite bound_var_Fun1_c in Hbv.
      eapply preord_exp_fun_compat; eauto.      
      assert (Disjoint _ S (name_in_fundefs f)).
      {
        eapply Disjoint_Included_l in Hbv.
        apply Disjoint_sym. apply Hbv.
        left.
        apply name_in_fundefs_bound_var_fundefs.
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
        * rewrite bound_var_Fun2_c in Hbv.
          assert (Hbv' := Disjoint_Union_l  _ _ _ Hbv).
          eapply preord_env_P_def_funs_compat_pre_vals_set; eauto.
          intros. eapply IH'; eauto.
          intros.
          eapply Hyp; eauto.
          omega.
          eapply eq_env_P_trans.
          apply H1. auto.
          eapply eq_env_P_trans. apply H2. auto.
          eapply preord_env_P_antimon; [ eassumption |].
          intros x' H'. simpl. inv H'.
          now eapply Free_Efun2.
          inv H. constructor; eauto.
        * eapply Ensembles_util.Included_trans.
          eapply occurs_free_Efun_Included.
          normalize_occurs_free. eauto with Ensembles_DB. 
      + repeat eexists; eauto. simpl. constructor; eauto.
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
    eapply preord_exp_compat_vals_set with (S := FromList xs); eauto.
    intros. apply H; eauto.
    erewrite <- eq_env_P_getlist.
    eauto.
    eauto. intro; auto.
    erewrite <- eq_env_P_getlist.
    eauto.
    eauto. intro; auto.
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



    Corollary preord_exp_compat_val x k val rho1 rho2 c e1 e2 :
    (forall k rho1 rho2, preord_env_P pr cenv (occurs_free e1) k rho1 rho2 ->
                         M.get x rho1 = Some val ->                         
                         preord_exp pr cenv k (e1, rho1) (e2, rho2)) ->
    ~ bound_var_ctx c x ->
    M.get x rho1 = Some val ->  
    preord_env_P pr cenv (occurs_free (c |[ e1 ]|)) k rho1 rho2 ->
    preord_exp pr cenv k (c |[ e1 ]|, rho1) (c |[ e2 ]|, rho2).
  Proof.
    intros.
    eapply preord_exp_compat_vals_set with (S := Singleton _ x); auto.
    intros.
    apply H. auto. specialize (H5 x). rewrite <- H1.
    symmetry. apply H5.
    constructor.
    split. intro. intro. apply H0.
    inv H3. inv H5. auto.
Qed.
  
  
  (* TODO: move this somewhere else *)
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
      ~bound_var_ctx c x ->
      preord_env_P pr cenv (occurs_free (Econstr x c0 ys (c |[ Ecase x cl ]|))) k rho1 rho2 ->
      preord_exp pr cenv k (Econstr x c0 ys (c |[ Ecase x cl ]|), rho1) (Econstr x c0 ys (c |[ e ]|), rho2). 
  Proof.
    intros; intro; intros. inversion H3; subst.
    assert (Hl : Included var (FromList ys) (occurs_free (Econstr x c0 ys (c |[ Ecase x cl ]|)))).  rewrite occurs_free_Econstr. left; auto.
    assert (H11' := preord_env_P_getlist_l _ _ _ _ _ _ _ _ H1 Hl H11). destructAll.
    eapply preord_exp_compat_val in H13; eauto.
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




Lemma rename_clos_constr_l': forall x y v p e l' l ,
                                rename_clos x y (Econstr v p (l++l') e) (Econstr v p (l++(apply_r_list (M.set x y (M.empty var)) l')) e).
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

  Theorem rename_clos_constr_l: forall x y v p e l ,
                                rename_clos x y (Econstr v p l e) (Econstr v p (apply_r_list (M.set x y (M.empty var)) l) e).
  Proof.
    intros. apply rename_clos_constr_l' with (l := nil).
  Qed.
  
Theorem rename_clos_prim_l': forall x y v p e l' l,
                                rename_clos x y (Eprim v p (l++l') e) (Eprim v p (l++(apply_r_list (M.set x y (M.empty var)) l')) e).
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

  Theorem rename_clos_prim_l: forall x y v p e  l,
                                rename_clos x y (Eprim v p l e) (Eprim v p (apply_r_list (M.set x y (M.empty var)) l) e).
Proof.    
  intros.
  apply rename_clos_prim_l' with (l := nil).
Qed.

Theorem rename_clos_app_l': forall x y f c l' l,
                                rename_clos x y (Eapp f c (l++l')) (Eapp f c (l++(apply_r_list (M.set x y (M.empty var)) l'))).
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

Theorem rename_clos_app_l: forall x y f c  l,
                                rename_clos x y (Eapp f c l) (Eapp f c (apply_r_list (M.set x y (M.empty var)) l)).
Proof.  
  intros.
  apply rename_clos_app_l' with (l := nil).
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
      unfold apply_r. destruct (M.get v0 sigma) eqn:gv0s.
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
      destruct (M.get v sigma) eqn:gvs.
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


Theorem num_occur_n:
  forall e x n m,
  num_occur e x n ->
  n = m ->
  num_occur e x m.
Proof.
  intros; subst. apply H.
Qed.

Theorem num_occur_fds_n:
  forall f x n m,
  num_occur_fds f x n ->
  n = m ->
  num_occur_fds f x m.
Proof.
  intros; subst. apply H.
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

      

  Transparent rename.
  Theorem rename_corresp: forall y x,
                            (forall e,
                               Disjoint _ (bound_var e) (FromList [x;y]) ->
                               rename_clos x y e (rename y x e)) /\
                            (forall fds,
                               Disjoint _ (bound_var_fundefs fds) (FromList [x;y]) ->
                               rename_fds_clos x y fds (rename_all_fun (M.set x y (M.empty var)) fds)).
  Proof.
    intros y x. eapply exp_def_mutual_ind; intros; simpl.
    -  unfold rename.
      simpl.
      eapply rt_trans.
      apply rename_clos_constr_l.
      do 2 (rewrite inv_app_Econstr).
      apply rename_context_clos.
      rewrite bound_var_Econstr in H0.
      assert (Hde := Disjoint_Union_l _ _ _ H0).
      apply H in Hde.
      erewrite (proj1 prop_rename_all).
      apply Hde.
      eapply smg_trans.
      apply remove_set_2.
      intro.
      inv H0.
      specialize (H2 x).
      apply H2.
      split.
      right; auto.
      constructor; auto.
      apply proper_set.
      apply remove_empty.
    - unfold rename. simpl. unfold apply_r.
      destruct (var_dec v x).
      + subst. rewrite M.gss. apply rt_step.
        rewrite inv_app_Hole.
      rewrite inv_app_Hole at 1.
      constructor.
      constructor. 
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
      constructor. constructor.
      rewrite M.gso by auto. rewrite M.gempty.
      apply rt_refl.      
      eapply rename_clos_case.
      unfold rename in H0. simpl in H0.
      eapply rename_case_one_step.        
      apply H0. reflexivity. reflexivity.         
      apply H. 
    - unfold rename.
      simpl.
      rewrite bound_var_Eproj in H0.      
      assert (Hde := Disjoint_Union_l _ _ _ H0).
      assert (Hdv := Disjoint_Union_r _ _ _ H0).
      apply H in Hde.
      inversion Hdv.
      destruct (var_dec v x).
      exfalso. specialize (H1 v).
      apply H1.
      subst. split; auto. constructor. auto.
      eapply rt_trans.
      Focus 2.
      assert (map_get_r var (M.remove v (M.set x y (M.empty var))) (M.set x y (M.empty var))).
      eapply smg_trans.
      apply remove_set_2; eauto.
      apply proper_set.
      apply remove_empty.
      assert (Hpr := prop_rename_all).
      destruct Hpr.
      erewrite (H3 _ _ _ H2).
      rewrite inv_app_Eproj.
      apply rename_context_clos.
      apply Hde.
      destruct (var_dec x v0).
      + subst. 
      unfold apply_r. rewrite M.gss.
      simpl.
      
      rewrite inv_app_Hole.
      rewrite inv_app_Hole at 1.
      apply rt_step.
      constructor. constructor.
      + unfold apply_r. rewrite M.gso by auto. rewrite M.gempty.
        apply rt_refl.
    - unfold rename. simpl.
      rewrite bound_var_Efun in H1.
      assert (Hdf := (Disjoint_Union_l _ _ _ H1)).
      assert (Hde := Disjoint_Union_r _ _ _ H1).
      specialize (H Hdf).
      specialize (H0 Hde).
      eapply rt_trans.
      rewrite inv_app_Efun1.
      apply rename_context_clos.
      eauto.
      simpl.
      erewrite (proj1 prop_rename_all).
      Focus 2.
      eapply smg_trans.
      apply remove_all_not_in. intro. inversion Hdf. specialize (H3 x). apply H3.
      split.
      apply name_in_fundefs_bound_var_fundefs.
      apply name_fds_same. auto.
      constructor. auto.
      apply proper_set.
      apply remove_all_empty.
      apply rename_fds_Efun.
      erewrite (proj2 prop_rename_all).
      apply H.
      eapply smg_trans.
      apply remove_all_not_in. intro.
      inversion Hdf. specialize (H3 x). apply H3.
      split.
      apply name_in_fundefs_bound_var_fundefs.
      apply name_fds_same. auto.      
      constructor. auto.
      apply proper_set.
      apply remove_all_empty.
    - unfold rename. simpl.
      unfold apply_r.
      destruct (var_dec x v).
      + subst.
        rewrite M.gss.
        eapply rt_trans.
        apply rt_step.
        rewrite inv_app_Hole at 1.
        constructor. constructor.
        simpl.
        apply rename_clos_app_l.
      + rewrite M.gso by auto.
        rewrite M.gempty.
        apply rename_clos_app_l.
    - unfold rename.
      simpl.
      eapply rt_trans.
      apply rename_clos_prim_l.
      do 2 (rewrite inv_app_Eprim).
      apply rename_context_clos.
      rewrite bound_var_Eprim in H0.
      assert (Hde := Disjoint_Union_l _ _ _ H0).
      apply H in Hde.
      erewrite (proj1 prop_rename_all).
      apply Hde.
      eapply smg_trans.
      apply remove_set_2.
      intro.
      inv H0.
      specialize (H2 x).
      apply H2.
      split.
      right; auto.
      constructor; auto.
      apply proper_set.
      apply remove_empty.
    - unfold rename.
      simpl. unfold apply_r. destruct (var_dec x v).
      subst. rewrite M.gss. constructor.
      rewrite inv_app_Hole.
      rewrite inv_app_Hole at 1.
      constructor; constructor.
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
      eapply rt_trans.
      rewrite inv_app_Fcons1.
      eapply rename_context_fds_clos.
      apply Hdee.      
      simpl.
      erewrite (proj1 prop_rename_all).
      Focus 2.
      eapply smg_trans.
      apply remove_all_not_in. intro. inversion Hdl. specialize (H3 x). apply H3.
      split. apply H2. constructor. auto.
      apply proper_set.
      apply remove_all_empty.
      apply rename_fds_Fcons2.
      auto.
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
                             ~ bound_var_ctx c x ->
                             ~ bound_var_ctx c y ->
                             ~ bound_var_ctx c' x' ->
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
    eapply preord_exp_compat_vals with (xs := x::y::nil) in H18; eauto.
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
      eapply preord_exp_compat_vals with (xs := x'::y::nil) in H32; eauto.
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
        apply H2. auto.
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
                             ~ bound_var_ctx c x ->
                             ~ bound_var_ctx c y ->
                             ~ bound_var e x' ->
                             ~ bound_var e y  ->
                             x <> y ->
                             rename_clos x' y e e' ->
                             nthN ys n = Some y ->
                             forall k rho1 rho2,
                             preord_env_P pr cenv (occurs_free (Econstr x t ys (c |[ Eproj x' t' n x e ]|))) k rho1 rho2 ->
                             preord_exp pr cenv k (Econstr x t ys (c |[ Eproj x' t' n x e ]|) , rho1 )
                                        (Econstr x t ys (c |[ Eproj x' t' n x e' ]|), rho2).
  Proof.                                                           
    intros.
    revert k rho1 rho2 H6.
    induction H4.
    - inversion H4; subst.
      intros.
      eapply rw_proj1_equiv; eauto.
      intro. apply H1. apply bound_var_app_ctx. left; auto.
      intro. apply H2. apply bound_var_app_ctx. left; auto. 
    - intros. apply preord_exp_refl. apply H6.
    - intros.
      eapply preord_exp_trans.
      apply IHclos_refl_trans1.
      auto.
      auto.
      apply H6.
      intro.
      apply IHclos_refl_trans2.
      apply bound_var_rename in H4_.
      intro. apply H1.
      apply H4_. auto.
      intro. apply H2.
      apply bound_var_rename in H4_.
      apply H4_. auto.
      apply preord_env_P_refl.
  Qed.


  
  (* rw rule for proj *)
  Corollary rw_proj_equiv : forall  x x' t t' ys  y e c n k rho1 rho2,
                             ~ bound_var_ctx c x ->
                             ~ bound_var_ctx c y ->
                             ~ bound_var e x' ->
                             ~ bound_var e y  ->
                             x <> y ->
                             x' <> y ->
                             nthN ys n = Some y ->                        
                             preord_env_P pr cenv (occurs_free (Econstr x t ys (c |[ Eproj x' t' n x e ]|))) k rho1 rho2 ->
                             preord_exp pr cenv k (Econstr x t ys (c |[ Eproj x' t' n x e ]|) , rho1 )
                                        (Econstr x t ys (c |[ rename y x' e ]|), rho2).
  Proof.                                                           
    intros.
    assert (rename_clos x' y e (rename y x' e)).
    apply rename_corresp.
    split.
    intros.
    intro. inversion H7. inv H9.
    auto.
    inv H11. auto.
    inversion H9.
    eapply preord_exp_trans.
    eapply rw_proj_clos_equiv; eauto.
    intros.
    do 2 (rewrite inv_app_Econstr).
    do 2 (rewrite app_ctx_f_fuse). 
    apply preord_exp_compat.
    intros.
    assert (num_occur (rename y x' e) x' 0).
    apply rename_dead_var. auto.
    split. intro. intro. apply H1. 
    inv H9. inv H11.
    auto.
    apply rm_proj.
    auto.
    2: apply preord_env_P_refl.
    eapply preord_env_P_antimon.
    apply H8.
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
    Disjoint var (bound_var_ctx c) (occurs_free_fundefs fl)  ->
    Disjoint var (bound_var_ctx c) (name_in_fundefs fl)  -> 
    preord_exp pr cenv k (Efun fl (c |[ e ]|) , rho1) (Efun fl (c|[ e' ]|), rho2).
Proof.
  intros. intro. intros.
  inv H4.
  eapply preord_exp_compat_vals_set in H10; eauto.
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

(* could make that more general like rename_loc_equiv *)
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

Theorem setlist_rename_all:
  forall xs ys vs rho2 rho2',
    NoDup xs ->
    getlist ys rho2 = Some vs ->
    setlist xs vs rho2 = Some rho2'  ->
    forall fb,
      (Disjoint _ (bound_var fb) (FromList xs)) ->
      (Disjoint _ (bound_var fb) (FromList ys)) ->
    (Disjoint _ (FromList ys) (FromList xs)) ->
    forall k,
    preord_exp pr cenv k (fb, rho2')
               (rename_all (set_list (combine xs ys) (M.empty var)) fb, rho2).
Proof.
  induction xs; intros ys vs rho2 rho2' Nb; intros.
  - inv H0. destruct vs; inv H5.
    rewrite <- (proj1 rename_all_empty).
    apply preord_exp_refl. apply preord_env_P_refl.    
  - assert (length (a::xs) = length vs).
    eapply setlist_length_eq. apply H0.
    destruct vs; simpl in H4.
    inv H4.
    simpl in H0.
    assert (length ys = length (v::vs)).
    eapply getlist_length_eq. apply H.
    destruct ys; simpl in H3. inv H5.
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
    specialize (IHxs _ _ _ _  H8 glyr2 slxr2).
    clear H7 H8.
    inv H0.
    
    assert (rename_clos a e fb (rename e a fb)).
    {
      apply (proj1 (rename_corresp e a)).
      split.
      intro.
      intro.
      inv H.
      inv H6.
      inv H1. specialize (H x). apply H.
      split; auto.
      constructor. auto.
      inv H.
      inv H2.
      specialize (H x). apply H.
      split. auto. constructor; auto.
      inv H6.
    }            
    eapply preord_exp_trans.
    eapply preord_exp_trans.    
    eapply preord_rename_clos.
    3: apply H.
    eapply Disjoint_FromList_r. apply H1.
    constructor; auto.
    eapply Disjoint_FromList_r. apply H2.
    constructor; auto.
    destruct (var_dec e a). subst.
    rewrite M.gss. auto. 
    rewrite M.gso by auto.
    erewrite <- setlist_not_In.
    apply ger2.
    apply slxr2.
    intro. inv H3.
    specialize (H6 e).
    apply H6.
    split. constructor. auto.
    constructor 2. apply H0.
    intros.    
    apply rm_set.
    assert (e <> a).
    intro. subst.
    inv H3. specialize (H0 a).
    apply H0.
    split; auto. constructor; auto.
    constructor; auto.    
    apply (proj1 (rename_dead_var e a H0)).
    eapply Disjoint_FromList_r. apply H1. constructor; auto.
    intro.
    eapply preord_exp_trans.
    apply IHxs.
    rewrite <- bound_var_rename; eauto.
    eapply Disjoint_FromList_cons. eauto.
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
    inv H3. specialize (H6 e).
    apply H6. split; auto.
    constructor; auto.
    constructor 2; auto.
Qed.

(* todo: replace get_fun with find_def in shrink_cps *)
Theorem find_get_fun: forall f fds,
  get_fun f fds = find_def f fds.
Proof.
  induction fds.
  - simpl. rewrite IHfds. reflexivity.
  -   reflexivity.
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


Theorem rw_fun_corr:
  forall f fds t xs fb vs c rho1 rho2 k,
  get_fun f fds = Some (t, xs, fb) ->
  (* lot of these can be reduces to unique_binding and closed top level *)
  Disjoint _ (Union _ (FromList xs) (bound_var fb)) (FromList vs) ->
  unique_bindings_fundefs fds -> 
  Disjoint var (bound_var_ctx c) (occurs_free_fundefs fds)  ->
  Disjoint var (bound_var_ctx c) (bound_var_fundefs fds)  -> 
  List.NoDup xs ->
  preord_env_P pr cenv (occurs_free (Efun fds (c |[ Eapp f t vs ]|))) k rho1 rho2 ->
  preord_exp pr cenv k (Efun fds (c |[ Eapp f t vs ]|), rho1)
                             (Efun fds (c |[ (rename_all (set_list (combine xs vs) (M.empty var)) fb)]|), rho2).
Proof.
  intros f fds t xs fb vs c rho1 rho2 k H H0 Hub H1 H2 H3 H4.
  apply fun_inline_compat_clos; auto.
  (* probably want this compat clos to also show that fds is already bound to the right thing in rho2' *)
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
  rewrite find_get_fun in H. rewrite H in fdffl. inv fdffl. split; auto.
  eapply find_def_name_in_fundefs.
  rewrite <- find_get_fun. eauto.
  right.
  eapply find_def_name_in_fundefs.
  rewrite <- find_get_fun. eauto.
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
  rewrite find_get_fun in H.
  eapply Disjoint_bindings_find_def; eauto.
  
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


  intro.
  apply preord_exp_refl.
  eapply preord_env_P_setlist_l with (P1 := Setminus _ (occurs_free fb) (FromList xs)).
  5: apply H14.
  4: apply H13.
  Focus 3. apply Forall2_refl. apply preord_val_refl.
  Focus 3. eapply Disjoint_Included_r.
  apply name_in_fundefs_bound_var_fundefs.
  auto.
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
  eapply find_def_free_included. rewrite <- find_get_fun. apply H. apply H18.
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
    left. eapply find_def_free_included. rewrite <- find_get_fun. apply H.
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
      apply rm_fundefs; auto.
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
      {
        split. intro; intro. inv H4.
        
        (* check if x is bound in c0 *)
        assert (Hof := Decidable_occurs_free (c0 |[ Eapp f t vs ]|)).
        inv Hof. specialize (Dec x). 
        rewrite occurs_free_Efun in H2. rewrite bound_var_Efun in H2.
        destruct Dec.
        + inv H2. specialize (H7 x).
          apply H7.
          split. right.          
          split. apply H4.
          intro. inv H.
          assert (Hdj := Disjoint_bindings_fundefs _ _ _ _ _ H11 H3). inv Hdj.
          specialize (H x). apply H. split; auto.
          left.
          inv H5.
          eapply name_boundvar_arg. apply H2.
          rewrite find_get_fun in H3. apply H3.
          eapply bv_in_find_def. 
          rewrite find_get_fun in H3. apply H3.
          auto. 
        + assert (bound_var_ctx c0 x).
                   
          eapply occurs_free_app_bound_var.
          2: apply H4. constructor. auto.
          inv H. inv H12. specialize (H x).
          apply H. split.
          rewrite bound_var_app_ctx. left; auto.
          inv H5.
          eapply name_boundvar_arg. apply H8.
          rewrite find_get_fun in H3. apply H3.
          eapply bv_in_find_def. 
          rewrite find_get_fun in H3. apply H3.
          auto.
      }
      inv H. auto.
      apply Disjoint_sym.
      eapply Disjoint_Included_l.
      2: eapply Disjoint_Included_r.
      3: apply H2.
      rewrite occurs_free_Efun. left; auto.
      rewrite bound_var_Efun. right. apply bound_var_app_ctx. left; auto.
      inv H. eapply Disjoint_Included_l.
      2: apply H8.
      intro. intros. apply bound_var_app_ctx.
      left; auto.
      inv H.
      eapply ub_find_def_nodup; eauto.
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

Theorem ub_fun_inlining: forall B1   xs fb B2 c f t vs c',
  unique_bindings (c' |[ Efun (fundefs_append B1 (Fcons f t xs fb B2)) (c |[ Eapp f t vs ]|) ]|)  ->
  unique_bindings (c' |[ Efun (fundefs_append B1 B2) (c |[ (rename_all (set_list (combine xs vs) (M.empty var)) fb) ]|) ]|).
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

  apply unique_bindings_rename_all.
  simpl in H0. inv H0.
  eapply fundefs_append_unique_bindings_l in H7. 2: reflexivity. destructAll.
  inv H4. auto.
  
  simpl. rewrite bound_var_Fun1_c.
  rewrite <- (proj1 bound_var_rename_all).
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
  left; right; right; right; left. rewrite <- (proj1 bound_var_rename_all) in H4.  auto. 
Qed.

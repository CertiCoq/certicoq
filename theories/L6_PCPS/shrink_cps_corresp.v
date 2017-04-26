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
Require Import L6.cps_util L6.List_util L6.shrink_cps L6.eval L6.set_util L6.identifiers  L6.stemctx.
Require Import L6.shrink_cps_correct.





Ltac pi0 :=
  repeat match goal with
           | [ H: _ + _ = 0 |- _ ] =>  apply plus_is_O in H; destruct H; subst; pi0
           | [ H: 0 = _ + _ |- _ ] => symmetry in H; pi0
           | [ H: (if cps_util.var_dec ?X ?Y then _ else _) = 0 |- _] => destruct (cps_util.var_dec X Y); try inversion H; pi0                | [ H: ?X <> ?X |- _] => exfalso; apply H; auto
         end.

Notation "A =mgd0= B" := (map_getd_r _ 0 A B) (at level 80).
Notation "A =mg= B" := (map_get_r _ A B) (at level 81).




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

Notation c_plus := (fun v c => get_c v c + 1)%nat.
Notation c_minus := (fun v c => get_c v c - 1)%nat.

Section CENSUS.

  Definition c_count: exp -> c_map -> Prop :=
    fun e count => forall v, num_occur e v (get_c v count).


  Definition c_count_f: fundefs -> c_map -> Prop :=
    fun f count => forall v, num_occur_fds f v (get_c v count).

  Definition c_count_c: exp_ctx -> c_map -> Prop :=
    fun c count => forall v, num_occur_ec c v (get_c v count).

  Definition c_count_fdc: fundefs_ctx -> c_map -> Prop :=
    fun fdc count => forall v, num_occur_fdc fdc v (get_c v count).


  
  Definition init_census_f (f:fundefs) := update_census_f (M.empty var) f (fun v c =>
                                                                             get_c v c + 1)%nat (M.empty nat).

  Fixpoint f_opt_d {A} (d:A) f on om: option A :=
    match on with
      | Some n =>  (match om with
                      | Some m => Some (f n m)
                      | None => Some (f n d)
                    end)
      | None => match om with
                  | Some m => Some (f d m)
                  | None => None
                end
    end.


  Lemma gccombine:
    forall (x : M.elt) (x1 x0 : c_map) (n m: nat),
      get_c x x1 = n ->
      get_c x x0 = m ->
      get_c x (M.combine (f_opt_d 0 Init.Nat.add) x1 x0) = (n + m).
  Proof.
    unfold getd; intros. rewrite M.gcombine. destruct (M.get x x1); destruct (M.get x x0); simpl; subst; auto. reflexivity.
  Qed.          


  Lemma gccombine':
    forall (x : M.elt) (x1 x0 : c_map),
      get_c x (M.combine (f_opt_d 0 Init.Nat.add) x1 x0) = (get_c x x1 + get_c x x0).
  Proof.
    unfold getd; intros. rewrite M.gcombine. destruct (M.get x x1); destruct (M.get x x0); simpl; subst; auto. reflexivity.
  Qed.

  Lemma gccombine_sub:
    forall (x : M.elt) (x1 x0 : c_map),
      get_c x (M.combine (f_opt_d 0 Init.Nat.sub) x1 x0) = (get_c x x1 - get_c x x0 ).
  Proof.
    unfold getd; intros. rewrite M.gcombine. destruct (M.get x x1); destruct (M.get x x0); simpl; subst; auto. reflexivity.
  Qed.          



  Lemma proper_set_fun: forall f x y z,      
                          map_getd_r nat 0 x y ->
                          (forall c c' : Maps.PTree.t nat,
                             map_getd_r nat 0 c c' -> forall n0 : var, f n0 c = f n0 c') ->
                          map_getd_r nat 0 (M.set z (f z x) x)
                                     (M.set z (f z y) y).
  Proof.
    intro; intro; intros; intro.
    destruct (var_dec v z).
    subst.
    do 2 (rewrite gdss).  apply H0; auto.
    rewrite gdso. rewrite gdso. apply H. auto. auto.
  Qed.      



  Theorem proper_update_census_sig_list:
    forall {l} {f} {c} {sig sig'},
      map_get_r (Maps.PTree.elt) sig sig' ->
      update_census_list sig l f c = update_census_list sig' l f c.
  Proof.
    induction l; intros.
    reflexivity.
    simpl. assert (H' := H); specialize (H a). unfold apply_r.
    rewrite H.
    destruct (Maps.PTree.get a sig'); auto.
  Qed.


  
  Theorem proper_update_census_d_list:
    forall {l} {f} {sig},
      (forall c c', map_getd_r _ 0 c c' -> forall n, f n c = f n c') ->
      Proper (map_getd_r _ 0 ==> map_getd_r _ 0) (update_census_list sig l f).
  Proof.    
    induction l; intros.
    simpl. intro. intros. auto.
    intro. intros. simpl. apply IHl.  
    intro; intros. apply H; auto.
    intro. destruct (M.elt_eq v (apply_r sig a)).
    subst. rewrite gdss. rewrite gdss. apply H; auto.
    rewrite gdso by auto. rewrite gdso by auto. apply H0.
  Qed.

  (** Equivalent substitutions results in equivalent counts under update_census 
      Could be strengthened to live vars in e *)
  Theorem proper_update_census_sig: 
    (forall {e} {f} {c} {sig sig'},
       map_get_r (Maps.PTree.elt) sig sig' ->
       update_census sig e f c = update_census sig' e f c)
    /\
    (forall {fds} {f} {c} {sig sig'},
       map_get_r _ sig sig' ->
       update_census_f sig fds f c = update_census_f sig' fds f c).    
  Proof.
    eapply exp_def_mutual_ind; intros.
    - simpl. rewrite (proper_update_census_sig_list H0).
      apply H.
      auto.
    - simpl.      
      unfold apply_r.
      rewrite H. destruct (M.get v sig'); auto.
    - simpl.
      simpl in H0.
      erewrite H0.
      apply H; auto. auto.
    - simpl.
      rewrite (prop_apply_r _ _ _ H0).
      apply H.
      auto.
    - simpl.
      erewrite H.
      erewrite H0.
      reflexivity.
      auto.
      auto.
    - simpl. rewrite (prop_apply_r _ _ _ H). apply proper_update_census_sig_list.
      auto.
    - simpl. rewrite (proper_update_census_sig_list H0).
      apply H; auto.
    - simpl. rewrite (prop_apply_r _ _ _ H). reflexivity.
    - simpl. erewrite H; auto.
    - reflexivity.
  Qed.
  
  Theorem proper_update_census_d: forall f, 
                                    (forall c c', map_getd_r _ 0 c c' -> forall n, f n c = f n c') -> 
                                    (forall e sig, Proper (map_getd_r _ 0 ==> map_getd_r _ 0) (update_census sig e f))
                                    /\ (forall fds sig, Proper (map_getd_r _ 0 ==> map_getd_r _ 0) (update_census_f sig fds f)).
  Proof.
    intros f fhs;
    eapply exp_def_mutual_ind; intros; simpl.
    - intro. intros.
      apply H.
      apply proper_update_census_d_list; auto.
    - intro; intros.
      apply proper_set_fun; auto.
    - intro; intros.
      eapply H.
      simpl in H0. apply H0. auto.
    - intro; intros.
      apply H.
      revert fhs.
      revert H0.
      apply proper_set_fun.
    - intro. intros.
      apply H0.
      apply H. auto.
    - intro; intros.
      apply proper_update_census_d_list.
      auto.
      apply proper_set_fun; auto.
    - intro. intros.
      apply H. apply proper_update_census_d_list; auto.
    - intro; intros.
      apply proper_set_fun; auto.
    - intro; intros.
      apply H0.
      apply H.
      auto.
    - intro; intros. auto.
  Qed.


  
  
  Theorem proper_plus_census_d: forall e sig, Proper (map_getd_r _ 0 ==> map_getd_r _ 0) (update_census sig e c_plus).
  Proof.
    apply proper_update_census_d.
    intros.  rewrite H. reflexivity.
  Qed.

  Theorem proper_minus_census_d: forall e sig, Proper (map_getd_r _ 0 ==> map_getd_r _ 0) (update_census sig e c_minus).
  Proof.
    apply proper_update_census_d.
    intros. rewrite H; auto.
  Qed.


  Theorem init_census_f_ar_l: forall f l sig c,
                                map_getd_r _ 0 (update_census_list (M.empty var) (apply_r_list sig l) f c) (update_census_list sig l f c). 
  Proof.
    induction l; intros.
    - intro. simpl. reflexivity.
    - simpl. rewrite apply_r_empty.
      apply IHl.
  Qed.

  (** update_census sig on m produces the same count as update_census (empty) on (sig m)  *)
  (* TODO: change name*)
  Theorem init_census_f_ar:
    forall f,       (forall c c', map_getd_r _ 0 c c' -> forall n, f n c = f n c') -> 

                    (forall m sig c,
                       map_getd_r _ 0 (update_census (M.empty var) (rename_all_ns sig m) f c) (update_census sig m f c)) /\
                    (forall m sig c,
                       map_getd_r _ 0 (update_census_f (M.empty var) (rename_all_fun_ns sig m) f c) (update_census_f sig m f c)).
  Proof.
    intros f Hf;
    eapply exp_def_mutual_ind; intros.
    -  simpl.
       intro. rewrite <- H.
       apply proper_update_census_d.
       auto.
       apply init_census_f_ar_l.
    - simpl.
      rewrite apply_r_empty.
      apply smgd_refl.
    - simpl.
      intro. rewrite <- H.
      apply proper_update_census_d. auto.
      simpl in H0.
      apply H0.
    -  simpl.
       intro. rewrite <- H.
       apply proper_update_census_d.
       auto.
       rewrite apply_r_empty.
       apply smgd_refl.
    - simpl.
      intro.
      rewrite <- H0.
      apply proper_update_census_d. auto.
      apply H.
    - simpl. rewrite apply_r_empty.
      apply init_census_f_ar_l.
    - simpl.
      intro. rewrite <- H.
      apply proper_update_census_d.
      auto.
      apply init_census_f_ar_l.
    - simpl.
      rewrite apply_r_empty.
      apply smgd_refl.
    - simpl.    
      intro.
      rewrite H0.
      apply proper_update_census_d. auto.
      intro. rewrite <- H.
      auto.
    - simpl. apply smgd_refl.
  Qed.


  Theorem init_census_plus_ar:
    (forall m sig c,
       map_getd_r _ 0 (update_census (M.empty var) (rename_all_ns sig m) c_plus c) (update_census sig m c_plus c)).
  Proof.
    apply init_census_f_ar.
    intros.
    rewrite H. reflexivity.
  Qed.

  
  Theorem init_census_plus_ar_f: 
    (forall m sig c,
       map_getd_r _ 0 (update_census_f (M.empty var) (rename_all_fun_ns sig m) c_plus c) (update_census_f sig m c_plus c)).
  Proof.
    apply init_census_f_ar.
    intros.
    rewrite H.
    reflexivity.
  Qed.

  
  Theorem combine_plus_census_list: forall l count sig,
                                      map_getd_r _ 0 (M.combine (f_opt_d 0 plus)
                                                                count
                                                                (update_census_list (M.empty var) (apply_r_list sig l) c_plus (M.empty nat)))
                                                 (update_census_list sig l c_plus count).
  Proof.
    induction l; intros.
    - simpl. intro. rewrite gccombine'. rewrite gdempty. auto.
    - simpl. intro. rewrite gccombine'. rewrite <- IHl.
      simpl. rewrite gccombine'. rewrite apply_r_empty.
      rewrite gdempty. simpl.
      rewrite init_census_f_ar_l.
      rewrite <- IHl.
      rewrite gccombine'.
      destruct (var_dec v (apply_r sig a)).
      + subst. rewrite gdss. rewrite gdss.
        omega.      
      + rewrite gdso by auto.
        rewrite gdso by auto.
        rewrite gdempty. simpl. reflexivity.
  Qed.

  Theorem get_c_up : forall v v0 count,
                       get_c v0 (M.set v (get_c v count + 1) count) = get_c v0 count + get_c v0 (M.set v 1 (M.empty nat)).
  Proof.
    intros. destruct (var_dec v v0).
    - subst.
      rewrite gdss. rewrite gdss. reflexivity.
    - rewrite gdso by auto.
      rewrite gdso by auto.
      rewrite gdempty.
      rewrite <- plus_n_O.
      auto.
  Qed.

  (** update_census sig on m with c_plus adds the occurences of variables in (sig m) to their respective tally in count  *)
  Theorem combine_plus_census_correct: (forall  m count sig,
                                          map_getd_r _ 0 (M.combine (f_opt_d 0 plus) count (init_census (rename_all_ns sig m))) (update_census sig m c_plus count)) /\
                                       (forall f count sig,   map_getd_r _ 0 (M.combine (f_opt_d 0 plus) count (update_census_f (M.empty var) (rename_all_fun_ns sig f) c_plus (M.empty nat))) (update_census_f sig f c_plus count)).  
  Proof.
    eapply exp_def_mutual_ind; intros; simpl.
    - intro. rewrite gccombine'.
      rewrite <- H.
      rewrite gccombine'.
      unfold init_census.
      simpl.
      rewrite <- combine_plus_census_list.
      rewrite gccombine'.
      assert (Hfr := init_census_f_ar).
      destruct (Hfr c_plus). intros.  simpl. rewrite H0. auto.
      rewrite H0.
      rewrite <- H.
      rewrite gccombine'.
      simpl.
      unfold init_census.
      omega.
    - intro.
      rewrite gccombine'.
      unfold init_census.
      simpl.
      rewrite gdempty.
      rewrite plus_n_O.
      rewrite apply_r_empty.
      simpl.
      rewrite get_c_up.
      omega.
    - intro.
      rewrite gccombine'.
      unfold init_census.
      simpl.
      unfold init_census in H0. simpl in H0.
      rewrite init_census_plus_ar.
      symmetry.
      erewrite proper_plus_census_d.
      Focus 2. apply smgd_sym. apply H0.      
      rewrite <- H. 
      rewrite <- H.
      do 3 (rewrite gccombine').
      omega.      
    - unfold init_census.
      simpl. intro. rewrite gccombine'.
      rewrite <- H.
      rewrite gccombine'.
      rewrite init_census_plus_ar.
      rewrite <- H.
      rewrite gccombine'.
      rewrite apply_r_empty.
      rewrite get_c_up.
      rewrite gdempty.
      rewrite get_c_up. omega.
    - intro.
      rewrite gccombine'.
      unfold init_census. simpl.
      rewrite init_census_plus_ar.
      rewrite <- H0.
      rewrite gccombine'.
      symmetry.
      rewrite <- H0.
      rewrite gccombine'.
      rewrite <- H.
      rewrite gccombine'.
      omega.      
    - intro.
      rewrite gccombine'.
      rewrite <- combine_plus_census_list.
      rewrite gccombine'.
      unfold init_census. simpl.
      rewrite <- combine_plus_census_list.
      rewrite gccombine'.
      rewrite apply_r_empty.
      rewrite apply_r_list_empty.
      rewrite get_c_up.
      rewrite get_c_up. rewrite gdempty.
      omega.
    - intro.
      rewrite gccombine'.
      unfold init_census. simpl.
      rewrite <- H.
      rewrite gccombine'.
      rewrite init_census_plus_ar.
      rewrite <- H.
      rewrite gccombine'.
      symmetry.
      rewrite <- combine_plus_census_list.
      rewrite gccombine'.
      omega.
    - intro.
      rewrite gccombine'.
      rewrite get_c_up. unfold init_census. simpl. rewrite get_c_up. rewrite gdempty. rewrite apply_r_empty. omega.
    - intro; rewrite gccombine'.
      rewrite <- H0.
      rewrite gccombine'.
      rewrite init_census_plus_ar_f.
      rewrite <- H0.
      rewrite gccombine'.
      symmetry. rewrite <- H. rewrite gccombine'. unfold init_census.
      omega.
    - intro.     
      rewrite gccombine'.
      rewrite gdempty.
      rewrite plus_n_O. reflexivity.
  Qed.
  
  Theorem num_occur_constr:
  forall {e} {v} {n n'},
    num_occur e v n ->
    n = n' ->
    num_occur e v n'.
  Proof.
    intros; subst; auto.
  Qed.

  Theorem num_occur_fds_constr:
  forall {e} {v} {n n'},
    num_occur_fds e v n ->
    n = n' ->
    num_occur_fds e v n'.
  Proof.
    intros; subst; auto.
  Qed.
  


  Theorem update_census_list_correct: forall v sig l count,  
                                        getd 0 v (update_census_list sig l c_plus count) =
                                        getd 0 v count + num_occur_list (apply_r_list sig l) v. 
  Proof.
    induction l; intros.
    - simpl; omega.
    - simpl. rewrite IHl. destruct (cps_util.var_dec v (apply_r sig a)).
      + subst. rewrite gdss. omega.
      + rewrite gdso by auto.
        unfold get_c. unfold maps_util.getd.
        reflexivity.
  Qed.


  Theorem get_c_minus : forall v v0 count,
                          get_c v0 (M.set v (get_c v count - 1) count) = get_c v0 count - get_c v0 (M.set v 1 (M.empty nat)).
  Proof.
    intros. destruct (var_dec v v0).
    - subst.
      rewrite gdss. rewrite gdss. reflexivity.
    - rewrite gdso by auto.
      rewrite gdso by auto.
      rewrite gdempty.
      rewrite <- minus_n_O.
      auto.
  Qed.


  Theorem combine_minus_census_list: forall l count sig,
                                       map_getd_r _ 0 (M.combine (f_opt_d 0 minus)
                                                                 count
                                                                 (update_census_list (M.empty var) (apply_r_list sig l) c_plus (M.empty nat)))
                                                  (update_census_list sig l c_minus count).
  Proof.
    induction l; intros.
    - simpl. intro. rewrite gccombine_sub. rewrite gdempty. rewrite minus_n_O. auto.
    - simpl. intro. rewrite gccombine_sub. rewrite <- IHl.
      simpl. rewrite gccombine_sub. rewrite apply_r_empty.
      rewrite gdempty. simpl.
      rewrite init_census_f_ar_l.
      rewrite <- combine_plus_census_list.
      rewrite gccombine'.
      rewrite get_c_minus. omega.
  Qed.


  
  
  
  


End CENSUS.





Fixpoint inlined_fundefs_f (fds:fundefs) (i:b_map): fundefs :=
  match fds with
    | Fnil => Fnil
    | Fcons f t ys e fds' =>
      match get_b f i with
        | true => inlined_fundefs_f fds' i
        | false => Fcons f t ys e (inlined_fundefs_f fds' i)
      end
  end.

Theorem inlined_fundefs_append: forall B2 im B1,
                                  inlined_fundefs_f (fundefs_append B1 B2) im =
                                  fundefs_append (inlined_fundefs_f B1 im) (inlined_fundefs_f B2 im). 
Proof.
  induction B1; intros; simpl; auto.
  destruct (get_b v im); auto.
  rewrite IHB1.
  simpl. reflexivity.
Qed.

(** Only functions which are on the stem are considered *)
Fixpoint inlined_ctx_f (c:exp_ctx) (i:b_map): exp_ctx :=
  match c with 
    | Hole_c => Hole_c
    | Econstr_c x t ys c => Econstr_c x t ys (inlined_ctx_f c i)
    | Eproj_c x t n y c => Eproj_c x t n y (inlined_ctx_f c i)
    | Ecase_c x te t c te' =>
      Ecase_c x te t (inlined_ctx_f c i) te'
    | Eprim_c x f ys c => Eprim_c x f ys (inlined_ctx_f c i) 
    | Efun1_c fds c => Efun1_c (inlined_fundefs_f fds i) (inlined_ctx_f c i) 
    | Efun2_c cfds e' => Efun2_c (inlined_fundefs_ctx_f cfds i) e'
  end
with inlined_fundefs_ctx_f (cfds: fundefs_ctx) (im:b_map): fundefs_ctx :=
       match cfds with
         | Fcons1_c f t ys c fds =>
           Fcons1_c f t ys (inlined_ctx_f c im) fds
         | Fcons2_c f t ys e' cfds =>
           Fcons2_c f t ys e' (inlined_fundefs_ctx_f cfds im)
       end
.


(* collect the names of functions in a term e  which could be affected by inlined_ctx *)
Inductive fun_names : exp -> Ensemble var :=
| Fun_Econstr :
    forall y x t ys e,
      fun_names e y ->
      fun_names (Econstr x t ys e) y
| Fun_Eproj :
    forall y x tau n y' e,
      fun_names e y ->
      fun_names (Eproj x tau n y' e) y
| Fun_Ecase :
    forall x y c e B,
      fun_names e y ->
      List.In (c, e) B ->
      fun_names (Ecase x B) y
| Fun_Efun1 :
    forall y defs e,
      fun_names_fundefs defs y ->
      fun_names (Efun defs e) y
| Fun_Efun2 :
    forall y defs e,
      fun_names e y ->
      fun_names (Efun defs e) y
| Fun_Eprim :
    forall y x p ys e,
      fun_names e y ->
      fun_names (Eprim x p ys e) y
with fun_names_fundefs : fundefs -> Ensemble var :=
     | Fun_Fcons1 :
         forall f tau ys e defs,
           fun_names_fundefs (Fcons f tau ys e defs) f
     | Fun_Fcons2 :
         forall x f tau ys e defs,
           fun_names_fundefs defs x ->
           fun_names_fundefs (Fcons f tau ys e defs) x
     | Fun_Fcons3 :
         forall x f tau ys e defs,
           fun_names e x ->
           fun_names_fundefs (Fcons f tau ys e defs) x.


Inductive fun_names_ctx: exp_ctx -> Ensemble var  :=
| Fun_Constr_c: forall c v v' t ys,
                  fun_names_ctx c v ->
                  fun_names_ctx (Econstr_c v' t ys c) v
| Fun_Proj_c: forall  t n r c v' v,
                fun_names_ctx c v' ->
                fun_names_ctx (Eproj_c v t n r c) v'
| Fun_Prim_c: forall  t r c v' v,
                fun_names_ctx c v' ->
                fun_names_ctx (Eprim_c v t r c) v'
| Fun_Case1_c: forall v v' lce t c lce',
                 fun_names_ctx c v' ->
                 fun_names_ctx (Ecase_c v lce t c lce') v'
| Fun_Case2_c: forall v v' e lce t' t c lce',
                 fun_names e v' ->
                 List.In (t',e) lce ->
                 fun_names_ctx (Ecase_c v lce t c lce') v'
| Fun_Case3_c: forall v v' e lce t' t c lce',
                 fun_names e v' ->
                 List.In (t',e) lce' ->
                 fun_names_ctx (Ecase_c v lce t c lce') v'
| Fun_Fun11_c: forall fds v c,
                 fun_names_fundefs fds v ->
                 fun_names_ctx (Efun1_c fds c) v
| Fun_Fun12_c: forall fds v c,
                 fun_names_ctx c v ->
                 fun_names_ctx (Efun1_c fds c) v
| Fun_Fun21_c: forall cfds v e,
                 fun_names_fundefs_ctx cfds v ->
                 fun_names_ctx (Efun2_c cfds e) v
| Fun_Fun22_c: forall cfds v e,
                 fun_names e v ->
                 fun_names_ctx (Efun2_c cfds e) v
with fun_names_fundefs_ctx: fundefs_ctx -> Ensemble var :=
     | Fun_Fcons11_c: forall f t xs c fds, 
                        fun_names_fundefs_ctx (Fcons1_c f t xs c fds) f
     | Fun_Fcons13_c: forall f t xs c fds v,
                        fun_names_ctx c v ->
                        fun_names_fundefs_ctx (Fcons1_c f t xs c fds) v
     | Fun_Fcons14_c: forall f t xs c fds v,
                        fun_names_fundefs fds v ->
                        fun_names_fundefs_ctx (Fcons1_c f t xs c fds) v

     | Fun_Fcons21_c: forall f t xs e cfds, 
                        fun_names_fundefs_ctx (Fcons2_c f t xs e cfds) f
     | Fun_Fcons23_c: forall f t xs e cfds v,
                        fun_names e v ->
                        fun_names_fundefs_ctx (Fcons2_c f t xs e cfds) v
     | Fun_Fcons24_c: forall f t xs e cfds v,
                        fun_names_fundefs_ctx cfds v ->
                        fun_names_fundefs_ctx (Fcons2_c f t xs e cfds) v.



Definition eq_b_map_P:  Ensemble var -> b_map -> b_map -> Prop :=
  fun S rho1 rho2 =>
    forall x, S x -> get_b x rho1 = get_b x rho2.


Theorem eq_b_map_P_mon:
  forall S S' b1 b2,
    eq_b_map_P S' b1 b2 ->
    Included _ S S' ->
    eq_b_map_P S b1 b2.
Proof.
  intros.
  intro; intros.
  apply H0 in H1. apply H in H1. auto.
Qed.

Theorem  eq_b_inlined_fundefs: forall b1 b2 fds,
                                 eq_b_map_P (name_in_fundefs fds) b1 b2 -> 
                                 inlined_fundefs_f fds b1 = inlined_fundefs_f fds b2.
Proof.
  induction fds; intros.
  - simpl in *.
    assert ( eq_b_map_P (name_in_fundefs fds) b1 b2 ).
    eapply eq_b_map_P_mon; eauto with Ensembles_DB.
    specialize (IHfds H0).      
    destruct (get_b v b1) eqn:gbv1.
    rewrite H in gbv1.
    rewrite gbv1.
    apply IHfds.
    left; auto.
    rewrite H in gbv1.
    rewrite gbv1.
    rewrite IHfds.
    auto.
    left; auto.
  - auto.
Qed.




Definition Dom_map_b im: Ensemble var :=
  fun x => get_b x im = true.

(** inlined_ctx_f distributes over context composition *)
Theorem inlined_comp_ctx: (forall c1 c2 im,  
                             inlined_ctx_f (comp_ctx_f c1 c2) im = comp_ctx_f (inlined_ctx_f c1 im) (inlined_ctx_f c2 im))
                          /\
                          (forall f c2 im, (inlined_fundefs_ctx_f (comp_f_ctx_f f c2) im)  =
                                           (comp_f_ctx_f (inlined_fundefs_ctx_f f im) (inlined_ctx_f c2 im)))
.
Proof.
  exp_fundefs_ctx_induction IHc1 IHf; intros; simpl; auto; try (    rewrite IHc1; reflexivity).
  rewrite IHf. reflexivity.
  rewrite IHf. reflexivity.
Qed.


Theorem Disjoint_inlined_fds':
  forall fds im,
    Disjoint _ (name_in_fundefs fds) (Dom_map_b im) ->
    inlined_fundefs_f fds im = fds.
Proof.
  induction fds; intros.
  - simpl in H.  
    simpl.
    destruct (get_b v im) eqn:bvm.
    + exfalso.
      inv H. specialize (H0 v).
      apply H0; split; auto.
    + rewrite IHfds.
      reflexivity.
      eapply Disjoint_Included_l.
      2: apply H.
      eauto with Ensembles_DB.
  - reflexivity.
Qed.     

(* OS: use Disjoint_inlined_fds' instead *)
Theorem Disjoint_inlined_fds:
  forall fds im,
    Disjoint _ (bound_var_fundefs fds) (Dom_map_b im) ->
    inlined_fundefs_f fds im = fds.
Proof.
  intros.
  apply Disjoint_inlined_fds'.
  eapply Disjoint_Included_l.
  apply name_in_fundefs_bound_var_fundefs.
  auto.
Qed.     


Theorem Disjoint_inlined_ctx_mut:
  forall im,
    (forall c,
       Disjoint _ (bound_var_ctx c) (Dom_map_b im) ->
       inlined_ctx_f c im = c) /\
    (forall fc,
       Disjoint _ (bound_var_fundefs_ctx fc) (Dom_map_b im) ->
       inlined_fundefs_ctx_f fc im = fc).
Proof.
  intro im.
  exp_fundefs_ctx_induction IHc IHf; simpl; intros; try (rewrite IHc); try (rewrite IHf); auto.
  - eapply Disjoint_Included_l.
    2: apply H.
    rewrite bound_var_Econstr_c.
    left; auto.
  - eapply Disjoint_Included_l.
    2: apply H.
    rewrite bound_var_Eproj_c.
    left; auto.
  - eapply Disjoint_Included_l.
    2: apply H.
    rewrite bound_var_Eprim_c.
    left; auto.
  - eapply Disjoint_Included_l.
    2: apply H.
    intro; intro.
    apply Bound_Case1_c. auto.
  - rewrite Disjoint_inlined_fds.
    reflexivity.
    eapply Disjoint_Included_l.
    2: apply H.      
    rewrite bound_var_Fun1_c.
    left; auto.
  - eapply Disjoint_Included_l.
    2: apply H.      
    rewrite bound_var_Fun1_c.
    right; auto.
  - eapply Disjoint_Included_l.
    2: apply H.
    rewrite bound_var_Fun2_c.
    left; auto.
  - eapply Disjoint_Included_l.
    2: apply H.
    rewrite bound_var_Fcons1_c.
    right; right; left; auto.
  - eapply Disjoint_Included_l.
    2: apply H.
    rewrite bound_var_Fcons2_c.
    right; right; right; auto.
Qed.


Theorem Disjoint_inlined_ctx:
  (forall c im,
     Disjoint _ (bound_var_ctx c) (Dom_map_b im) ->
     inlined_ctx_f c im = c).
Proof.
  intros.
  apply Disjoint_inlined_ctx_mut.
  auto.
Qed.


Section CONTRACT.

  (** The domain of inl represents inlined functions in the context. 
      The function and its arguments should no longer be bound in the term *)
  Definition inl_inv (im:b_map) (sub:ctx_map) (e:exp):Prop :=
    forall f, get_b f im = true ->
              ~ (bound_var e f) /\
              (forall t xs m, M.get f sub = Some (SVfun t xs m) ->
                              Disjoint _ (bound_var e) (FromList xs)).

  (** cmap is a correct approximation of the context w.r.t. constructors and functions on the stem *)
  Definition cmap_view_ctx sub c: Prop :=
    (forall x t xs,
       M.get x sub = Some (SVconstr t xs) <->
       exists c' c'',
         c = comp_ctx_f c' (Econstr_c x t xs c'')) /\
    (forall f t ys e,
       M.get f sub = Some (SVfun t ys e) <->
       exists c' c'' B1 B2,
         c = comp_ctx_f c' (Efun1_c
                              (fundefs_append B1 (Fcons f t ys e B2)) c'')).

  Theorem empty_view_hole:
    cmap_view_ctx (M.empty _) (Hole_c).
  Proof.
    split; split; intros.
    - rewrite M.gempty in H. inv H.
    - destructAll.
      exfalso.
      destruct x0; inv H.
    - rewrite M.gempty in H. inv H.
    - destructAll.
      exfalso.
      destruct x; inv H.
  Qed.




  







  Theorem num_occur_case_le :
    forall x v e m cl,
      List.In (v, e) cl ->
      forall n,
        num_occur_case cl x n ->
        num_occur e x m ->
        m <= n.
  Proof.
    induction cl; intros.
    inv H.
    inv H.
    + inv H0. assert (m = n0).
      eapply (proj1 (num_occur_det _)); eauto. 
      omega.
    + inv H0.
      specialize (IHcl H2 _ H7 H1).
      omega.
  Qed.
  
  (* equivalent to c_nozombie in aj  *)
  Definition no_zombie e1 e2: Prop :=
    Included _ (dead_var e1) (dead_var e2).



  Theorem gsr_no_zombie:
    forall e1 e2,
      gen_sr_rw  e1 e2 ->
      no_zombie e1 e2.
  Proof.
    intros. inv H. inv H0; intro; 
                   intros;
                   apply num_occur_app_ctx in H0; destructAll; pi0; inv H1; pi0.
    -  apply num_occur_app_ctx. eexists; eauto.
    -  apply num_occur_app_ctx. eexists; eauto.
    -  apply num_occur_app_ctx. eexists; eauto.
    -  apply num_occur_app_ctx. eexists; eauto.
    -  apply fundefs_append_num_occur' in H7. destructAll; pi0.
       inv H2; pi0.
       apply num_occur_app_ctx. eexists 0, 0; eauto.
       split; auto. split; auto.
       rewrite <- plus_0_l.
       constructor; auto.
       rewrite <- plus_0_l.
       eapply fundefs_append_num_occur; eauto.
    - apply num_occur_app_ctx in H7; destructAll; pi0.
      apply num_occur_app_ctx. eexists 0, 0; eauto.
      split; auto. split.
      eapply num_occur_n. constructor.
      apply num_occur_app_ctx. eexists 0, 0; eauto.
      split; auto. split; auto.
      inv H3. rewrite H8.
      apply findtag_In in H.
      pi0.
      assert (exists n, num_occur e0 x0 n) by apply e_num_occur.
      destruct H4.
      assert (x1 <= 0).
      eapply num_occur_case_le; eauto.
      apply le_n_0_eq in H5. subst; auto.
      omega. auto.
    - apply num_occur_app_ctx in H7; destructAll; pi0.
      inv H3; pi0.
      apply num_occur_app_ctx. exists 0, 0; eauto. split; auto.
      split; auto.
      eapply num_occur_n. constructor. apply num_occur_app_ctx.
      exists 0, 0; split; auto. split.
      assert (exists n,  num_occur  (rename_all_ns (M.set v k (M.empty var)) e0) x0 n) by apply e_num_occur.
      destruct H4.
      assert (x1 <= 0).
      eapply num_occur_rename_all_ns_not_range. apply H10.
      apply H4.
      intro. inv H5.
      destruct (var_dec x2 v).
      subst. rewrite M.gss in H6. inv H6.
      apply nthN_In in H.
      apply not_occur_list_not_in in H2.
      auto.
      rewrite M.gso in H6; auto. rewrite M.gempty in H6.
      inv H6.
      apply le_n_0_eq in H5; subst; auto.

      reflexivity. auto.
    - inv H2; pi0.
      apply num_occur_app_ctx in H9. destructAll; pi0.
      inv H2; pi0.
      eapply fundefs_append_num_occur' in H10.
      destructAll; pi0.
      inv H4; pi0.
      eapply num_occur_app_ctx. exists 0, 0; split; auto.
      split; auto.
      eapply num_occur_n. constructor.
      apply num_occur_app_ctx. exists 0, 0; split; auto.
      split.
      assert (exists n,  num_occur (rename_all_ns (set_list (combine xs vs) (M.empty var)) fb) x n) by apply e_num_occur.
      destruct H4.
      assert (x0 <= 0).
      eapply num_occur_rename_all_ns_not_range.
      apply H15. apply H4. intro.
      apply Range_map_setlist in H6.
      apply not_occur_list in H3. auto.
      apply le_n_0_eq in H6. subst; auto.
      reflexivity.
      eapply fundefs_append_num_occur; eauto.
      auto.
  Qed.

  (** If a variable is dead in a term, it will be dead in any shrink rewrites of the term *)
  Corollary shrink_no_zombie:
    forall e1 e2,
      gsr_clos  e1 e2 ->
      no_zombie e1 e2.
  Proof.
    intros. induction H.
    - apply gsr_no_zombie in H; auto.
    - intro. auto with Ensembles_DB. 
    - eapply Included_trans; eauto.
  Qed.

  
  (* This is implied by sig_inv_dom in the case where e is also closed.
   *) 
  Definition sig_inv sig e: Prop := 
    forall x y, M.get x sig = Some y ->
                (* dom *) ~ (bound_var e x) /\
                          (* codom *)
                          (num_occur e y  0 \/ bound_var e y).


  (* Strengthening of sig_inv. Need the bound_stem_ctx due to function inlining  *)
  Definition sig_inv_full sig c e: Prop := 
    forall x y, M.get x sig = Some y ->
                (* dom *) ~ (bound_var (c |[e]|) x) /\
                          (* codom *)
                          (num_occur (c |[e ]|) y  0 \/ bound_stem_ctx c y).


  Definition sig_inv_codom sig c e: Prop :=
    forall x y, M.get x sig = Some y ->
                (num_occur (c |[e ]|) y  0 \/ bound_stem_ctx c y).



  Theorem sig_inv_full_push: forall sig c c' e,
                               sig_inv_full sig c (c' |[ e ]|) ->
                               sig_inv_full sig (comp_ctx_f c c') e. 
  Proof.
    intros. intro. intros. apply H in H0.
    destruct H0.
    rewrite app_ctx_f_fuse in H0.
    rewrite app_ctx_f_fuse in H1.
    split; auto.
    inv H1. auto.
    right.
    apply bound_stem_comp_ctx_mut.
    auto.
  Qed.

  Theorem sig_inv_full_dead_l:
    forall c c' e sig,
      sig_inv_full sig c (c' |[ e ]|) ->
      sig_inv_full sig c e.
  Proof.
    intros. intro. intros. apply H in H0. destruct H0. split.
    - intro. apply H0. apply bound_var_app_ctx in H2.
      apply bound_var_app_ctx.
      inv H2. auto.
      right;           apply bound_var_app_ctx; auto.
    - inv H1.
      apply num_occur_app_ctx in H2; destructAll; pi0.
      apply num_occur_app_ctx in H2; destructAll; pi0.
      left. apply num_occur_app_ctx. exists 0, 0; auto.
      auto.
  Qed.
  

  Theorem   not_occur_rename_fun_not_dom :
    forall (sig : M.t var) (v : M.elt) (e : fundefs),
      ~ Dom_map sig v -> num_occur_fds (rename_all_fun_ns sig e) v 0 -> num_occur_fds e v 0.
  Proof.
    intros.
    assert (exists n, num_occur_fds e v n) by apply e_num_occur_fds.
    destruct H1.
    assert (x <= 0).
    eapply num_occur_rename_all_not_dom_mut.
    apply H1. apply H0. auto.
    apply le_n_0_eq in H2. subst; auto.
  Qed.

  
  (* meaning either get_c y count 0 OR y is bound on the way to the hole [or, weaker, bound somewhere in the term, which is enough to show that Disjoint Dom Codom *)
  Theorem not_free_bound_or_not_occur :
    forall v : var,
      (forall e : exp,  ~ occurs_free e v -> num_occur e v 0  \/ bound_var e v) /\
      (forall f : fundefs, ~ occurs_free_fundefs f v ->  num_occur_fds f v 0 \/ bound_var_fundefs f v).
  Proof.
    intro v.
    apply exp_def_mutual_ind; intros.
    - destruct (var_dec v0 v).
      + right. subst.
        constructor.
      + assert (~ List.In v l).
        intro; apply H0.
        constructor; auto.
        assert (~ (occurs_free e) v).
        intro; apply H0.
        constructor 2; auto.
        apply H in H2. inv H2.
        left.
        apply not_occur_list_not_in in H1.
        eapply num_occur_n. constructor.
        apply H3.
        rewrite H1. auto.
        right.
        apply bound_var_Econstr.
        left; auto.
    - left.
      eapply num_occur_n.
      constructor.
      constructor.
      simpl.
      destruct (cps_util.var_dec v v0).
      exfalso; apply H.
      subst. constructor.
      auto.
    - assert (~occurs_free e v).
      intro; apply H1.
      constructor. auto.
      assert (~ occurs_free (Ecase v0 l) v).
      intro; apply H1.
      apply Free_Ecase3. auto.
      apply H in H2.
      apply H0 in H3.
      inv H2.
      inv H3.
      left.
      inv H2. rewrite H8.
      eapply num_occur_n.
      constructor. constructor.
      apply H4. apply H7.
      simpl. destruct (cps_util.var_dec v v0).
      inv H8.
      auto.
      right.
      apply bound_var_Ecase_cons. right; auto.
      right. apply bound_var_Ecase_cons. auto.
    - destruct (var_dec v0 v).
      right; subst; constructor.
      assert (~ occurs_free e v).
      intro; apply H0.
      constructor. auto. auto.
      apply H in H1.
      destruct H1. left.
      eapply num_occur_n.
      constructor; eauto.
      simpl.
      destruct (cps_util.var_dec v v1).
      exfalso; apply H0; subst; constructor.
      auto.
      right; auto.
    - assert ( ~ occurs_free_fundefs f2 v).
      intro.
      apply H1.        
      apply Free_Efun2. auto.
      assert (Hf2 := Decidable_name_in_fundefs f2).
      destruct Hf2.
      specialize (Dec v).
      destruct Dec.
      + right. constructor. apply name_in_fundefs_bound_var_fundefs. auto.
      + assert (~ occurs_free e v).
        intro.
        apply H1.
        constructor; auto.
        apply H0 in H4.
        apply H in H2.
        inv H4.
        inv H2.
        left.
        eapply num_occur_n. constructor; eauto. auto.
        right; auto.
        right; auto.
    - left.
      eapply num_occur_n. constructor.
      simpl.
      destruct (cps_util.var_dec v v0).
      exfalso; apply H; subst; auto.
      apply not_occur_list_not_in.
      intro; apply H.
      constructor.
      auto.
    - destruct (var_dec v0 v).
      + right. subst.
        constructor.
      + assert (~ List.In v l).
        intro; apply H0.
        constructor; auto.
        assert (~ (occurs_free e) v).
        intro; apply H0.
        apply Free_Eprim2; auto.
        apply H in H2.  inv H2.
        left.
        apply not_occur_list_not_in in H1.
        eapply num_occur_n. constructor.
        apply H3.
        rewrite H1. auto.
        right.
        apply bound_var_Eprim.
        left; auto.
    - left.
      eapply num_occur_n.
      constructor.
      simpl.
      destruct (cps_util.var_dec v v0).
      exfalso; apply H; subst; auto.
      auto.
    - destruct (var_dec v0 v).
      right; subst; auto.
      assert (Hl := Decidable_FromList l).
      inv Hl. specialize (Dec v). inv Dec.
      right.
      constructor. right; auto.
      assert (Hf5 := Decidable_name_in_fundefs f5).
      destruct Hf5; specialize (Dec v); inv Dec.
      right. constructor 2. apply name_in_fundefs_bound_var_fundefs. auto.
      assert (~ occurs_free e v).
      intro; apply H1.
      constructor; auto.
      apply H in H4.
      assert (~ occurs_free_fundefs f5 v).
      intro; apply H1.
      constructor 2; auto.
      apply H0 in H5.
      destruct H4.
      destruct H5.
      left.
      eapply num_occur_fds_n.
      constructor; eauto. auto.
      right.
      constructor 2. auto.
      right. auto.
    - left; constructor.
  Qed.



  
  
  
  
  Theorem Disjoint_apply_r: forall sig x,
                              Disjoint _ (Dom_map sig) (Singleton _ x) ->
                              apply_r sig x = x.
  Proof.
    intros.
    unfold apply_r.
    destruct (M.get x sig) eqn:gxs.
    exfalso; inv H. specialize (H0 x).
    apply H0.
    split; auto. exists e. auto.
    auto.
  Qed.      
  
  Theorem Disjoint_apply_r_FromList: forall sig l,
                                       Disjoint _ (Dom_map sig) (FromList l) ->
                                       apply_r_list sig l = l. 
  Proof.
    induction l; intros.
    - auto.
    - simpl. rewrite IHl.
      rewrite Disjoint_apply_r.
      auto.
      eapply Disjoint_Included_r.
      2: apply H. rewrite FromList_cons; auto with Ensembles_DB.
      eapply Disjoint_Included_r.
      2: apply H. rewrite FromList_cons; auto with Ensembles_DB.
  Qed.        

  Theorem Disjoint_Setminus_swap:
    forall {A} s1 s2 s3,
      Disjoint A (Setminus _ s1 s2) s3 <-> Disjoint A s1 (Setminus _ s3 s2).
  Proof.
    intros. split; intro.
    - split; intro; intro.
      inv H. specialize (H1 x).
      apply H1.
      inv H0.
      inv H2.
      split;
        eauto with Ensembles_DB.
      split; auto.
    - split; intro; intro.
      inv H.
      inv H0.
      specialize (H1 x).
      inv H.
      apply H1. split.
      auto.
      split; auto.
  Qed.

  
  
  Theorem Disjoint_Dom_map_funs: forall f2 sig s,
                                   
                                   Disjoint _ (Dom_map sig) (Setminus _ s (name_in_fundefs f2)) -> 
                                   
                                   Disjoint M.elt (Dom_map (remove_all sig (all_fun_name f2))) s.
  Proof.
    intros.
    rewrite Dom_map_remove_all.
    apply Disjoint_Setminus_swap.
    rewrite same_name_in_fun in H.
    auto.
  Qed.

  
  
  Theorem Disjoint_dom_rename_all:
    (forall  e sig,
       Disjoint _ (Dom_map sig) (occurs_free e) ->
       rename_all sig e = e) /\
    (forall f sig,
       Disjoint _ (Dom_map sig) (Union _ (occurs_free_fundefs f) (name_in_fundefs f)) ->
       rename_all_fun sig f = f).
  Proof.
    apply exp_def_mutual_ind; intros; repeat normalize_occurs_free_in_ctx; simpl.
    - rewrite H.
      rewrite Disjoint_apply_r_FromList.
      reflexivity.        
      eapply Disjoint_Included_r.
      2: apply H0. auto with Ensembles_DB.
      rewrite Dom_map_remove.
      split.
      intros. intro.
      inv H1.
      destruct (var_dec v x). subst.
      inv H2. apply H4. auto.
      inv H0. specialize (H1 x).
      apply H1. split.
      apply H2.
      right.
      split; auto.
      intro; apply n.
      inv H0. auto.
    - rewrite Disjoint_apply_r; auto.
    - assert ( Disjoint M.elt (Dom_map sig) (occurs_free (Ecase v l)) ).
      eauto with Ensembles_DB.
      apply H0 in H2.
      simpl in H2.
      inversion H2.
      rewrite  H4.
      rewrite H4.
      rewrite H5.
      rewrite H5.
      rewrite H; auto with Ensembles_DB.        
    - rewrite Disjoint_apply_r.
      rewrite H; auto.
      rewrite Dom_map_remove.
      rewrite Disjoint_Setminus_swap.
      eapply Disjoint_Included_r.
      2: apply H0.
      right; auto.
      eapply Disjoint_Included_r.
      2: apply H0.
      left; auto.
    -  rewrite H.
       rewrite H0.
       auto.         
       apply Disjoint_Dom_map_funs.
       auto with Ensembles_DB.
       apply Disjoint_Dom_map_funs.
       eapply Disjoint_Included_r.
       2: apply H1. eauto with Ensembles_DB.
    - rewrite Disjoint_apply_r.
      rewrite Disjoint_apply_r_FromList.
      auto.
      eauto with Ensembles_DB.
      eauto with Ensembles_DB.
    - rewrite Disjoint_apply_r_FromList.
      rewrite H.
      auto.
      rewrite Dom_map_remove.
      rewrite Disjoint_Setminus_swap.
      auto with Ensembles_DB.
      auto with Ensembles_DB.
    - rewrite Disjoint_apply_r.
      auto.
      rewrite occurs_free_Ehalt in H.
      auto.
    -  rewrite H.
       rewrite H0.
       auto.
       { simpl in H1.
         split; intro; intro.
         inv H2.
         inv H1.
         specialize (H2 x).
         apply H2.
         destruct (var_dec x v).
         subst; auto.           
         inv H4.
         split. auto.
         left.
         right. split; auto. intro; apply n.
         inv H4; auto.
         split; auto.
       }         
       simpl in H1.
       rewrite Dom_map_remove_all.
       rewrite Disjoint_Setminus_swap.
       eapply Disjoint_Included_r.
       2: apply H1.
       intro.
       intro.
       assert (Hd := Decidable_name_in_fundefs f5).
       inv Hd.
       specialize (Dec x).
       inv Dec; 
         auto with Ensembles_DB.
       destruct (var_dec x v).
       right. subst; left; auto.
       left.
       inv H2.
       left.       
       split; auto.         
       intro.
       inv H2; auto.
       inv H6; auto.
       inv H6; auto.
    -                 reflexivity.
  Qed.

  

  
  
  (* split sig_inv into the comps *)
  Definition sig_inv_dom (sig:r_map) e: Prop := 
    forall x y, M.get x sig = Some y ->
                ~ (bound_var e x).



  Theorem sig_inv_combine:
    forall sig c e,
      sig_inv_dom sig (c |[e ]|) /\
      sig_inv_codom sig c e <->
      sig_inv_full sig c e.
  Proof.
    intros.
    split; intro; intros.
    - intro. intros.
      inv H.
      assert (H0' := H0).
      apply H1 in H0.
      apply H2 in H0'.
      auto.
    - split; intro; intros.
      + apply H in H0. inv H0; auto.
      + apply H in H0. inv H0; auto.
  Qed.


  
  Definition sig_inv_dom_fundefs (sig:r_map) fds: Prop := 
    forall x y, M.get x sig = Some y ->
                ~ (bound_var_fundefs fds x).


  Definition sig_inv_dead (sig:r_map) e :Prop :=
    forall x y, M.get x sig = Some y ->
                num_occur e x 0.

  Definition sig_inv_dead_fundefs (sig:r_map) f :Prop :=
    forall x y, M.get x sig = Some y ->
                num_occur_fds f x 0.

  

  Theorem sig_inv_implies_dom:
    forall sig e,
      sig_inv sig e ->
      sig_inv_dom sig e.
  Proof.
    intros. intro. intros.
    apply H in H0. destructAll; auto.
  Qed.



  
  

  Theorem inl_inv_mon:
    forall e' e im sub ,
      Included _ (bound_var e') (bound_var e) ->
      inl_inv im sub e ->
      inl_inv im sub e'.
  Proof.
    intros; intro; intros.
    apply H0 in H1; destructAll.
    split; intro; intros.
    - apply H1. apply H; auto.
    - apply H2 in H3.
      eapply Disjoint_Included_l.
      2: apply H3. auto.
  Qed.

  
  Theorem sig_inv_dom_mon:
    forall e' e sig,
      Included _ (bound_var e') (bound_var e) ->
      sig_inv_dom sig e ->
      sig_inv_dom sig e'.
  Proof.
    intros. intro; intros.
    apply H0 in H1.
    intro.
    apply H1.
    apply H. auto.
  Qed.

  Theorem sig_inv_dom_fundefs_antimon:
    forall fds' fds sig,
      Included _ (bound_var_fundefs fds') (bound_var_fundefs fds) ->
      sig_inv_dom_fundefs sig fds ->
      sig_inv_dom_fundefs sig fds'.
  Proof.
    intros. 
    intro; intros.
    apply H0 in H1.
    intro; apply H1.
    apply H; auto.
  Qed.
  
  Theorem bound_var_subterm_e:
    forall e e', 
      subterm_e e e' ->
      Included _ (bound_var e) (bound_var e').
  Proof.
    intros.
    induction H.
    inv H; repeat normalize_bound_var; eauto with Ensembles_DB.
    intro. intro.
    eapply Bound_Ecase; eauto.
    left.
    revert H H0.
    revert x0.
    induction fds; intros.
    rewrite bound_var_fundefs_Fcons.
    inv H0; auto.
    inv H0.            
    eapply Included_trans; eauto.
  Qed.


  Theorem dsubterm_num_occur:
    (forall {e' e} {x} {n m},
       dsubterm_e e e' ->
       num_occur e' x n ->
       num_occur e x m ->
       m <= n) /\
    (forall {f} {e} {x} {n m},
       dsubterm_fds_e e f ->
       num_occur_fds f x n ->
       num_occur e x m ->
       m <= n).
  Proof.      
    eapply exp_def_mutual_ind; intros.
    - inv H0; inv H1.
      assert (m = n0).
      eapply (proj1 (num_occur_det _)); eauto.
      omega.
    - inv H.
      inv H4.
    - inv H2.
      inv H8.
      inv H1.
      inv H5.
      + inv H1.
        assert (m = n).
        eapply (proj1 (num_occur_det _)); eauto.
        omega.
      + assert (m <=  num_occur_list [v] x + m0).
        eapply H0.
        eapply dsubterm_case.
        apply H1.
        constructor; auto.
        auto.
        omega.
    - inv H0; inv H1.
      assert (m = n1).
      eapply (proj1 (num_occur_det _)); eauto.
      omega.
    - inv H2.
      inv H1.
      specialize (H _ _ _ _ H5 H9 H3).
      omega.
      assert (n0 = m).
      eapply (proj1 (num_occur_det _)); eauto.
      omega.       
    - inv H.
    - inv H0; inv H1.
      assert (m = n0).
      eapply (proj1 (num_occur_det _)); eauto.
      omega.
    - inv H.
    - inv H2.
      inv H1.
      + assert (m = n0).
        eapply (proj1 (num_occur_det _)); eauto.
        omega.
      + specialize (H0 _ _ _ _ H5 H12 H3).
        omega.
    - inv H.
  Qed.

  Theorem subterm_num_occur:
    forall {e e'} {x} ,
      subterm_e e e' ->
      forall {n m},
        num_occur e x m ->
        num_occur e' x n ->
        m <= n.
  Proof.
    intros e e' x H.
    induction H.
    - intros.
      eapply (proj1 dsubterm_num_occur); eauto.
    - intros.
      assert (exists z, num_occur y x z).
      eapply e_num_occur. inv H3.
      specialize (IHclos_trans1 _ _ H1 H4).
      specialize (IHclos_trans2 _ _ H4 H2).
      omega.
  Qed.


  Theorem subterm_sig_dead:
    forall {e e'},
      subterm_e e e' ->
      forall {sig}, 
        sig_inv_dead sig e' ->
        sig_inv_dead sig e.
  Proof.
    intros.
    intro. intros.
    apply H0 in H1.
    assert (exists y, num_occur e x y) by apply e_num_occur.
    inv H2.
    assert (x0 <= 0).
    eapply subterm_num_occur; eauto.
    apply le_n_0_eq in H2. subst; auto.
  Qed.


  Theorem rename_sig_dead:
    forall {sig} {e},
      sig_inv_dead sig e -> 
      rename_all sig e = e.
  Proof.
    intros.
    apply Disjoint_dom_rename_all.
    split. intro. intro.
    inv H0.
    inv H1. apply H in H0.
    revert H2.    
    apply not_occurs_not_free. auto.
  Qed.


  Theorem sig_inv_closed_dead:
    forall {sig} {e},
      sig_inv sig e ->
      closed e ->
      sig_inv_dead sig e.
  Proof.
    intros. intro. intros.
    apply H in H1.
    destructAll.
    assert (~ occurs_free e x).
    intro.
    apply H0 in H3. inv H3.
    apply not_free_bound_or_not_occur in H3.
    inv H3; auto.
    exfalso; auto.
  Qed.
  
  

  
  Theorem rename_all_no_shadow:
    forall sig,
      (forall e,
         sig_inv_dom sig e ->
         rename_all sig e = rename_all_ns sig e) /\
      (forall fds,
         sig_inv_dom_fundefs sig fds -> 
         rename_all_fun sig fds = rename_all_fun_ns sig fds)
  .         
  Proof.
    intros. split; intros; eapply Disjoint_dom_rename_all_eq; split; intro; intro;       inv H0; inv H1; apply H in H0; auto.
  Qed.

  Theorem rename_all_ns_empty: (forall e,
                                  e = rename_all_ns (M.empty var) e) /\
                               (forall fds, fds = rename_all_fun_ns (M.empty var) fds).
  Proof.
    split; intros.
    rewrite <- (proj1 (rename_all_no_shadow _)).
    apply rename_all_empty.
    intro. intros. rewrite M.gempty in H. inv H.
    rewrite <- (proj2 (rename_all_no_shadow _)).
    apply rename_all_empty.
    intro. intros. rewrite M.gempty in H. inv H.
  Qed.

  Theorem init_census_correct: (forall e, c_count e (init_census e)) /\
                               forall f, c_count_f f (init_census_f f). 
  Proof.  
    eapply exp_def_mutual_ind; intros; intro vv;
    assert (Hcpc := combine_plus_census_correct).
    - specialize (H vv).
      unfold init_census. simpl. 
      eapply num_occur_constr.
      constructor. eauto.
      destructAll.
      rewrite <- H0.
      rewrite gccombine'.
      rewrite update_census_list_correct.
      rewrite gdempty. rewrite apply_r_list_empty.
      rewrite <- (proj1 rename_all_ns_empty).
      omega.
    - unfold init_census.
      simpl.
      rewrite gdempty.
      rewrite apply_r_empty.
      eapply num_occur_constr.
      constructor. constructor.
      simpl. destruct (cps_util.var_dec vv v).
      subst.
      rewrite gdss. auto.
      rewrite gdso by auto.
      rewrite gdempty.
      auto.
    - unfold init_census; simpl.
      specialize (H0 vv).
      inversion H0; subst.
      eapply num_occur_constr.
      constructor. constructor; eauto.
      unfold init_census in H5.
      simpl.
      simpl in H5.
      rewrite apply_r_empty in *.
      destruct Hcpc.
      rewrite <- H1.
      rewrite gccombine'.
      rewrite <- H5.
      rewrite <- (proj1 rename_all_ns_empty).
      omega.
    - unfold init_census; simpl.
      eapply num_occur_constr.
      constructor. apply H.
      destruct Hcpc. rewrite <- H0.
      rewrite gccombine'.
      rewrite apply_r_empty.
      rewrite get_c_up. rewrite gdempty. rewrite <- (proj1 rename_all_ns_empty).
      simpl. destruct (cps_util.var_dec vv v0). subst; rewrite gdss. auto.
      rewrite gdso by auto.
      rewrite gdempty. auto.
    - unfold init_census; simpl.
      eapply num_occur_constr.
      constructor; auto.
      destruct Hcpc.
      rewrite <- H1. rewrite gccombine'.
      rewrite <- (proj1 rename_all_ns_empty).
      unfold init_census_f. apply plus_comm.
    - eapply num_occur_constr.
      constructor.
      unfold init_census. simpl.
      rewrite apply_r_empty.
      rewrite update_census_list_correct.
      rewrite apply_r_list_empty.
      destruct (cps_util.var_dec vv v).
      subst; rewrite gdss. rewrite gdempty. auto.
      rewrite gdso by auto. rewrite gdempty. auto.
    - unfold init_census; simpl. eapply num_occur_constr.
      constructor; auto.
      destruct Hcpc.
      rewrite <- H0.
      rewrite gccombine'.
      rewrite update_census_list_correct.
      rewrite <- (proj1 rename_all_ns_empty).
      rewrite apply_r_list_empty.
      rewrite gdempty.
      simpl.
      apply plus_comm.
    - unfold init_census.
      eapply num_occur_constr.
      constructor.
      simpl.
      rewrite gdempty.
      rewrite apply_r_empty.
      simpl.
      destruct (cps_util.var_dec vv v).
      subst; rewrite gdss. auto.
      rewrite gdso by auto.
      rewrite gdempty.
      auto.
    - unfold init_census_f; simpl.
      eapply num_occur_fds_constr.
      constructor; auto.
      destruct Hcpc.
      rewrite <- H2.
      rewrite gccombine'.
      rewrite <- (proj2 rename_all_ns_empty).
      auto.
    - unfold init_census_f. simpl. rewrite gdempty. constructor.
  Qed.

  
  (** dec_census removes the occurences of variables in (sig m) from their tally in count *)
  Theorem combine_minus_census_correct: (forall  m count sig,
                                           map_getd_r _ 0 (M.combine (f_opt_d 0 minus) count (init_census (rename_all_ns sig m))) (update_census sig m c_minus count)) /\
                                        (forall f count sig,   map_getd_r _ 0 (M.combine (f_opt_d 0 minus) count (update_census_f (M.empty var) (rename_all_fun_ns sig f) c_plus (M.empty nat))) (update_census_f sig f c_minus count)).  
  Proof.
    eapply exp_def_mutual_ind; intros; simpl.
    - intro. rewrite gccombine_sub.
      rewrite <- H.
      rewrite gccombine_sub.
      unfold init_census.
      simpl.
      rewrite <- combine_minus_census_list.
      rewrite gccombine_sub.
      assert (Hfr := init_census_f_ar).
      destruct (Hfr c_plus). intros.  simpl. rewrite H0. auto.
      rewrite H0.
      assert (Hcc := combine_plus_census_correct).
      destruct Hcc.
      rewrite <- H2.
      rewrite gccombine'.
      unfold init_census.
      omega.
    - intro.
      rewrite gccombine_sub.      
      unfold init_census.
      simpl.
      rewrite gdempty.
      simpl.
      rewrite apply_r_empty.
      rewrite get_c_minus.
      reflexivity.
    - intro.
      rewrite gccombine_sub.
      unfold init_census.
      simpl.
      simpl in H0. unfold init_census in H0. simpl in H0.
      rewrite init_census_plus_ar.
      erewrite proper_minus_census_d.
      Focus 2.
      apply smgd_sym.
      apply H0.
      rewrite <- H.
      rewrite gccombine_sub.
      rewrite gccombine_sub.
      assert (Hcc := combine_plus_census_correct).
      destruct Hcc.
      rewrite <- H1.
      rewrite gccombine'.
      omega.
    - unfold init_census.
      simpl. intro. rewrite gccombine_sub.
      rewrite <- H.
      rewrite gccombine_sub.
      rewrite init_census_plus_ar.
      assert (H' := combine_plus_census_correct).
      destruct H'.
      rewrite <- H0.
      rewrite gccombine'.
      rewrite apply_r_empty.
      rewrite get_c_up.
      rewrite gdempty.
      rewrite get_c_minus. omega.
    - intro.
      rewrite gccombine_sub.
      unfold init_census. simpl.
      rewrite init_census_plus_ar.
      rewrite <- H0.
      rewrite gccombine_sub.
      symmetry.
      assert (H' := combine_plus_census_correct).
      destruct H'.
      rewrite <- H1.
      rewrite gccombine'.
      rewrite <- H2.
      rewrite gccombine'.
      rewrite <- (proj2 rename_all_ns_empty).
      rewrite <- H.
      rewrite gccombine_sub.
      unfold init_census.
      rewrite gdempty.
      omega. 
    - intro.
      rewrite gccombine_sub.
      rewrite <- combine_minus_census_list.
      rewrite gccombine_sub.
      unfold init_census. simpl.
      rewrite <- combine_plus_census_list.
      rewrite gccombine'.
      rewrite apply_r_empty.
      rewrite apply_r_list_empty.
      rewrite get_c_up.
      rewrite get_c_minus. rewrite gdempty.
      omega.
    - intro.
      rewrite gccombine_sub.
      unfold init_census. simpl.
      rewrite <- H.
      rewrite gccombine_sub.
      assert (H' := combine_plus_census_correct).
      destruct H'.
      rewrite <- H0.
      rewrite gccombine'.
      symmetry.
      rewrite <- combine_minus_census_list.
      rewrite gccombine_sub.
      rewrite <- (proj1 rename_all_ns_empty).
      omega.
    - intro.
      rewrite gccombine_sub.
      rewrite get_c_minus. unfold init_census. simpl. rewrite get_c_up. rewrite gdempty. rewrite apply_r_empty. omega.
    - intro; rewrite gccombine_sub.
      rewrite <- H0.
      rewrite gccombine_sub.
      rewrite init_census_plus_ar_f.
      assert (H' := combine_plus_census_correct).
      destruct H'.      
      rewrite <- H2.
      rewrite gccombine'.
      symmetry. rewrite <- H. rewrite gccombine_sub. unfold init_census.
      omega.
    - intro.     
      rewrite gccombine_sub.
      rewrite gdempty.
      rewrite minus_n_O. reflexivity.
  Qed.


  

  Theorem rename_all_ns_app_ctx:
    forall e sig, 
      (forall c,
         rename_all_ns sig (c |[ e]|) =
         (rename_all_ctx_ns sig c) |[rename_all_ns sig e ]|) /\
      (forall fc,
         rename_all_fun_ns sig (fc <[ e]>) =
         (rename_all_fun_ctx_ns sig fc) <[rename_all_ns sig e ]>)
  .
  Proof.
    intros.
    exp_fundefs_ctx_induction IHc IHfc; simpl; auto; try (rewrite IHc; auto); try (rewrite IHfc; auto).
    intro. 
    rewrite list_append_map.
    simpl.
    rewrite IHc; auto.
  Qed.


  Theorem rename_all_ctx_ns_comp_ctx:
    forall c' sig, 
      (forall c,
         rename_all_ctx_ns sig (comp_ctx_f c c') =
         comp_ctx_f (rename_all_ctx_ns sig c) (rename_all_ctx_ns sig c')) /\
      (forall fc,
         rename_all_fun_ctx_ns sig (comp_f_ctx_f fc c') =
         comp_f_ctx_f (rename_all_fun_ctx_ns sig fc) (rename_all_ctx_ns sig c'))
  .
    intros.
    exp_fundefs_ctx_induction IHc IHfc; simpl; auto; try (rewrite IHc; auto); try (rewrite IHfc; auto).
  Qed.
  
  
  
  
  Theorem rename_all_ns_fundefs_append:
    forall sig B2 B1,
      rename_all_fun_ns sig (fundefs_append B1 B2) =
      fundefs_append (rename_all_fun_ns sig B1) (rename_all_fun_ns sig B2).
  Proof.
    induction B1; simpl; auto.
    rewrite IHB1. auto.
  Qed.               



  
  Theorem all_fun_name_append:
    forall B2 B1,
      all_fun_name (fundefs_append B1 B2) = all_fun_name B1 ++ all_fun_name B2.
  Proof.
    induction B1; auto.
    simpl.
    rewrite IHB1. auto.
  Qed.      


  Theorem remove_all_append:
    forall B2 B1 sig,
      remove_all sig (B1++B2) = remove_all (remove_all sig B1) B2.
  Proof.
    induction B1; auto.
    intro.
    simpl.
    erewrite IHB1. auto.
  Qed.

  Corollary ub_app_ctx_exp:
    forall c e v,
      unique_bindings (c |[ e ]|) ->
      bound_var e v ->
      ~ bound_var_ctx c v. 
  Proof.
    intros.
    apply ub_app_ctx_f in H.
    destructAll.
    inv H2. specialize (H3 v).
    intro; apply H3.
    split; auto.
  Qed.



  (** set of free variables for an applicative context *)
  Inductive occurs_free_ctx : exp_ctx -> Ensemble var :=
  | Free_Econstr1 :
      forall y x t ys e,
        List.In y ys ->
        occurs_free_ctx (Econstr_c x t ys e) y
  | Free_Econstr2 :
      forall y x t ys e,
        ~ x = y ->
        occurs_free_ctx e y ->
        occurs_free_ctx (Econstr_c x t ys e) y
  | Free_Ecase1 :
      forall x cl1 c e cl2, 
        occurs_free_ctx (Ecase_c x cl1 c e cl2) x
  | Free_Ecase2 :  
      forall y x cl1 c e cl2,
        occurs_free_ctx e y ->
        occurs_free_ctx (Ecase_c x cl1 c e cl2) y
  | Free_Ecase3 :  
      forall y x cl1 c e cl2,
        occurs_free (Ecase x cl1) y ->
        occurs_free_ctx (Ecase_c x cl1 c e cl2) y
  | Free_Ecase4 :  
      forall y x cl1 c e cl2,
        occurs_free (Ecase x cl2) y ->
        occurs_free_ctx (Ecase_c x cl1 c e cl2) y
  | Free_Eproj1 :
      forall y x tau n e,
        occurs_free_ctx (Eproj_c x tau n y e) y
  | Free_Eproj2 :
      forall y x tau n y' e,
        x <> y ->
        occurs_free_ctx e y ->
        occurs_free_ctx (Eproj_c x tau n y' e) y
  | Free_Efun11 :
      forall y defs e,
        ~ (name_in_fundefs defs y) -> 
        occurs_free_ctx e y ->
        occurs_free_ctx (Efun1_c defs e) y
  | Free_Efun21 :
      forall y defs e,
        ~ (names_in_fundefs_ctx defs y) -> 
        occurs_free e y ->
        occurs_free_ctx (Efun2_c defs e) y                             
  | Free_Efun12 :
      forall y defs e, 
        occurs_free_fundefs defs y ->
        occurs_free_ctx (Efun1_c defs e) y
  | Free_Efun22 :
      forall y defs e, 
        occurs_free_fundefs_ctx defs y ->
        occurs_free_ctx (Efun2_c defs e) y
  | Free_Eprim1 :
      forall y x p ys e,
        List.In y ys ->
        occurs_free_ctx (Eprim_c x p ys e) y
  | Free_Eprim2 :
      forall y x p ys e,
        x <> y ->
        occurs_free_ctx e y ->
        occurs_free_ctx (Eprim_c x p ys e) y
  with occurs_free_fundefs_ctx : fundefs_ctx -> Ensemble var :=
        | Free_Fcons11 :
            forall x f tau ys e defs,  
              x <> f ->
              ~ (List.In x ys) ->
              ~ (name_in_fundefs defs x) ->
              occurs_free_ctx e x ->
              occurs_free_fundefs_ctx (Fcons1_c f tau ys e defs) x
        | Free_Fcons12 :
            forall x f tau ys e defs,
              occurs_free_fundefs defs x ->
              x <> f ->
              occurs_free_fundefs_ctx (Fcons1_c f tau ys e defs) x
        | Free_Fcons21 :
            forall x f tau ys e defs,  
              x <> f ->
              ~ (List.In x ys) ->
              ~ (names_in_fundefs_ctx defs x) ->
              occurs_free e x ->
              occurs_free_fundefs_ctx (Fcons2_c f tau ys e defs) x
        | Free_Fcons22 :
            forall x f tau ys e defs,
              occurs_free_fundefs_ctx defs x ->
              x <> f ->
              occurs_free_fundefs_ctx (Fcons2_c f tau ys e defs) x.

  Hint Constructors occurs_free_ctx occurs_free_fundefs.

  Lemma occurs_free_Econstr_c x t ys e :
    Same_set var (occurs_free_ctx (Econstr_c x t ys e))
             (Union _ (FromList ys) (Setminus var (occurs_free_ctx e) (Singleton var x))).
  Proof.
    split; intros x' H; inv H; eauto.
    right. constructor; eauto. intros H. inv H; eauto.
    inv H0.  constructor 2; eauto. intros Hc. subst. eauto.
  Qed.

  Lemma occurs_free_Eprim_c x f ys e :
    Same_set var (occurs_free_ctx (Eprim_c x f ys e))
             (Union _ (FromList ys) (Setminus var (occurs_free_ctx e) (Singleton var x))).
  Proof.
    split; intros x' H; inv H; eauto.
    right. constructor; eauto. intros H. inv H; eauto.
    inv H0. eapply Free_Eprim2; eauto. intros Hc. subst. eauto.
  Qed.

  Lemma occurs_free_Eproj_c x tag n y e :
    Same_set var (occurs_free_ctx (Eproj_c x tag n y e))
             (Union _ (Singleton var y) (Setminus var (occurs_free_ctx e) (Singleton var x))).
  Proof.
    split; intros x' H; inv H; eauto. 
    right. constructor; eauto. intros H. inv H; eauto.
    inv H0. eauto.
    inv H0. constructor; eauto.
    intros Hc. subst. eauto.
  Qed.

  Lemma occurs_free_Efun1_c B e :
    Same_set var (occurs_free_ctx (Efun1_c B e))
             (Union _ (occurs_free_fundefs B)
                    (Setminus _ (occurs_free_ctx e) (name_in_fundefs B))).
  Proof.
    split; intros x' H; inv H; eauto.
    right; eauto. constructor; eauto.
    inv H0. eauto. 
  Qed.
  
  Lemma occurs_free_Efun2_c B e :
    Same_set var (occurs_free_ctx (Efun2_c B e))
             (Union _ (occurs_free_fundefs_ctx B)
                    (Setminus _ (occurs_free e) (names_in_fundefs_ctx B))).
  Proof.
    split; intros x' H; inv H; eauto.
    right; eauto. constructor; eauto.
    inv H0. eauto. 
  Qed.


  Lemma occurs_free_Ecase_c x cl1 cl2 c e :
    Same_set var (occurs_free_ctx (Ecase_c x cl1 c e cl2))
             (Union _ (Singleton _ x)
                    (Union _ (occurs_free_ctx e)
                           (Union _ (occurs_free (Ecase x cl1)) (occurs_free (Ecase x cl2))))).
  Proof.
    split; intros x' H; inv H; eauto.
    inv H0; eauto. inv H0; eauto.
    inv H; eauto.
  Qed.

  
  Lemma occurs_free_fundefs_Fcons1_c f t xs e B :
    Same_set var (occurs_free_fundefs_ctx (Fcons1_c f t xs e B))
             (Union var (Setminus var (occurs_free_ctx e)
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

  Lemma occurs_free_fundefs_Fcons2_c f t xs e B :
    Same_set var (occurs_free_fundefs_ctx (Fcons2_c f t xs e B))
             (Union var (Setminus var (occurs_free e)
                                  (Union var (Singleton var f)
                                         (Union var (FromList xs)
                                                (names_in_fundefs_ctx B))))
                    (Setminus var (occurs_free_fundefs_ctx B) (Singleton var f))).
  Proof.
    split; intros x H; inv H.
    - left. constructor; eauto. intros Hin. inv Hin; eauto.
      inv H. congruence. inv H; eauto.
    - right. constructor; eauto. intros H. inv H. congruence.
    - inv H0. constructor; eauto. 
      intros Hc. subst. eauto.
    - inv H0.
      constructor 4;  eauto.
      intros Hc; subst; eauto.
  Qed.

  Lemma occurs_free_Hole_c:
    Same_set var (occurs_free_ctx Hole_c)
             (Empty_set var).
  Proof.
    split; intros x H; inv H.
  Qed.


  Ltac normalize_occurs_free_ctx :=
    match goal with
      | [|- context[occurs_free_ctx (Econstr_c _ _ _ _)]] =>
        rewrite occurs_free_Econstr_c
      | [|- context[occurs_free_ctx (Eproj_c _ _ _ _ _)]] =>
        rewrite occurs_free_Eproj_c
      | [|- context[occurs_free_ctx (Ecase_c _ _ _ _ _ )]] =>
        rewrite occurs_free_Ecase_c
      | [|- context[occurs_free_ctx (Efun1_c _ _)]] =>
        rewrite occurs_free_Efun1_c
      | [|- context[occurs_free_ctx (Efun2_c _ _)]] =>
        rewrite occurs_free_Efun2_c
      | [|- context[occurs_free_ctx (Eprim_c _ _ _ _)]] =>
        rewrite occurs_free_Eprim_c
      | [|- context[occurs_free_fundefs_ctx (Fcons1_c _ _ _ _ _)]] =>
        rewrite occurs_free_fundefs_Fcons1_c
      | [|- context[occurs_free_fundefs_ctx (Fcons2_c _ _ _ _ _)]] =>
        rewrite occurs_free_fundefs_Fcons2_c
      | [|- context[occurs_free_ctx (Hole_c)]] =>
        rewrite occurs_free_Hole_c
    end.

  Ltac normalize_occurs_free_ctx_in_ctx :=
    match goal with
      | [ H : context[occurs_free_ctx (Econstr_c _ _ _ _)] |- _ ] =>
        rewrite occurs_free_Econstr_c
      | [ H : context[occurs_free_ctx (Eproj_c _ _ _ _ _)] |- _ ] =>
        rewrite occurs_free_Eproj_c
      | [ H : context[occurs_free_ctx (Ecase_c _ _ _ _ _ )] |- _ ] =>
        rewrite occurs_free_Ecase_c
      | [ H : context[occurs_free_ctx (Efun1_c _ _)] |- _ ] =>
        rewrite occurs_free_Efun1_c
      | [ H : context[occurs_free_ctx (Efun2_c _ _)] |- _ ] =>
        rewrite occurs_free_Efun2_c
      | [ H : context[occurs_free_ctx (Eprim_c _ _ _ _)] |- _ ] =>
        rewrite occurs_free_Eprim_c
      | [ H : context[occurs_free_fundefs_ctx (Fcons1_c _ _ _ _ _)] |- _ ] =>
        rewrite occurs_free_fundefs_Fcons1_c
      | [ H : context[occurs_free_fundefs_ctx (Fcons2_c _ _ _ _ _)] |- _ ] =>
        rewrite occurs_free_fundefs_Fcons2_c
      | [ H : context[occurs_free_ctx (Hole_c)] |- _ ] =>
        rewrite occurs_free_Hole_c
    end.

  (* push rename_all_ns and inlined_ctx down *)    
  Ltac normalize_ctx :=
    match goal with
      (* rename_all *)
      | [H: context[rename_all_ns _ (_ |[ _ ]|)] |- _] =>
        rewrite (proj1 (rename_all_ns_app_ctx _ _)) in H
      | [H: context[rename_all_fun_ns _ (_ <[ _ ]>)] |- _] =>
        rewrite (proj2 (rename_all_ns_app_ctx _ _)) in H
      | [|- context[rename_all_ns _ (_ |[ _ ]|)]] =>
        rewrite (proj1 (rename_all_ns_app_ctx _ _))
      | [|- context[rename_all_fun_ns _ (_ <[ _ ]>)]] =>
        rewrite (proj2 (rename_all_ns_app_ctx _ _))
      | [H: context[rename_all_fun_ns _ (fundefs_append _ _)] |- _] =>
        rewrite rename_all_ns_fundefs_append in H
      | [|- context[rename_all_fun_ns _ (fundefs_append _ _)]] =>
        rewrite rename_all_ns_fundefs_append
      | [H: context[rename_all_ctx_ns _ (comp_ctx_f _ _)] |- _] =>
        rewrite (proj1 (rename_all_ctx_ns_comp_ctx _ _)) in H
      | [|- context[rename_all_ctx_ns _ (comp_ctx_f _ _)]] =>
        rewrite (proj1 (rename_all_ctx_ns_comp_ctx _ _))
      | [H: context[rename_all_fun_ctx_ns _ (comp_f_ctx_f _ _)] |- _] =>
        rewrite (proj2 (rename_all_ctx_ns_comp_ctx _ _)) in H
      | [|- context[rename_all_fun_ctx_ns _ (comp_f_ctx_f _ _)]] =>
        rewrite (proj2 (rename_all_ctx_ns_comp_ctx _ _))

      (* inlined *)
      | [H: context[ inlined_ctx_f (comp_ctx_f _ _ ) _ ] |- _] =>
        rewrite (proj1 (inlined_comp_ctx)) in H
      | [|-context[ inlined_ctx_f (comp_ctx_f _ _) _]] =>
        rewrite (proj1 (inlined_comp_ctx))
      | [H: context[ inlined_fundefs_ctx_f (comp_f_ctx_f _ _) _] |- _] =>
        rewrite (proj2 (inlined_comp_ctx)) in H
      | [|-context[ inlined_fundefs_ctx_f (comp_f_ctx_f _ _) _]] =>
        rewrite (proj2 (inlined_comp_ctx))
      | [H: context[ inlined_fundefs_f (fundefs_append _ _) _] |- _] =>
        rewrite inlined_fundefs_append in H
      | [|-context[ inlined_fundefs_f (fundefs_append _ _) _]] =>
        rewrite inlined_fundefs_append
    end.



  Theorem sig_inv_full_dead:
    forall c c' e sig,
      sig_inv_full sig (comp_ctx_f c c')  e  ->
      (forall v, bound_stem_ctx c' v -> num_occur (c  |[ e ]|) v 0) -> 
      sig_inv_full sig c e.
  Proof.
    intros.
    intro. intros. apply H in H1.
    inv H1.
    split.
    - intro; apply H2.
      apply bound_var_app_ctx in H1.
      apply bound_var_app_ctx.
      inv H1.
      left. 
      apply bound_var_ctx_comp_ctx.
      auto.
      auto.
    - destruct H3.
      + left.
        apply num_occur_app_ctx in H1.
        destructAll; pi0.
        apply num_occur_ec_comp_ctx in H1.
        destructAll; pi0.
        apply num_occur_app_ctx; eauto.
      + apply bound_stem_comp_ctx_mut in H1.
        inv H1. auto.
        left; apply H0; auto.
  Qed.            

  
  Definition closed_ctx :=
    fun c => Empty_set var <--> occurs_free_ctx c.
  
  Definition closed_fundefs_ctx :=
    fun cf => Empty_set var <--> occurs_free_fundefs_ctx cf.

  Definition closed_fundefs :=
    fun f => Empty_set var <--> occurs_free_fundefs f.

  Theorem fun_names_not_free_in_fundefs_ctx :
    forall x f7,
      names_in_fundefs_ctx f7 x
      -> ~ occurs_free_fundefs_ctx f7 x.
  Proof.
    induction f7; intros; intro.
    inv H; inv H0; auto.
    inv H1; auto.
    inv H1; auto.
    revert H7.
    apply fun_names_not_free_in_fundefs.
    auto.
    inv H; inv H0; auto.
    inv H1; auto.
    inv H1; auto.
    revert H7.
    apply IHf7; auto.
  Qed.
  
  Theorem occurs_free_ctx_dec :
    (forall c,
       Decidable (occurs_free_ctx c)) /\
    (forall fc,
       Decidable (occurs_free_fundefs_ctx fc)).
  Proof.         
    exp_fundefs_ctx_induction IHc IHf; constructor; intros x; try (inv IHc; specialize (Dec x)); try (inv IHf; specialize (Dec x)).
    - right; auto.
      intro. inv H.
    - assert (Hl := Decidable_FromList l).
      inv Hl.
      specialize (Dec0 x).
      inv Dec0.
      left; auto.
      destruct (var_dec  v x).
      subst.
      right.
      intro.
      inv H0. auto.
      apply H6; auto.
      inv Dec.
      left; auto.
      right.
      intro. inv H1; auto.           
    - destruct (var_dec x v0).
      subst. left; auto.
      destruct (var_dec v x).
      subst.
      right; intro. inv H; auto.
      inv Dec.
      left; auto.
      right; intro.
      inv H0; auto.           
    - assert (Hl := Decidable_FromList l).
      inv Hl.
      specialize (Dec0 x).
      inv Dec0.
      left; auto.
      destruct (var_dec  v x).
      subst.
      right.
      intro.
      inv H0. auto.
      apply H6; auto.
      inv Dec.
      left; auto.
      right.
      intro. inv H1; auto.           
    - assert (Hl := Decidable_occurs_free (Ecase v l)).
      assert (Hl0 := Decidable_occurs_free (Ecase v l0)).
      inv Hl. specialize (Dec0 x).
      inv Hl0. specialize (Dec1 x).
      inv Dec0.
      left. apply Free_Ecase3; auto.
      inv Dec1.
      left. apply Free_Ecase4; auto.
      inv Dec.
      left. constructor; auto.
      right. intro.
      inv H2; auto.
    - assert (Hf4 := Decidable_occurs_free_fundefs f4).
      inv Hf4; specialize (Dec0 x).
      inv Dec0.
      left; auto.
      assert (Hf4n := Decidable_name_in_fundefs f4).
      inv Hf4n. specialize (Dec0 x).
      inv Dec0.
      right.
      intro.
      inv H1; auto.
      destruct Dec.
      left; auto.
      right; intro. inv H2; auto.
    - assert (He := Decidable_occurs_free e). 
      inv He; specialize (Dec0 x).
      inv Dec.
      left; auto.
      assert (Hf5 := Decidable_name_in_fundefs_ctx f5).
      inv Hf5. specialize (Dec x). inv Dec.
      right.
      intro; auto. inv H1; auto.
      inv Dec0.
      left; auto.
      right; intro; apply H1.
      inv H2; auto.
      exfalso; auto.
    - destruct (var_dec x v).
      right.
      intro. subst. inv H; auto.
      assert (Hf6 := Decidable_name_in_fundefs f6).
      inv Hf6. specialize (Dec0 x).
      inv Dec0.
      right. intro. inv H0.
      auto.
      revert H7; apply fun_names_not_free_in_fundefs; auto.
      assert (He := Decidable_occurs_free_fundefs f6).
      inv He. specialize (Dec0 x).
      inv Dec0.
      left; constructor 2; auto.
      inv Dec.
      assert (Hl := Decidable_FromList l).
      inv Hl. specialize (Dec x). inv Dec.
      right; intro; inv H3; auto.
      left. constructor; auto.
      right. intro. inv H2; auto.           
    - destruct (var_dec x v).
      right.
      intro. subst. inv H; auto.
      assert (Hf6 := Decidable_name_in_fundefs_ctx f7).
      inv Hf6. specialize (Dec0 x).
      inv Dec0.
      right. intro. inv H0.
      auto.
      revert H7.
      apply fun_names_not_free_in_fundefs_ctx; auto.
      inv Dec.
      left; constructor 4; auto.
      assert (Hl := Decidable_FromList l).
      inv Hl. specialize (Dec x). inv Dec.
      right; intro; inv H2; auto.
      assert (He :=  Decidable_occurs_free e).
      inv He. specialize (Dec x). inv Dec. left; constructor; auto.
      right. intro. inv H3; auto.           
  Qed.

  Theorem Decidable_occurs_free_ctx:         
    (forall c,
       Decidable (occurs_free_ctx c)).
  Proof.
    intro; apply occurs_free_ctx_dec; auto.
  Qed.         

  Theorem Decidable_occurs_free_fundefs_ctx:         
    forall fc,
      Decidable (occurs_free_fundefs_ctx fc).
  Proof.
    intro; apply occurs_free_ctx_dec; auto.
  Qed.         

  Lemma occurs_free_included_ctx_mut:
    forall e,
      (forall c,
         Included _ (occurs_free_ctx c) (occurs_free (c|[e]|))) /\
      (forall fc,
         Included _ (occurs_free_fundefs_ctx fc) (occurs_free_fundefs (fc <[ e ]>))).
  Proof.
    intro e; exp_fundefs_ctx_induction IHc IHf; intros; repeat normalize_occurs_free_ctx; simpl; repeat normalize_occurs_free; eauto with Ensembles_DB.
    rewrite <- name_in_fundefs_ctx_ctx.
    eauto with Ensembles_DB.
    rewrite <- name_in_fundefs_ctx_ctx.
    eauto with Ensembles_DB.
  Qed.


  Theorem occurs_free_included_ctx:
    forall e,
      (forall c,
         Included _ (occurs_free_ctx c) (occurs_free (c|[e]|))).
  Proof.
    intros; apply occurs_free_included_ctx_mut.
  Qed.

  Theorem occurs_free_included_fundefs_ctx:
    forall e,
      (forall fc,
         Included _ (occurs_free_fundefs_ctx fc) (occurs_free_fundefs (fc <[ e ]>))).
  Proof.
    intros; apply occurs_free_included_ctx_mut.
  Qed.

  Corollary closed_app_ctx:
    forall e c,
      closed (c |[ e ]|) ->
      closed_ctx c. 
  Proof.
    intros.
    assert (Hc := occurs_free_included_ctx e c).
    apply Included_Empty_set_l.
    eapply Proper_Included_r; eauto.
  Qed.
  



  
  
  Corollary ub_app_ctx_ctx:
    forall c e v,
      unique_bindings (c |[ e ]|) ->
      bound_var_ctx c v ->
      ~ bound_var e v. 
  Proof.
    intros.
    apply ub_app_ctx_f in H.
    destructAll.
    inv H2.
    specialize (H3 v).
    intro; apply H3.
    split; auto.
  Qed.



  
  (* End move_to_identifiers.*)

  
  Theorem not_free_dead_or_bound:
    forall e,
      Included _ (Complement _ (occurs_free e)) (Union _ (dead_var e) (bound_var e)).
  Proof.
    intros.
    intro. intro.
    apply not_free_bound_or_not_occur in H.
    destruct H; auto.
  Qed.

  Theorem not_bound_dead_or_free:
    forall e,
      Included _ (Complement _ (bound_var e)) (Union _ (dead_var e) (occurs_free e)).
  Proof.
    intros.
    intro; intro.
    assert (He := Decidable_occurs_free e). 
    inv He. specialize (Dec x).
    inv Dec; auto.
    apply not_free_dead_or_bound in H0.
    inv H0; auto.
    exfalso. auto.
  Qed.         

  Theorem closed_sig_inv_dom_implies_sig_inv:
    forall sig e,
      closed e ->
      sig_inv_dom sig e ->
      sig_inv sig e.
  Proof.
    intros.
    intro; intros.
    apply H0 in H1.
    split; auto.
    assert (~ occurs_free e y). intro.
    apply H in H2. inv H2.
    apply not_free_dead_or_bound in H2.
    inv H2; auto.
  Qed.

  Theorem rename_all_ns_id: forall sig e,
                              sig_inv_dom sig e ->
                              closed e ->
                              rename_all_ns sig e = e.
  Proof.
    intros.
    rewrite <- (proj1 (rename_all_no_shadow _)) by auto.
    apply rename_sig_dead.
    apply sig_inv_closed_dead; auto.
    apply closed_sig_inv_dom_implies_sig_inv; auto.
  Qed.
  
  
  Theorem name_in_bound_var_fundefs_ctx: forall cf,
                                           Included _ (names_in_fundefs_ctx cf) (bound_var_fundefs_ctx cf).
  Proof.
    induction cf; simpl; normalize_bound_var_ctx; auto with Ensembles_DB.
    intro. intro. inv H. auto.
    apply name_in_fundefs_bound_var_fundefs in H0.
    auto.
  Qed.
  
  Theorem not_free_bound_or_not_occur_ctx:
    forall v : var,
      (forall c : exp_ctx, ~ occurs_free_ctx c v -> num_occur_ec c v 0 \/ bound_var_ctx c v) /\
      (forall cf : fundefs_ctx,
         ~ occurs_free_fundefs_ctx cf v -> num_occur_fdc cf v 0 \/ bound_var_fundefs_ctx cf v).
  Proof.
    intro v; exp_fundefs_ctx_induction IHc IHf; intros; eauto with Ensembles_DB.
    -  left. constructor.
    - destruct (var_dec v0 v).
      + right; subst; auto.
      + assert (~occurs_free_ctx e v).
        intro; apply H.
        constructor 2; auto.
        apply IHc in H0.
        inv H0.
        * left.
          eapply num_occur_ec_n.
          constructor. apply H1.
          assert (~ FromList l v).
          intro; apply H.
          auto.
          apply not_occur_list_not_in in H0. rewrite H0; auto.
        * right; auto.
    -  destruct (var_dec v0 v).
       + right; subst; auto.
       +  assert (~occurs_free_ctx e v).
          intro; apply H.
          auto.
          apply IHc in H0.
          inv H0.
          * left.
            eapply num_occur_ec_n.
            constructor. apply H1.
            simpl. destruct (cps_util.var_dec v v1).
            subst;
              exfalso; apply H; auto.
            auto.
          * right; auto.
    -  destruct (var_dec v0 v).
       + right; subst; auto.
       +  assert (~occurs_free_ctx e v).
          intro; apply H.
          auto.
          apply IHc in H0.
          inv H0.
          * left.
            eapply num_occur_ec_n.
            constructor. apply H1.
            simpl.
            assert (~ FromList l v).
            intro; apply H.
            auto.
            apply not_occur_list_not_in in H0. rewrite H0; auto.
          * right; auto.
    - assert (~ Union var [set v0]
                (Union var (occurs_free_ctx e)
                       (Union var (occurs_free (Ecase v0 l))
                              (occurs_free (Ecase v0 l0)))) v).
      intro. apply H.
      apply occurs_free_Ecase_c.
      auto.
      assert (v <> v0).
      intro; apply H0; subst; 
      left; auto.
      assert (~ occurs_free (Ecase v0 l) v).
      intro; apply H0.
      right; right; left; auto.
      assert (~ occurs_free (Ecase v0 l0) v).
      intro; apply H0.
      right; right; right; auto.
      assert (~(occurs_free_ctx e) v). 
      intro; apply H0.
      right; left; auto.
      clear H0.
      apply IHc in H4.
      apply not_free_bound_or_not_occur in H2.
      apply not_free_bound_or_not_occur in H3. 
      destruct H2.
      destruct H3.
      destruct H4.
      left.
      inv H0; pi0.
      inv H2; pi0.
      eapply num_occur_ec_n.
      constructor; eauto.
      simpl. destruct (cps_util.var_dec v v0). subst; exfalso; auto.
      auto.
      right; auto.
      right; auto.
      inv H2.
      eapply Bound_Case3_c; eauto.
      right.
      inv H0;
        eapply Bound_Case2_c; eauto.
    - assert (Hf4 := Decidable_name_in_fundefs f4).
      destruct Hf4.
      specialize (Dec v).
      inv Dec.
      right.
      constructor.
      apply name_in_fundefs_bound_var_fundefs.
      auto.
      assert (~ occurs_free_ctx e v).
      intro; apply H; auto.
      assert (~ occurs_free_fundefs f4 v).
      intro; apply H. auto.
      apply IHc in H1.
      apply not_free_bound_or_not_occur in H2.
      destruct H1.
      destruct H2.
      left.
      eapply num_occur_ec_n.
      constructor; eauto.
      auto.
      right; auto.
      right; auto.
    - assert (Hf5 := Decidable_name_in_fundefs_ctx f5).
      destruct Hf5.
      specialize (Dec v).
      inv Dec.
      right.
      constructor.
      apply name_in_bound_var_fundefs_ctx. auto.
      assert (~ occurs_free_fundefs_ctx f5 v).
      intro; apply H; auto.
      assert (~ occurs_free e v).
      intro; apply H; auto.
      apply IHf in H1.
      apply not_free_bound_or_not_occur in H2.
      inv H1. inv H2.
      left.
      eapply num_occur_ec_n.
      constructor; eauto. auto.
      right; auto.
      right; auto.
    - destruct (var_dec v0 v).
      right; subst.
      constructor.
      assert (Hl := Decidable_FromList l).
      inv Hl.
      specialize (Dec v).
      inv Dec.
      right; auto.
      assert (Hf6 := Decidable_name_in_fundefs f6).
      destruct Hf6.
      specialize (Dec v).
      inv Dec.
      right. apply name_in_fundefs_bound_var_fundefs in H1. auto.
      assert (~ occurs_free_ctx e v).
      intro; apply H.
      constructor; auto.
      apply IHc in H2.
      assert (~ occurs_free_fundefs f6 v).
      intro; apply H. constructor 2; auto.
      apply not_free_bound_or_not_occur in H3. 
      inv H2.
      inv H3.
      left. eapply num_occur_fdc_n.
      constructor; eauto. auto.
      right. auto.
      right. auto.    
    - destruct (var_dec v0 v).
      right; subst.
      constructor.
      assert (Hl := Decidable_FromList l).
      inv Hl.
      specialize (Dec v).
      inv Dec.
      right; auto.
      assert (Hf7 := Decidable_name_in_fundefs_ctx f7).
      destruct Hf7.
      specialize (Dec v).
      inv Dec.
      right. apply name_in_bound_var_fundefs_ctx in H1. auto.
      assert (~ occurs_free e v).
      intro; apply H.
      constructor; auto.
      apply not_free_bound_or_not_occur in H2. 
      assert (~ occurs_free_fundefs_ctx f7 v).
      intro; apply H. apply Free_Fcons22; auto.
      apply IHf in H3.
      inv H2.
      inv H3.
      left. eapply num_occur_fdc_n.
      constructor; eauto. auto.
      right. auto.
      right. auto.
  Qed.





  Corollary not_occurs_free_ctx_not_bound:
    forall c e x,
      ~ occurs_free (c |[ e ]|) x ->
      ~ bound_var_ctx c x ->
      ~ occurs_free e x.
  Proof.
    intros. intro. apply H.
    apply occurs_free_ctx_not_bound; auto.
  Qed.

  Corollary not_occur_free_Efun:
    forall f e,
      Same_set _
               (Complement _ (occurs_free (Efun f e)))
               (Intersection _ (Complement _ (occurs_free_fundefs f))
                             (Complement _ (Setminus _  (occurs_free e) (name_in_fundefs f)))).
  Proof.
    intros; split; intro; intro.
    -  split.
       intro. apply H.
       apply occurs_free_Efun. auto.
       intro. apply H.
       apply occurs_free_Efun. auto.
    - intro.
      apply occurs_free_Efun in H0.
      inv H. 
      inv H0; auto.
  Qed.



  Theorem occurs_free_fundefs_append:
    forall f1 f2,
      Same_set _
               (occurs_free_fundefs (fundefs_append f1 f2))
               (Setminus _ (Union _ (occurs_free_fundefs f1) (occurs_free_fundefs f2))  (name_in_fundefs (fundefs_append f1 f2))).
  Proof.
    induction f1; intros.
    -  simpl.
       rewrite occurs_free_fundefs_Fcons.
       rewrite IHf1.     
       rewrite occurs_free_fundefs_Fcons.
       assert (Hf := fundefs_append_name_in_fundefs).
       specialize (Hf f1 f2 (fundefs_append f1 f2)).     
       specialize (Hf eq_refl).
       split; intro; intro.
       + inv H.
         * inv H0. split.
           left. left. constructor.
           auto. intro. apply H1. rewrite Hf. inv H0; auto. inv H2; auto.
           intro. apply H1. inv H0; auto.
         * inv H0. inv H. inv H0.
           split; auto.
           left. right. split; auto.
           intro. inv H0; auto.
           split. right; auto.
           intro. inv H0; auto.
       +          inv H. inv H0.
                  inv H.
                  inv H0.
                  left. split; auto.
                  intro.
                  inv H0. apply H1. auto.
                  inv H3. apply H2. auto.
                  apply H1. auto.
                  inv H0. right. split. split.
                  left; auto.
                  intro. apply H1; auto. auto.
                  right. split. split.
                  right; auto.
                  intro; apply H1; auto.
                  intro; apply H1; auto.
    -          simpl. rewrite occurs_free_fundefs_Fnil.
               assert (Hnn := name_not_free_in_fds f2).
               rewrite Union_Empty_set_neut_l.
               symmetry.
               apply Setminus_Disjoint.
               auto.
  Qed.

  Theorem not_occurs_free_fundefs_append:
    forall f1 f2,
      Same_set _
               (Complement _ (occurs_free_fundefs (fundefs_append f1 f2)))
               (Intersection _ (Complement _ (Setminus _ (occurs_free_fundefs f1) (name_in_fundefs (fundefs_append f1 f2)))) (Complement _ (Setminus _ (occurs_free_fundefs f2) (name_in_fundefs (fundefs_append f1 f2))))).
  Proof.
    intros. split; intro; intro.
    - split. intro. apply H.
      apply occurs_free_fundefs_append.
      inv H0. split; auto.
      intro. apply H.
      apply occurs_free_fundefs_append. inv H0.
      split; auto.                        
    - intro.
      apply occurs_free_fundefs_append in H0. inv H0.
      inv H.
      inv H1. apply H0; split; auto.
      apply H3; split; auto.
  Qed.
  
  
  Theorem not_free_dead_or_bound_ctx:
    forall c,
      Included _ (Complement _ (occurs_free_ctx c)) (Union _ (dead_var_ctx c) (bound_var_ctx c)).
  Proof.
    intros.
    intro. intro.
    apply not_free_bound_or_not_occur_ctx in H.
    destruct H; auto.
  Qed.

  
  Theorem not_bound_dead_or_free_ctx:
    forall e,
      Included _ (Complement _ (bound_var_ctx e)) (Union _ (dead_var_ctx e) (occurs_free_ctx e)).
  Proof.
    intros.
    intro; intro.
    assert (He := (proj1 occurs_free_ctx_dec) e).
    inv He. specialize (Dec x).
    inv Dec; auto.
    apply not_free_dead_or_bound_ctx in H0.
    inv H0; auto.
    exfalso. auto.
  Qed.         

  


  Theorem closed_not_occurs_in_context:
    forall c v,
      closed_ctx c ->
      ~ bound_var_ctx c v ->
      num_occur_ec c v 0.
  Proof.
    intros.
    assert (~ occurs_free_ctx c v).
    intro.
    apply H in H1.
    inv H1.
    apply not_free_bound_or_not_occur_ctx in H1.
    inv H1; auto.
    exfalso; auto.
  Qed.

  
  
  Theorem closed_implies_Disjoint:
    forall e,
      closed e ->
      Disjoint _ (bound_var e) (occurs_free e).
  Proof.
    intros. split; intro. intro.
    inv H0.
    apply H in H2. inv H2.
  Qed.


  
  Theorem gsr_preserves_sig_dom:
    forall sig ce ce',
      unique_bindings ce ->
      closed ce ->
      gsr_clos ce ce' ->
      sig_inv_dom sig ce ->
      sig_inv_dom sig ce'. 
  Proof.      
    intros sig ce ce' Hub Hdj H H0.
    induction H; auto.
    inv H. intro.
    intros.

    apply H0 in H.
    inv H1.
    (* dead var *)
    - intro;
      apply H.
      apply bound_var_app_ctx in H1.
      apply bound_var_app_ctx.
      normalize_bound_var.
      destruct H1; auto.
    -   intro.
        apply H.
        apply bound_var_app_ctx in H1.
        apply bound_var_app_ctx.
        normalize_bound_var.
        destruct H1; auto.
    - intro.
      apply H.
      apply bound_var_app_ctx in H1.
      apply bound_var_app_ctx.
      normalize_bound_var.
      destruct H1; auto.
    - intro.
      apply H.
      apply bound_var_app_ctx in H1.
      apply bound_var_app_ctx.
      normalize_bound_var.
      destruct H1; auto.
    - intro.
      apply H.
      apply bound_var_app_ctx in H1.
      apply bound_var_app_ctx.          
      normalize_bound_var.
      rewrite bound_var_Efun in H1.
      rewrite fundefs_append_bound_vars.
      2: reflexivity.
      rewrite fundefs_append_bound_vars in H1.
      2: reflexivity.
      rewrite bound_var_fundefs_Fcons.          
      destruct H1; auto.
      destruct H1; auto.
      destruct H1; auto.
      right. left. right.
      auto.
    (* fold *)
    -  intro.
       apply H.
       apply bound_var_app_ctx.
       apply bound_var_app_ctx in H1. destruct H1; auto.
       right.
       rewrite bound_var_Econstr in *.
       destruct H1; auto.
       left.
       apply bound_var_app_ctx.
       apply bound_var_app_ctx in H1. destruct H1; auto.
       right.
       eapply Bound_Ecase. apply H1.
       apply findtag_In_patterns. eauto.
    -  intro.
       apply H.
       apply bound_var_app_ctx.
       apply bound_var_app_ctx in H1. destruct H1; auto.
       right.
       rewrite bound_var_Econstr in *.
       destruct H1; auto.
       left.
       apply bound_var_app_ctx.
       apply bound_var_app_ctx in H1. destruct H1; auto.
       right.
       rewrite bound_var_Eproj.
       left.
       unfold rename in H1.
       apply bound_var_rename_all_ns in H1.
       auto.
    (* inline *)
    -  intro.
       apply H.
       apply bound_var_app_ctx.
       apply bound_var_app_ctx in H1.
       inv H1; auto.
       right.
       rewrite bound_var_Efun.
       rewrite bound_var_Efun in H4.
       rewrite fundefs_append_bound_vars.
       2: reflexivity.
       rewrite fundefs_append_bound_vars in H4.
       2: reflexivity.
       rewrite bound_var_fundefs_Fcons.
       inv H4; auto.
       left.
       inv H1; auto.
       apply bound_var_app_ctx in H1.
       inv H1.
       right.
       apply bound_var_app_ctx.
       auto.
       apply bound_var_rename_all_ns in H4.
       left.
       auto.
    - apply gsr_preserves_clos in H; auto. destruct H.
      apply gsr_preserves_clos in H1; auto.         
  Qed.


  

  
  Theorem gsr_preserves_sig:
    forall sig ce ce',
      unique_bindings ce ->
      closed ce ->
      gsr_clos ce ce' ->
      sig_inv sig ce ->
      sig_inv sig ce'. 
  Proof.
    intros.
    apply sig_inv_implies_dom in H2.
    assert (He' := gsr_preserves_clos _ _ H H0 H1).
    destruct He'.
    apply closed_sig_inv_dom_implies_sig_inv; auto.
    eapply gsr_preserves_sig_dom.
    apply H.
    auto. auto. auto.
  Qed.


  


  
  (** rename_all_ns only affects variables which occurs in the term *)
  Theorem eq_P_rename_all_ns :
    (forall e : exp,
     forall sub sub' : maps_util.M.t var,
       eq_env_P (Complement _ (dead_var e)) sub sub' ->
       rename_all_ns sub e = rename_all_ns sub' e) /\
    (forall fds : fundefs,
     forall sub sub' : maps_util.M.t var,
       eq_env_P (Complement _ (dead_var_fundefs fds)) sub sub' ->
       rename_all_fun_ns sub fds = rename_all_fun_ns sub' fds).
  Proof.
    apply exp_def_mutual_ind; intros; simpl.
    - erewrite H.
      Focus 2.
      intro. intro. apply H0.
      intro. apply H1. inv H2; pi0; auto.
      erewrite eq_P_apply_r_list.
      reflexivity.
      intro; intro; apply H0.
      intro. inv H2.
      pi0.
      apply not_occur_list in H3.
      auto.
    - erewrite eq_P_apply_r.
      auto.
      intro; intro; apply H.
      inv H0.
      intro. inv H0.
      destruct (cps_util.var_dec x x).
      inv H5.
      apply n0; auto.
    - erewrite H.
      assert  (eq_env_P (Complement var (dead_var (Ecase v l))) sub sub').
      intro; intro; apply H1; intro.
      inv H3; pi0; auto. inv H7; pi0; auto.
      apply H2. eapply num_occur_n.
      constructor; eauto.
      simpl. destruct (cps_util.var_dec x v); auto.
      exfalso; auto.
      apply H0 in H2. simpl in H2. inv H2.
      auto.
      intro; intro; apply H1; intro.
      inv H3. inv H7; pi0.
      auto.
    - erewrite eq_P_apply_r.
      erewrite H.
      reflexivity.
      intro; intro; apply H0.
      intro. inv H2. pi0; auto.
      intro; intro. apply H0.
      intro. inv H2. pi0; auto.
      inv H1.
      auto.
    - erewrite H. erewrite H0.
      auto.
      intro; intro; apply H1.
      intro. inv H3; pi0; auto.
      intro; intro; apply H1.
      intro. inv H3; pi0; auto.
    - erewrite eq_P_apply_r.
      erewrite eq_P_apply_r_list.
      reflexivity.
      intro; intro. apply H. intro. inv H1; pi0.
      apply not_occur_list in H2.
      auto.
      intro; intro. apply H. intro.
      inv H0; inv H1; auto.
      pi0.
    - erewrite H.
      Focus 2.
      intro. intro. apply H0.
      intro. apply H1. inv H2; pi0; auto.
      erewrite eq_P_apply_r_list.
      reflexivity.
      intro; intro; apply H0.
      intro. inv H2.
      pi0.
      apply not_occur_list in H3.
      auto.
    - erewrite eq_P_apply_r.
      auto.
      intro; intro; apply H; intro.
      inv H0. inv H1; pi0.
    - erewrite H.
      erewrite H0; auto.
      intro; intro; apply H1; intro.
      inv H3; pi0; auto.
      intro; intro; apply H1; intro.
      inv H3; pi0; auto.
    - auto.
  Qed.

  Theorem eq_P_rename_all_ctx_ns :
    (forall e : exp_ctx,
     forall sub sub' : maps_util.M.t var,
       eq_env_P (Complement _ (dead_var_ctx e)) sub sub' ->
       rename_all_ctx_ns sub e = rename_all_ctx_ns sub' e) /\
    (forall fds : fundefs_ctx,
     forall sub sub' : maps_util.M.t var,
       eq_env_P (Complement _ (dead_var_fundefs_ctx fds)) sub sub' ->
       rename_all_fun_ctx_ns sub fds = rename_all_fun_ctx_ns sub' fds).
  Proof.
    exp_fundefs_ctx_induction IHc IHfdc; intros; simpl; auto.
    - erewrite IHc.
      erewrite eq_P_apply_r_list.
      auto.
      intro; intro; apply H; intro.
      inv H1; pi0.
      apply not_occur_list in H1. auto.
      intro; intro; apply H; intro.
      inv H1; pi0. auto.
    - erewrite IHc.
      erewrite eq_P_apply_r.
      auto.
      intro; intro; apply H; intro; inv H1; pi0. inv H0; auto.
      intro; intro; apply H; intro; inv H1; pi0; auto.
    - erewrite IHc.
      erewrite eq_P_apply_r_list.
      auto.
      intro; intro; apply H; intro.
      inv H1; pi0.
      apply not_occur_list in H1. auto.
      intro; intro; apply H; intro.
      inv H1; pi0. auto.
    - assert (rename_all_ns sub (Ecase v l) = rename_all_ns sub' (Ecase v l)).
      erewrite (proj1 eq_P_rename_all_ns).
      reflexivity.
      intro; intro; apply H; intro. inv H1; pi0. apply H0.
      eapply num_occur_n.
      constructor; eauto.
      simpl. destruct (cps_util.var_dec x v); eauto. exfalso; auto.
      assert (rename_all_ns sub (Ecase v l0) = rename_all_ns sub' (Ecase v l0)).
      erewrite (proj1 eq_P_rename_all_ns).
      reflexivity.
      intro; intro; apply H; intro. inv H2; pi0. apply H1.
      eapply num_occur_n.
      constructor; eauto.
      simpl. destruct (cps_util.var_dec x v); eauto. exfalso; auto.
      simpl in *. inv H0; inv H1.
      erewrite IHc. reflexivity.
      intro; intro; apply H; intro.
      inv H1; pi0; auto.        
    - erewrite IHc.
      erewrite (proj2 eq_P_rename_all_ns).
      auto.
      intro; intro; apply H; intro; inv H1; pi0; auto.
      intro; intro; apply H; intro; inv H1; pi0; auto.
    - erewrite IHfdc.
      erewrite (proj1 eq_P_rename_all_ns).
      auto.
      intro; intro; apply H; intro; inv H1; pi0; auto.
      intro; intro; apply H; intro; inv H1; pi0; auto.
    - erewrite IHc.
      erewrite (proj2 eq_P_rename_all_ns).
      auto.
      intro; intro; apply H; intro; inv H1; pi0; auto.
      intro; intro; apply H; intro; inv H1; pi0; auto.
    - erewrite IHfdc.
      erewrite (proj1 eq_P_rename_all_ns).
      auto.
      intro; intro; apply H; intro; inv H1; pi0; auto.
      intro; intro; apply H; intro; inv H1; pi0; auto.
  Qed.

  Theorem eq_P_set_list_not_in:
    forall {A} (rho:M.t A) l l',
      eq_env_P (Complement _ (FromList l)) (set_list (combine l l') rho) rho.
  Proof.            
    induction l.
    - intros; intro; intros. simpl. reflexivity.
    - intros l' x Hl.
      simpl. destruct l'.
      simpl; auto.
      simpl.
      rewrite M.gso. apply IHl. intro; apply Hl. constructor 2. auto.
      intro; apply Hl; subst.
      constructor. auto.
  Qed.
  



  
  Theorem cmap_view_case:
    forall sub c x cl1 c0 cl2,
      cmap_view_ctx sub c -> 
      cmap_view_ctx sub (comp_ctx_f c (Ecase_c x cl1 c0 Hole_c cl2)).
  Proof.
    intros.
    split; intros; split; intros.
    - apply H in H0.
      destructAll.
      eexists; eexists; eauto.
      rewrite comp_ctx_f_assoc.
      simpl.
      reflexivity.
    - destructAll.
      destruct H.
      apply H.
      exists x1.
      apply comp_ctx_split in H0.
      destruct H0.
      + destructAll.
        destruct x3; inv H0.
        eexists; eauto.
      + destructAll.
        destruct x4; inv H3.
        destruct x4; inv H6.
    - apply H in H0.
      destructAll.
      eexists; eexists; eexists; eexists.
      rewrite comp_ctx_f_assoc.
      simpl.
      reflexivity.
    - destructAll.
      destruct H.
      apply H1.
      exists x0.
      apply comp_ctx_split in H0.
      destruct H0.
      + destructAll.
        destruct x4; inv H0.
        exists x4, x2, x3; auto.
      + destructAll.
        destruct x5; inv H3.
        destruct x5; inv H6.
  Qed.

  
  Fixpoint fundefs_ctx_append B1 B2:=
    match B1 with
      | Fcons f t xs xe B => Fcons2_c f t xs xe (fundefs_ctx_append B B2)
      | Fnil => B2
    end.


  Lemma bound_stem_fundefs_append:
    forall fc f,
      Same_set _ (bound_stem_fundefs_ctx (fundefs_ctx_append f fc)) 
               (bound_stem_fundefs_ctx fc).
  Proof.
    induction f. simpl.
    rewrite bound_stem_Fcons2_c. auto.
    simpl. reflexivity.
  Qed.
  
  Theorem fundex_ctx_comp_f_ctx:
    forall fds1 f1 c v f l fds2,
      fundefs_ctx_append fds1 (Fcons1_c v f l Hole_c fds2) =
      comp_f_ctx_f f1 c ->
      c = Hole_c.
  Proof.
    induction fds1; intros.
    -  simpl in H.
       destruct f1; inv H.
       apply IHfds1 in H5. auto.
    - simpl in H.
      destruct f1; inv H.
      destruct e; inv H4. simpl; auto.
  Qed.
  
  Theorem cmap_view_efun2:
    forall sub c fds1 fds2 v f l e,
      cmap_view_ctx sub c -> 
      cmap_view_ctx sub
                    (comp_ctx_f c
                                (Efun2_c (fundefs_ctx_append fds1                                  
                                                             (Fcons1_c v f l Hole_c fds2)) e)).
  Proof.
    intros. split; intros; split; intros.
    - apply H in H0.
      destructAll.
      exists x0.
      exists (comp_ctx_f x1 (Efun2_c (fundefs_ctx_append fds1 (Fcons1_c v f l Hole_c fds2)) e)).
      rewrite comp_ctx_f_assoc.
      simpl. auto.
    - apply H.
      destructAll.
      apply comp_ctx_split in H0.
      destruct H0.
      + destructAll.
        destruct x2; inv H0.
        eauto.
      + destructAll.
        destruct x3; inv H2.
        apply fundex_ctx_comp_f_ctx in H1.
        inv H1.
    - apply H in H0.
      destructAll.
      exists x.
      exists (comp_ctx_f x0 (Efun2_c (fundefs_ctx_append fds1 (Fcons1_c v f l Hole_c fds2)) e)).
      exists x1, x2.
      rewrite comp_ctx_f_assoc.
      auto. 
    - apply H.
      destructAll.
      apply comp_ctx_split in H0.
      destruct H0.
      + destructAll.
        destruct x3; inv H0.
        eauto.
      + destructAll.
        destruct x4; inv H2.
        apply fundex_ctx_comp_f_ctx in H1.
        inv H1.
  Qed.      

  
  Theorem cmap_view_constr:
  forall {sub c} x t xs, 
    cmap_view_ctx sub c ->
    M.get x sub = None ->
    cmap_view_ctx (M.set x (SVconstr t xs) sub) (comp_ctx_f c (Econstr_c x t xs Hole_c)).
  Proof.
    intros; split; intros; split; intros.
    - destruct (var_dec x0 x).
      + exists c, Hole_c.
        subst.
        rewrite M.gss in H1. inv H1. auto.
      + rewrite M.gso in H1 by auto.
        apply H in H1.
        destructAll.
        exists x1, (comp_ctx_f x2 (Econstr_c x t xs Hole_c)).
        rewrite comp_ctx_f_assoc.
        simpl. auto.
    - destructAll.
      apply comp_ctx_split in H1.
      destruct H1.
      + destructAll.
        destruct x3; inv H1.
        * rewrite M.gss. auto.
        * rewrite M.gso.
          Focus 2.
          intro.
          subst.
          destruct H. specialize (H x c l).
          assert ((exists c' c'' : exp_ctx,
                     comp_ctx_f x1 (Econstr_c x c l x3) =
                     comp_ctx_f c' (Econstr_c x c l c''))) by eauto.
          apply H in H2. rewrite H0 in H2. inv H2.
          apply H. eauto.
      + destructAll.
        destruct x4; inv H3.
        * rewrite M.gss; auto.
        * destruct x4; inv H6.
    - rewrite M.gso in H1.
      apply H in H1. destructAll.
      exists x0.
      exists (comp_ctx_f x1 (Econstr_c x t xs Hole_c)).
      rewrite comp_ctx_f_assoc. simpl. eauto.
      intro.
      subst.
      rewrite M.gss in H1. inv H1.
    - destructAll.
      rewrite M.gso.
      apply H.
      apply comp_ctx_split in H1.
      destruct H1.
      + destructAll; subst.
        destruct x4; inv H1.
        eauto.
      + destructAll. destruct x5; inv H3.
        destruct x5; inv H6.
      + intro; subst.
        apply comp_ctx_split in H1.
        destruct H1.
        * destructAll; subst.
          destruct x4; inv H1.
          destruct H.
          specialize (H1 x t0 ys e).
          assert
            (exists (c' c'' : exp_ctx) (B1 B2 : fundefs),
               comp_ctx_f x0 (Efun1_c (fundefs_append x2 (Fcons x t0 ys e x3)) x4) =
               comp_ctx_f c' (Efun1_c (fundefs_append B1 (Fcons x t0 ys e B2)) c'')) by eauto.
          apply H1 in H2. rewrite H0 in H2. inv H2.
        * destructAll.
          destruct x5; inv H3.
          destruct x5; inv H6.
  Qed.

  Theorem cmap_view_prim:
    forall sub c v p l,
      cmap_view_ctx sub c ->
      cmap_view_ctx sub (comp_ctx_f c (Eprim_c v p l Hole_c)).
  Proof.    
    intros; split; intros; split; intros.
    - apply H in H0.
      destructAll.
      eexists; eexists.
      rewrite  comp_ctx_f_assoc.
      simpl. reflexivity.
    - apply H. destructAll.
      apply comp_ctx_split in H0.
      destruct H0; destructAll.
      + destruct x2; inv H0.
        eauto.
      + destruct x3; inv H2.
        destruct x3; inv H5.
    - apply H in H0.
      destructAll.
      eexists; eexists; eexists; eexists.
      rewrite  comp_ctx_f_assoc.
      simpl. reflexivity.
    - apply H.
      destructAll.
      apply comp_ctx_split in H0.
      destruct H0; destructAll.
      + destruct x3; inv H0.
        eauto.
      + destruct x4; inv H2.
        destruct x4; inv H5.
  Qed.

  Theorem cmap_view_proj:
    forall sub c v t n v',
      cmap_view_ctx sub c ->
      cmap_view_ctx sub (comp_ctx_f c (Eproj_c v t n v' Hole_c)).
  Proof.    
    intros; split; intros; split; intros.
    - apply H in H0.
      destructAll.
      eexists; eexists.
      rewrite  comp_ctx_f_assoc.
      simpl. reflexivity.
    - apply H. destructAll.
      apply comp_ctx_split in H0.
      destruct H0; destructAll.
      + destruct x2; inv H0.
        eauto.
      + destruct x3; inv H2.
        destruct x3; inv H6.
    - apply H in H0.
      destructAll.
      eexists; eexists; eexists; eexists.
      rewrite  comp_ctx_f_assoc.
      simpl. reflexivity.
    - apply H.
      destructAll.
      apply comp_ctx_split in H0.
      destruct H0; destructAll.
      + destruct x3; inv H0.
        eauto.
      + destruct x4; inv H2.
        destruct x4; inv H6.
  Qed.

  
  Theorem cmap_view_efun1_cons:
    forall c0 c f0 v f l e,
      cmap_view_ctx c0 (comp_ctx_f c (Efun1_c f0 Hole_c)) ->
      M.get v c0 = None -> 
      cmap_view_ctx (M.set v (SVfun f l e) c0)
                    (comp_ctx_f c (Efun1_c (Fcons v f l e f0) Hole_c)).
  Proof.
    intros; split; intros; split; intros.
    - rewrite M.gso in H1. apply H in H1.
      destructAll.
      apply comp_ctx_split in H1. destruct H1.
      + destructAll. destruct x2; inv H1.
        exists x0, (comp_ctx_f x2 (Efun1_c (Fcons v f l e f0) Hole_c)).
        rewrite comp_ctx_f_assoc. auto.
      + destructAll.
        destruct x3; inv H3.
        destruct x3; inv H4.
      + intro. subst.
        rewrite M.gss in H1.
        inv H1.
    - destructAll.
      rewrite M.gso.
      apply H.
      apply comp_ctx_split in H1.
      destruct H1.
      + destructAll.
        destruct x2; inv H1.
        exists x0, (comp_ctx_f x2 (Efun1_c f0 Hole_c)).
        rewrite comp_ctx_f_assoc. auto.
      + destructAll.
        destruct x3; inv H3.
        destruct x3; inv H4.
      + intro; subst.
        apply comp_ctx_split in H1.
        destruct H1.
        * destructAll. 
          destruct x; inv H1.
          assert (exists e e', (comp_ctx_f (comp_ctx_f x0 (Econstr_c v0 c l0 x)) (Efun1_c f0 Hole_c)) = (comp_ctx_f e (Econstr_c v0 c l0 e'))).
          exists x0, (comp_ctx_f x (Efun1_c f0 Hole_c)).
          rewrite comp_ctx_f_assoc.
          auto.
          apply H in H1.
          rewrite H0 in H1. inv H1.
        * destructAll. destruct x2; inv H3.
          destruct x2; inv H4.
    - destruct (var_dec f1 v).
      + subst. rewrite M.gss in H1.
        inv H1.
        exists  c, Hole_c, Fnil, f0.
        simpl. auto.
      + rewrite M.gso in H1 by auto.
        apply H in H1. destructAll.
        apply comp_ctx_split in H1.
        destruct H1.
        * destructAll.
          destruct x3; inv H1.
          exists  (comp_ctx_f x Hole_c), Hole_c, (Fcons v f l e x1), x2.
          auto.
          exists x, (comp_ctx_f x3 (Efun1_c (Fcons v f l e f0) Hole_c)), x1, x2.
          rewrite comp_ctx_f_assoc. auto.
        * destructAll.
          destruct x4; inv H3.
          exists x3, Hole_c, (Fcons v f l e x1), x2. auto.
          destruct x4; inv H4.
    - destructAll.
      apply comp_ctx_split in H1.
      destruct H1.
      + destructAll.
        destruct x3; inv H1.
        * destruct x1; inv H3.
          rewrite M.gso.
          apply H. exists (comp_ctx_f x Hole_c), Hole_c, x1, x2.
          auto.
          intro; subst.
          assert (exists g1 g2 B1 B2, (comp_ctx_f (comp_ctx_f x Hole_c)
                                                  (Efun1_c (fundefs_append x1 (Fcons v t ys e0 x2)) Hole_c)) =
                                      comp_ctx_f g1 (Efun1_c (fundefs_append B1 (Fcons v t ys e0 B2)) g2)).
          eauto.
          apply H in H1. rewrite H0 in H1. inv H1.
          rewrite M.gss. auto.
        * assert (M.get f1 c0 = Some (SVfun t ys e0)).
          apply H.
          exists x, (comp_ctx_f x3 (Efun1_c f0 Hole_c)), x1, x2.
          rewrite comp_ctx_f_assoc.
          auto.
          destruct (var_dec f1 v).
          subst.
          rewrite H1 in H0.
          inv H0.
          rewrite M.gso; auto.
      + destructAll.
        destruct x4; inv H3.
        * destruct x1; inv H2.
          assert (M.get f1 c0 = Some (SVfun t ys e0)).
          apply H.
          exists x3, Hole_c, x1, x2.
          auto.
          destruct (var_dec f1 v0).
          subst. rewrite H1 in H0. inv H0.
          rewrite M.gso; auto.
          rewrite M.gss. auto.
        * destruct x4; inv H4.
  Qed.
  
  Theorem cmap_view_efun1_nil:
    forall sub c,
      cmap_view_ctx sub c ->
      cmap_view_ctx sub (comp_ctx_f c (Efun1_c Fnil Hole_c)).
  Proof.
    intros. split; intros; split; intros.
    - apply H in H0.
      destructAll.
      eexists x0, (comp_ctx_f x1 (Efun1_c Fnil Hole_c)).
      rewrite comp_ctx_f_assoc. auto.
    - apply H. destructAll.
      apply comp_ctx_split in H0.
      destruct H0.
      + destructAll. destruct x2; inv H0.
        eauto.
      + destructAll. destruct x3; inv H2. destruct x3; inv H3.
    - apply H in H0.
      destructAll.
      exists x, (comp_ctx_f x0 (Efun1_c Fnil Hole_c)), x1, x2.
      rewrite comp_ctx_f_assoc; auto.
    - apply H. destructAll.
      apply comp_ctx_split in H0.
      destruct H0.
      + destructAll.
        destruct x3; inv H0.
        * destruct x1; inv H2.
        * eauto.
      + destructAll.
        destruct x4; inv H2.
        destruct x1; inv H1.
        destruct x4; inv H3.
  Qed.
  

  Theorem bound_var_ctx_rename_all_ns:
    forall sigma, 
      (forall (c : exp_ctx),
         bound_var_ctx c <--> bound_var_ctx (rename_all_ctx_ns sigma c)) /\
      (forall (fdc : fundefs_ctx),
         bound_var_fundefs_ctx fdc <--> bound_var_fundefs_ctx (rename_all_fun_ctx_ns sigma fdc)).
  Proof.
    intro sig.
    assert (Hcc := bound_var_rename_all_ns_mut).
    specialize (Hcc sig).
    destruct Hcc.               
    exp_fundefs_ctx_induction IHc IHfdc; intros; simpl; repeat (first [normalize_bound_var_ctx|normalize_bound_var]); split; try (rewrite IHc); try (rewrite IHfdc); try (rewrite <- H); try (rewrite <- H0); auto with Ensembles_DB.
    rewrite H.
    simpl.
    rewrite H with (e := (Ecase v l0)).
    simpl.
    eauto with Ensembles_DB.
    rewrite H with (e:= (Ecase v l)).
    simpl.
    rewrite H with (e := (Ecase v l0)).
    simpl.
    eauto with Ensembles_DB.
  Qed.


  Theorem name_in_fundefs_ctx_rename_all_ns:
    forall sig f,
      names_in_fundefs_ctx f <--> names_in_fundefs_ctx (rename_all_fun_ctx_ns sig f).
  Proof.
    induction f; simpl; eauto with Ensembles_DB.
    rewrite name_in_fundefs_rename_all_ns. reflexivity. 
  Qed.

  
  Theorem bound_stem_ctx_rename_all_ns:
    forall sigma, 
      (forall (c : exp_ctx),
         bound_stem_ctx c <--> bound_stem_ctx (rename_all_ctx_ns sigma c)) /\
      (forall (fdc : fundefs_ctx),
         bound_stem_fundefs_ctx fdc <--> bound_stem_fundefs_ctx (rename_all_fun_ctx_ns sigma fdc)).
  Proof.
    intro sig.
    exp_fundefs_ctx_induction IHc IHfdc; intros; simpl; repeat (first [normalize_bound_stem_ctx'|normalize_bound_stem_ctx_in_ctx']); split; try (rewrite IHc); try (rewrite IHfdc); try (rewrite <- H); try (rewrite <- H0); try (rewrite <- name_in_fundefs_rename_all_ns); try (rewrite <- name_in_fundefs_ctx_rename_all_ns); auto with Ensembles_DB.
  Qed.
  
  Theorem cmap_view_bound_in_ctx:
    forall sub c v s,
      cmap_view_ctx sub c ->
      M.get v sub = Some s ->
      bound_var_ctx c v.
  Proof.
    intros. destruct s; apply H in H0; destructAll.
    - apply bound_var_ctx_comp_ctx.
      right; auto.
    - apply bound_var_ctx_comp_ctx.
      right.
      constructor.
      eapply fundefs_append_bound_vars.
      reflexivity.
      right; auto.
  Qed.

  Theorem InList_snd:
    forall {A B} (x:A) (l:list (B*A)),
      List.In x (map snd l) <-> exists v, List.In (v, x) l.
  Proof.
    induction l; intros.
    - split; intro H; inv H.
      inv H0.
    - split.
      + intro. destruct a.
        simpl in H. inv H.
        exists b; constructor; auto.
        apply IHl in H0. inv H0. exists x0.
        constructor 2. auto.
      + intro. inv H.
        destruct a. simpl.
        inv H0.
        inv H; auto.
        right.
        apply IHl; eauto.
  Qed.                
  
  Theorem Decidable_Range_map:
    forall sig, @Decidable var (Range_map sig).
  Proof.
    intros. constructor.
    intro.
    assert (Decidable (FromList (map snd (M.elements sig)))).
    apply Decidable_FromList.
    inv H.
    specialize (Dec x).
    inv Dec.
    unfold FromList in H.
    rewrite InList_snd in H.
    destruct H.
    apply M.elements_complete in H.
    left. exists x0; auto.
    right. intro. inv H0.
    apply H.
    apply InList_snd.
    exists x0. apply M.elements_correct. auto.
  Qed.

  (* Variables are bound by (1) binding on the stem (2) mutually rec. functions *)
  Theorem occurs_free_app_bound_stem x e:        
    occurs_free e x ->
    ( forall c,
        ~ occurs_free (c |[e]|) x ->
        bound_stem_ctx c x) /\
    ( forall fds,
        ~ occurs_free_fundefs (fds <[e]>) x ->
        bound_stem_fundefs_ctx fds x \/ names_in_fundefs_ctx fds x).
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
      auto.
      apply SBound_Fun12_c. apply H0. intro.
      apply H1.
      apply Free_Efun1; auto.
    + simpl in H1.
      assert (Hv := Decidable_name_in_fundefs_ctx f5).
      inv Hv. specialize (Dec x). inv Dec.
      constructor; auto.
      apply SBound_Fun2_c.
      assert (~ occurs_free_fundefs (f5 <[ e ]>) x).
      intro.
      apply H1.
      apply Free_Efun2.
      auto. apply H0 in H3. inv H3. auto.
      exfalso. auto.
    + simpl in H1.
      assert (Hv := Decidable_name_in_fundefs (Fcons v t l (e0 |[ e ]|) f6)).
      destruct Hv. specialize (Dec x). destruct Dec.
      right.              
      eapply name_in_fundefs_ctx_ctx with (e := e). eauto.
      left.
      assert (Hl := Decidable_FromList l).
      inv Hl. specialize (Dec x). inv Dec. 
      constructor. auto.
      apply SBound_Fcons12_c. apply H0. intro. apply H1.
      constructor; auto. intro. apply H2. subst; constructor.
      constructor.
      intro; apply H2. constructor 2. auto.
    + simpl in H1.
      assert (Hv := Decidable_name_in_fundefs (Fcons v t l e0 (f7 <[ e ]>))).
      destruct Hv. specialize (Dec x). destruct Dec.
      right.
      eapply name_in_fundefs_ctx_ctx. eauto.
      left.
      constructor.
      assert ( ~ occurs_free_fundefs (f7 <[ e ]>) x).
      intro; apply H1.
      constructor 2. auto.
      intro. apply H2. subst; constructor; auto.
      apply H0 in H3. inv H3; auto.
      exfalso. apply H2.
      simpl. right.
      eapply name_in_fundefs_ctx_ctx. eauto.
  Qed.

  (* TODO: move to identifier *)
  Theorem ub_comp_ctx_f :
    forall c' : exp_ctx,
      (forall c : exp_ctx,
         unique_bindings_c (comp_ctx_f c c') <->
         unique_bindings_c c /\
         unique_bindings_c c' /\ Disjoint var (bound_var_ctx c) (bound_var_ctx c')) /\
      (forall fds : fundefs_ctx,
         unique_bindings_fundefs_c (comp_f_ctx_f fds c') <->
         unique_bindings_fundefs_c fds /\
         unique_bindings_c c' /\ Disjoint var (bound_var_fundefs_ctx fds) (bound_var_ctx c')).
  Proof.
    intros c'.
    exp_fundefs_ctx_induction IHc IHfdc; intros; simpl; repeat normalize_bound_var_ctx.
    (* Hole *)
    - split; intros.
      split. constructor. split; auto. eauto with Ensembles_DB.
      destructAll; auto.
    (* Constr *)
    - split; intros.
      + inv H. apply IHc in H5. destructAll.
        split; auto. constructor. intro. apply H2.
        apply bound_var_ctx_comp_ctx.  auto.
        auto.
        split; auto.
        apply Union_Disjoint_l. auto.
        split. intro. intro. inv H3. inv H4.
        apply H2.
        apply bound_var_ctx_comp_ctx.  auto.      
      + destructAll.
        constructor.  intro. apply bound_var_ctx_comp_ctx in H2. inv H2.
        inv H. apply H5. auto.
        inv H1. specialize (H2 v).
        apply H2. split; auto.
        apply IHc. inv H. split; auto. split; auto.
        eapply Disjoint_Included_l. 2: apply H1. auto with Ensembles_DB.
    (* Proj *)
    - split; intros.
      + inv H. apply IHc in H6. destructAll.
        split; auto. constructor. intro. apply H2.
        apply bound_var_ctx_comp_ctx.  auto.
        auto.
        split; auto.
        apply Union_Disjoint_l. auto.
        split. intro. intro. inv H3. inv H4.
        apply H2.
        apply bound_var_ctx_comp_ctx.  auto.      
      + destructAll.
        constructor.  intro. apply bound_var_ctx_comp_ctx in H2. inv H2.
        inv H. apply H5. auto.
        inv H1. specialize (H2 v).
        apply H2. split; auto.
        apply IHc. inv H. split; auto. split; auto.
        eapply Disjoint_Included_l. 2: apply H1. auto with Ensembles_DB.
    - split; intros.
      + inv H. apply IHc in H5. destructAll.
        split; auto. constructor. intro. apply H2.
        apply bound_var_ctx_comp_ctx.  auto.
        auto.
        split; auto.
        apply Union_Disjoint_l. auto.
        split. intro. intro. inv H3. inv H4.
        apply H2.
        apply bound_var_ctx_comp_ctx.  auto.      
      + destructAll.
        constructor.  intro. apply bound_var_ctx_comp_ctx in H2. inv H2.
        inv H. apply H5. auto.
        inv H1. specialize (H2 v).
        apply H2. split; auto.
        apply IHc. inv H. split; auto. split; auto.
        eapply Disjoint_Included_l. 2: apply H1. auto with Ensembles_DB.
    (* case *)
    -  split; intros.
       + inv H. apply IHc in H6. destructAll.
         split. constructor; auto. eapply Disjoint_Included_l.
         2: apply H7. intro; intro. apply bound_var_ctx_comp_ctx. auto.
         split; auto.
         apply Union_Disjoint_l.
         split; intro; intro. inv H2. inv H7. specialize (H2 x).
         apply H2. split. apply bound_var_ctx_comp_ctx; auto.
         apply bound_var_Ecase_app. auto.
         apply Union_Disjoint_l.
         auto. 
         split; intro; intro. inv H2. inv H7. specialize (H2 x).
         apply H2. split. apply bound_var_ctx_comp_ctx; auto.
         apply bound_var_Ecase_app. auto.
       + destructAll.
         inv H.
         constructor; auto.
         apply IHc. split; auto. split; auto.
         eapply Disjoint_Included_l. 2: apply H1.
         eauto with Ensembles_DB.
         split.
         intros. intro. inv H. apply bound_var_ctx_comp_ctx in H2.
         inv H2. inv H9. specialize (H2 x). apply H2.
         split; auto.
         inv H1. specialize (H2 x). apply H2. split; auto.
         apply bound_var_Ecase_app in H3. inv H3; auto.
    (* Efun1_c *)
    - split; intros.
      + inv H. apply IHc in H2. destructAll.
        split. constructor; auto.
        eapply Disjoint_Included_l. 2: apply H4.
        intro; intros; apply bound_var_ctx_comp_ctx; auto.
        split; auto.
        apply Disjoint_sym.  apply Union_Disjoint_r.
        eapply Disjoint_Included_l. 2: apply H4.
        intro; intros; apply bound_var_ctx_comp_ctx; auto.
        apply Disjoint_sym; auto.
      + destructAll. inv H. constructor. apply IHc.
        split; auto. split; auto.
        eapply Disjoint_Included_l. 2: apply H1.
        auto with Ensembles_DB.
        auto.
        split. intro. intro. inv H.
        apply bound_var_ctx_comp_ctx in H2. inv H2.
        inv H6. specialize (H2 x). apply H2; auto.
        inv H1. specialize (H2 x). apply H2; auto.
    (* Efun2_c *)
    - split; intros.
      + inv H. apply IHfdc in H3. destructAll. split.
        constructor; auto. eapply Disjoint_Included_r.
        2: apply H4.
        intro. intros. apply bound_var_ctx_comp_ctx. auto.
        split; auto.
        apply Union_Disjoint_l. auto.
        eapply Disjoint_Included_r.
        2: apply H4.
        intro. intros. apply bound_var_ctx_comp_ctx. auto.
      + destructAll. inv H.
        constructor; auto.
        apply IHfdc. split; auto. split; auto.
        eapply Disjoint_Included_l. 2: apply H1.
        auto with Ensembles_DB.
        split. intro; intro.
        inv H. apply bound_var_ctx_comp_ctx in H3. inv H3.
        inv H6. specialize (H3 x). apply H3. auto.
        inv H1. specialize (H3 x). apply H3. split; auto.
    (* Fcons1 *)
    - split; intros.
      + inv H.
        apply IHc in H12.
        destructAll. split.
        constructor; auto.
        intro; apply H5.
        apply bound_var_ctx_comp_ctx; auto.
        eapply Disjoint_Included_l. 2: apply H7.
        intro; intros. apply bound_var_ctx_comp_ctx. auto.
        eapply Disjoint_Included_l. 2: apply H9.
        intro; intros. apply bound_var_ctx_comp_ctx; auto.
        split; auto. repeat eapply Union_Disjoint_l; eauto.
        split. intro. intro. apply H5. inv H2.
        inv H3.
        apply bound_var_ctx_comp_ctx; auto.
        apply Disjoint_sym.
        eapply Disjoint_Included_l. 2: apply H7.
        intro; intros. apply bound_var_ctx_comp_ctx; auto.
        apply Disjoint_sym.
        eapply Disjoint_Included_l. 2: apply H9.
        intro; intros. apply bound_var_ctx_comp_ctx; auto.
      + destructAll.
        inv H. constructor; eauto.
        intro.
        apply bound_var_ctx_comp_ctx in H.
        inv H. apply H7; auto.
        inv H1. specialize (H v). apply H. split; auto.
        split. intro. intro. inv H. apply bound_var_ctx_comp_ctx in H2.
        inv H2.
        inv H9. specialize (H2 x). apply H2. split; auto.
        inv H1. specialize (H2 x). apply H2.
        split. right; auto. auto.
        split; intro; intro. inv H.
        apply bound_var_ctx_comp_ctx in H2. inv H2. inv H11. specialize (H2 x); auto.
        inv H1. specialize (H2 x); apply H2. split; auto.
        apply IHc.
        split; auto. split; auto. eapply Disjoint_Included_l.
        2: apply H1.
        eauto with Ensembles_DB.
    (* Fcons2 *)
    - split; intro.
      + inv H. apply IHfdc in H13. destructAll.
        split. constructor; auto.
        intro; apply H6. apply bound_var_ctx_comp_ctx.
        auto.
        eapply Disjoint_Included_l. 2: apply H8.
        intro; intro. apply bound_var_ctx_comp_ctx; auto.
        eapply Disjoint_Included_r. 2: apply H9.
        intro; intro. apply bound_var_ctx_comp_ctx; auto.
        split; auto. split. intro. intro. inv H2. inv H3.
        apply H6. inv H2. apply bound_var_ctx_comp_ctx; auto.
        inv H2.
        inv H8. specialize (H2 x). apply H2. split; auto.
        apply bound_var_ctx_comp_ctx; auto.
        inv H3.
        inv H9. specialize (H3 x). apply H3. split; auto.
        apply bound_var_ctx_comp_ctx; auto.
        inv H1. specialize (H3 x). apply H3; split; auto.
      + destructAll. inv H.
        constructor; auto. intro.
        apply bound_var_ctx_comp_ctx in H.
        inv H. auto.
        inv H1. specialize (H v). apply H. split; auto.
        split. intro; intro. inv H.
        apply bound_var_ctx_comp_ctx in H2. inv H2.
        inv H10. specialize (H2 x). apply H2; auto.
        inv H1. specialize (H2 x). apply H2; auto.
        split; intro; intro. inv H.
        apply bound_var_ctx_comp_ctx in H3. inv H3.
        inv H11. specialize (H3 x). apply H3; auto.
        inv H1. specialize (H3 x). apply H3. split. auto. auto.
        apply IHfdc.
        split; auto. split; auto. eapply Disjoint_Included_l.
        2: apply H1. auto with Ensembles_DB.
  Qed.

  Theorem inlined_fundefs_f_staged:
    forall x im f4,
      (inlined_fundefs_f f4 (M.set x true im)) =
      (inlined_fundefs_f (inlined_fundefs_f f4 im) (M.set x true (M.empty bool))).
  Proof.  
    induction f4; simpl; try rewrite IHf4; auto.
    destruct (var_dec v x).
    - subst.
      unfold get_b.
      rewrite M.gss.
      destruct (M.get x im). destruct b.
      auto.
      simpl. unfold get_b.
      rewrite M.gss. auto.
      simpl. unfold get_b. rewrite M.gss.
      auto.
    - unfold get_b. rewrite M.gso.
      destruct (M.get v im).  destruct b. auto.
      simpl. unfold get_b. rewrite M.gso. rewrite M.gempty.
      auto. auto.
      simpl. unfold get_b. rewrite M.gso; auto.
      rewrite M.gempty; auto. auto.
  Qed.
  
  Theorem inlined_ctx_f_staged_mut:
    forall x  im,
      (forall c,
         inlined_ctx_f c (M.set x true im) =
         inlined_ctx_f (inlined_ctx_f c im) (M.set x true (M.empty bool))) /\
      ( forall fc,
          inlined_fundefs_ctx_f fc (M.set x true im) =
          inlined_fundefs_ctx_f (inlined_fundefs_ctx_f fc im) (M.set x true (M.empty bool))).
  Proof.
    intros x im.
    apply exp_fundefs_ctx_mutual_ind; simpl; intros; try rewrite H; auto .
    rewrite <- inlined_fundefs_f_staged. auto.
  Qed.

  Theorem inlined_ctx_f_staged:
    forall x  im,
      (forall c,
         inlined_ctx_f c (M.set x true im) =
         inlined_ctx_f (inlined_ctx_f c im) (M.set x true (M.empty bool))).        
  Proof.
    intros.
    apply inlined_ctx_f_staged_mut.
  Qed.

  Theorem inlined_fundefs_ctx_f_staged:
    forall x im,
      ( forall fc,
          inlined_fundefs_ctx_f fc (M.set x true im) =
          inlined_fundefs_ctx_f (inlined_fundefs_ctx_f fc im) (M.set x true (M.empty bool))).
  Proof.
    intros.
    apply inlined_ctx_f_staged_mut.
  Qed.

  (** precontractfun returns a subset of the current fundefs related to the original term by Fun_rem_s *) 
  Theorem precontractfun_corresp:
    forall fds_c fds e c im sub count sig,
      let ce := (app_ctx_f (rename_all_ctx_ns sig (inlined_ctx_f c im)) (rename_all_ns sig (Efun (fundefs_append fds fds_c) e))) in
      unique_bindings ce ->
      closed ce ->
      c_count ce count ->
      cmap_view_ctx sub c ->
      inl_inv im sub ce ->
      sig_inv_full sig (rename_all_ctx_ns sig (inlined_ctx_f c im)) (rename_all_ns sig (Efun (fundefs_append fds fds_c) e)) ->
      forall fds_c' count' sub',
        precontractfun sig count sub fds_c = (fds_c', count', sub') ->
        let ce' := (app_ctx_f (rename_all_ctx_ns sig (inlined_ctx_f c im)) (rename_all_ns sig (Efun (fundefs_append fds fds_c') e))) in
        gsr_clos ce ce' /\ c_count ce' count' /\ inl_inv im sub' ce' /\
        cmap_view_ctx sub' (comp_ctx_f c (Efun1_c fds_c' Hole_c)) /\
        sig_inv_full sig (rename_all_ctx_ns sig (inlined_ctx_f c im)) (rename_all_ns sig (Efun (fundefs_append fds fds_c') e)).
  Proof.
    induction fds_c; intros.
    - simpl in H5.
      destruct (get_c v count) eqn:gvc.
      +  assert (H1v := H1 v).
         rewrite gvc in H1v.
         assert (gsr_clos ce
                          (rename_all_ctx_ns sig (inlined_ctx_f c im)
                          |[ rename_all_ns sig
                                           (Efun (fundefs_append fds fds_c) e0) ]|)).
         { constructor.
           constructor.             
           simpl.
           rewrite rename_all_ns_fundefs_append.
           rewrite rename_all_ns_fundefs_append.
           simpl.
           apply Fun_rem_s.
           specialize (H1 v).
           rewrite gvc in H1.
           unfold ce in H1.
           apply num_occur_app_ctx in H1. destructAll; pi0.
           simpl in H6.
           rewrite rename_all_ns_fundefs_append in H6.
           simpl in H6. auto.
         }             
         assert (Hub' := gsr_preserves_clos _ _ H H0 H6).
         destruct Hub'.
         assert (H4' := H4).
         apply sig_inv_combine in H4.
         destruct H4 as (H4dom, H4co).           
         assert (Hse := gsr_preserves_sig_dom _ _ _ H H0 H6 H4dom).           
         eapply IHfds_c with (fds := fds) (e := e0) (c := c) (im := im) in H5; eauto.
         destructAll.
         unfold ce'.
         split.
         eapply rt_trans.
         apply H6.
         auto.
         split; auto.
         {
           intro.
           specialize (H1 v0).
           unfold ce in H1.
           apply num_occur_app_ctx in H1.
           destructAll.
           simpl in H4. inv H4.
           rewrite rename_all_ns_fundefs_append in H15.
           apply fundefs_append_num_occur' in H15.
           destructAll.
           simpl in H10.
           inv H10.
           eapply num_occur_n.
           apply num_occur_app_ctx.
           exists x, (n+(x0 + m)).
           split; auto.
           split.
           simpl.
           constructor; auto.
           rewrite rename_all_ns_fundefs_append.
           eapply fundefs_append_num_occur.
           reflexivity.
           auto. auto.
           reflexivity.
           symmetry.
           unfold dec_census.
           assert  (Hcc := combine_minus_census_correct).
           destruct Hcc.
           specialize (H10 e count sig). rewrite <- H10.
           rewrite gccombine_sub.
           rewrite H9.
           assert (c_count (rename_all_ns sig e) (init_census (rename_all_ns sig e))) by apply init_census_correct.
           assert (n0 =  get_c v0 (init_census (rename_all_ns sig e))).
           eapply (proj1 (num_occur_det v0)); eauto.             
           omega.
         }
         {
           intro.
           intros.
           apply H3 in H4.
           destruct H4.
           split; [| split].
           - intro.
             apply H4.
             unfold ce.
             apply bound_var_app_ctx in H10.
             apply bound_var_app_ctx.
             inv H10; auto.
             right.
             apply bound_var_rename_all_ns.
             apply bound_var_rename_all_ns in H11.
             normalize_bound_var.
             rewrite bound_var_Efun in H11.
             inv H11; auto.
             left.
             rewrite fundefs_append_bound_vars.
             2: reflexivity.
             rewrite fundefs_append_bound_vars in H10.
             2: reflexivity.
             rewrite bound_var_fundefs_Fcons.
             inv H10; auto.
           - apply H9 in H10.
             unfold ce in H10.
             intro. intro.
             inv H10.
             specialize (H12 x).
             apply H12.
             inv H11. split; auto.
             rewrite bound_var_app_ctx in H10.
             rewrite bound_var_app_ctx.
             inv H10; auto.
             right.
             apply bound_var_rename_all_ns.
             apply bound_var_rename_all_ns in H11.
             normalize_bound_var.
             rewrite bound_var_Efun in H11.
             inv H11; auto.
             left.
             rewrite fundefs_append_bound_vars.
             2: reflexivity.
             rewrite fundefs_append_bound_vars in H10.
             2: reflexivity.
             rewrite bound_var_fundefs_Fcons.
             inv H10; auto.               
         }
         apply sig_inv_combine.
         split; auto.
         intro.
         intros.
         apply H4' in H4.
         inv H4. inv H10; auto.
         left.
         apply num_occur_app_ctx in H4.
         destructAll; pi0.
         simpl in H10.
         rewrite rename_all_ns_fundefs_append in H10.
         inv H10.
         apply fundefs_append_num_occur' in H16; destructAll.
         inv H11; pi0.
         simpl.
         apply num_occur_app_ctx.
         exists 0, 0.
         split; auto.
         split; auto.
         eapply num_occur_n.
         constructor; eauto.
         rewrite rename_all_ns_fundefs_append.
         eapply fundefs_append_num_occur.
         reflexivity.
         eauto. eauto.
         auto.           
      +  assert (rename_all_ctx_ns sig (inlined_ctx_f c im)
                |[ rename_all_ns sig
                                 (Efun (fundefs_append fds (Fcons v f l e fds_c)) e0) ]| =
                                                                                         rename_all_ctx_ns sig (inlined_ctx_f c im)
                |[ rename_all_ns sig
                                 (Efun (fundefs_append (fundefs_append fds (Fcons v f l e Fnil)) fds_c) e0) ]|) by 
            (rewrite <- fundefs_append_assoc; reflexivity).
         unfold ce in IHfds_c.
         fold ce in H6. rewrite H6 in *.
         destruct  (precontractfun sig count sub fds_c ) eqn:prefun.
         destruct p.
         assert (Hff : (fundefs_append fds (Fcons v f l e fds_c)) =
                       (fundefs_append (fundefs_append fds (Fcons v f l e Fnil))
                                       fds_c)).
         rewrite <- fundefs_append_assoc. simpl. auto.
         rewrite Hff in H4.
         specialize (IHfds_c  _ _ _ _ _ _ _ H H0 H1 H2 H3 H4 _ _ _ prefun).
         inv H5.
         assert (rename_all_ctx_ns sig (inlined_ctx_f c im)
                |[ rename_all_ns sig (Efun (fundefs_append fds (Fcons v f l e f0)) e0)
                 ]| =
                    rename_all_ctx_ns sig (inlined_ctx_f c im)
                |[ rename_all_ns sig (Efun (fundefs_append (fundefs_append fds (Fcons v f l e Fnil))  f0) e0)
                 ]|).
         rewrite <-fundefs_append_assoc; reflexivity.          
         unfold ce'.
         rewrite H5.
         destructAll.
         split; auto.
         split; auto.
         split; auto.
         clear H10.
         intro. intro. apply H9 in H10.          
         destruct H10.
         split; auto.
         
         intros.
         destruct (var_dec f1 v).
         * subst.
           exfalso.
           apply H10.
           apply bound_var_app_ctx.
           right.
           rewrite <- bound_var_rename_all_ns.
           rewrite bound_var_Efun.
           left.
           rewrite fundefs_append_bound_vars.
           2: reflexivity.
           left.
           rewrite fundefs_append_bound_vars.
           2: reflexivity.
           right.
           rewrite bound_var_fundefs_Fcons.
           left; auto.
         * rewrite M.gso in H13.
           apply H12 in H13.
           auto. auto.
         * split. apply cmap_view_efun1_cons. apply H10.
           
           (* due to unique binding *)

           apply (gsr_preserves_clos _ _ H H0) in H7.
           destruct H7.
           destruct (M.get v c0) eqn:gvc0.
           2: auto.

           assert (bound_var_ctx (comp_ctx_f c (Efun1_c f0 Hole_c)) v).
           eapply cmap_view_bound_in_ctx; eauto.                      

           apply bound_var_ctx_comp_ctx in H13.
           apply ub_app_ctx_f in H7.
           destructAll.
           exfalso.
           inv H13.
           {
             inv H15.
             specialize (H13 v).
             apply H13.
             split.
             apply bound_var_ctx_rename_all_ns.
             {
               destruct s.
               - apply H10 in gvc0. destructAll.
                 apply comp_ctx_split in H15.
                 destruct H15.
                 + destructAll.
                   destruct x1; inv H15.
                   rewrite (proj1 inlined_comp_ctx).
                   simpl.                            
                   apply bound_var_ctx_comp_ctx.
                   right; auto.
                 + destructAll. destruct x2; inv H18. destruct x2; inv H19.
               - assert (gvc0' := gvc0).
                 apply H10 in gvc0. destructAll.
                 apply comp_ctx_split in H15.
                 destruct H15.
                 + destructAll.
                   destruct x3; inv H15.
                   * simpl in H14.
                     inv H14.
                     repeat rewrite rename_all_ns_fundefs_append in H19.
                     eapply fundefs_append_unique_bindings_l in H19.
                     2: reflexivity.
                     destructAll.
                     inv H17.
                     exfalso. specialize (H19 v).
                     apply H19.                                
                     split.
                     eapply fundefs_append_bound_vars.
                     reflexivity. right.
                     simpl. auto.
                     eapply fundefs_append_bound_vars.
                     reflexivity. right.
                     simpl. auto.                              
                   * rewrite (proj1 inlined_comp_ctx).
                     apply bound_var_ctx_comp_ctx. right. simpl.
                     rewrite inlined_fundefs_append.
                     simpl. destruct (get_b v im) eqn:gbvim.
                     apply H3 in gbvim. destructAll.
                     exfalso.
                     apply H15.
                     apply bound_var_app_ctx.
                     right.
                     apply bound_var_rename_all_ns.
                     constructor.
                     eapply fundefs_append_bound_vars.
                     reflexivity.
                     left.
                     eapply fundefs_append_bound_vars.
                     reflexivity.  
                     right.
                     auto.
                     constructor.
                     eapply fundefs_append_bound_vars.
                     reflexivity.  
                     right.
                     auto.
                 + destructAll.
                   destruct x4; inv H18.
                   * exfalso.
                     simpl in H14.
                     inv H14.
                     repeat rewrite rename_all_ns_fundefs_append in H19.
                     eapply fundefs_append_unique_bindings_l in H19.
                     2: reflexivity.
                     destructAll.
                     inv H17.
                     exfalso. specialize (H19 v).
                     apply H19.                                
                     split.
                     eapply fundefs_append_bound_vars.
                     reflexivity. right.
                     simpl. auto.
                     eapply fundefs_append_bound_vars.
                     reflexivity. right.
                     simpl. auto.                              
                   * destruct x4; inv H19.                                
             }
             apply bound_var_rename_all_ns.
             constructor.
             eapply fundefs_append_bound_vars.
             reflexivity.
             left.
             eapply fundefs_append_bound_vars.
             reflexivity.
             right.
             auto.                        
           }
           {
             simpl in H14. inv H14.
             rewrite rename_all_ns_fundefs_append in H19.
             rewrite rename_all_ns_fundefs_append in H19.
             eapply fundefs_append_unique_bindings_l in H19.
             2: reflexivity.
             destructAll.
             inv H17. specialize (H19 v).
             apply H19.
             split.
             eapply fundefs_append_bound_vars.
             reflexivity.
             right. simpl. auto.
             apply bound_var_rename_all_ns_fundefs.
             inv H16. 
             auto.
             inv H23.
           }
           rewrite <- fundefs_append_assoc in H11.
           simpl in H11. simpl. auto.
    - simpl in H5. inv H5.
      split.
      apply rt_refl.
      split; auto.
      split; auto.
      split.
      apply cmap_view_efun1_nil. auto.
      auto.
  Qed.

  Theorem bound_var_fundefs_inlined:
    forall im1 im2,
      b_map_le im1 im2 ->
      forall fds,
        Included _ (bound_var_fundefs (inlined_fundefs_f fds im2)) (bound_var_fundefs (inlined_fundefs_f fds im1)).
  Proof.
    intros im1 im2 Him; induction fds; simpl; repeat normalize_bound_var; auto.
    - destruct (get_b v im1) eqn:gbvi.
      + apply Him in gbvi. rewrite gbvi. auto.
      + destruct (get_b v im2); repeat normalize_bound_var; eauto with Ensembles_DB.
    - intro. intro. inv H.
  Qed.
  
  Lemma bound_var_ctx_inlined_antimon_mut:
    forall im1 im2,
      b_map_le im1 im2 ->
      (forall c, 
         Included _ (bound_var_ctx (inlined_ctx_f c im2)) (bound_var_ctx (inlined_ctx_f c im1))) /\
      (forall fdc, 
         Included _ (bound_var_fundefs_ctx (inlined_fundefs_ctx_f fdc im2)) (bound_var_fundefs_ctx (inlined_fundefs_ctx_f fdc im1))).
  Proof.
    intros im1 im2 Him.
    exp_fundefs_ctx_induction IHc1 IHfc1; simpl; repeat normalize_bound_var_ctx; eauto with Ensembles_DB.
    - intro.
      repeat normalize_bound_var_ctx.
      eauto with Ensembles_DB.
    - apply Included_Union_compat; auto.
      apply bound_var_fundefs_inlined; auto.
  Qed.

  Theorem bound_var_ctx_inlined_antimon:
    forall im1 im2 c,
      b_map_le im1 im2 ->
      Included _ (bound_var_ctx (inlined_ctx_f c im2)) (bound_var_ctx (inlined_ctx_f c im1)). 
  Proof.
    intros.
    apply bound_var_ctx_inlined_antimon_mut; auto.
  Qed.


  Theorem num_occur_rename_all_ns_dead_set:
    forall f x y sigma e,
      f <> y -> 
      num_occur (rename_all_ns sigma e) f 0 ->
      num_occur (rename_all_ns (M.set x y sigma) e) f 0. 
  Proof.
    intros.
    assert (exists n,  num_occur (rename_all_ns (M.set x y sigma) e) f n) by apply e_num_occur.
    destruct H1.
    assert (x0 <= 0).
    eapply (proj1 (num_occur_rename_all_ns_set f x y H)); eauto.
    apply le_n_0_eq in H2.
    subst; auto.
  Qed.
  
  Theorem bound_var_fundefs_ctx_inlined_antimon:
    forall im1 im2 fdc,
      b_map_le im1 im2 ->
      Included _ (bound_var_fundefs_ctx (inlined_fundefs_ctx_f fdc im2)) (bound_var_fundefs_ctx (inlined_fundefs_ctx_f fdc im1)).
  Proof.
    intros.
    apply bound_var_ctx_inlined_antimon_mut; auto.
  Qed.

  
  (* used for function and constructor case *)
  Theorem sub_none_from_pre:
    forall c im e v sub sig,
      unique_bindings (rename_all_ctx_ns sig (inlined_ctx_f c im) |[ e ]|) ->
      cmap_view_ctx sub c ->
      inl_inv im sub (rename_all_ctx_ns sig (inlined_ctx_f c im) |[ e ]|) ->
      bound_var e v ->
      M.get v sub = None.
  Proof.
    intros.
    destruct (M.get v sub) eqn:gvs; auto.
    exfalso.
    destruct s; apply H0 in gvs; destructAll.
    - apply ub_app_ctx_f in H.
      destructAll.
      inv H4.
      specialize (H5 v).
      apply H5.
      split.
      apply bound_var_ctx_rename_all_ns.
      rewrite (proj1 inlined_comp_ctx).
      apply bound_var_ctx_comp_ctx.
      right.
      simpl. auto.
      auto.
    - apply ub_app_ctx_f in H.
      destructAll.
      inv H4.
      specialize (H5 v).
      apply H5.
      split.
      apply bound_var_ctx_rename_all_ns.
      rewrite (proj1 inlined_comp_ctx).
      apply bound_var_ctx_comp_ctx.
      right.
      simpl.
      constructor.
      rewrite inlined_fundefs_append.
      simpl. destruct (get_b v im) eqn:gbvi.
      + apply H1 in gbvi.
        exfalso.
        destruct gbvi. apply H4.
        apply bound_var_app_ctx.
        right. auto.
      + eapply fundefs_append_bound_vars.
        reflexivity.
        right. simpl; auto.
      + auto.
  Qed.

  Ltac ctx_inl_push :=
    rewrite (proj1 inlined_comp_ctx);
    simpl;
    rewrite (proj1 (rename_all_ctx_ns_comp_ctx _ _));
    symmetry;
    rewrite <- app_ctx_f_fuse;
    simpl; auto.




  Theorem get_set_list2:
    forall (x : M.elt) (sig : M.t Maps.PTree.elt) (l : list M.elt)
           (l' : list Maps.PTree.elt),
      ~ FromList l x -> M.get x (set_list (combine l l') sig) = M.get x sig.
  Proof.
    induction l; intros.
    simpl. auto.
    destruct l'.
    simpl; auto.
    simpl. rewrite M.gso.
    apply IHl. intro; apply H. simpl; auto.
    intro; apply H. subst. simpl; auto.
  Qed.
  
  Theorem apply_r_set_list2:
    forall x sig l l',
      ~ FromList l x ->
      apply_r (set_list (combine l l') sig) x =
      apply_r sig x.
  Proof.
    intros. unfold apply_r.
    rewrite get_set_list2; auto.
  Qed.
  
  (* can stage setlist *)
  Theorem set_list_rename_all_ar: forall l0 l sig v,
                                    (forall x, FromList l0 x -> (x <> (apply_r sig v) \/
                                                                 ~ Range_map sig x)) ->
                                    Disjoint _ (FromList l0) (Dom_map sig) ->
                                    (apply_r (set_list (combine l0 (apply_r_list sig l)) (M.empty var))
                                             (apply_r sig v)) = 
                                    (apply_r (set_list (combine l0 (apply_r_list sig l)) sig) v).
  Proof.
    intros.
    assert (Hl0 := Decidable_FromList l0).
    inv Hl0. specialize (Dec v). inv Dec.
    - assert (H' := H v H1).
      unfold apply_r in H'.
      destruct (Maps.PTree.get v sig) eqn:gvs.
      + exfalso. inv H0.
        specialize (H2 v). apply H2. split; auto.
        exists e. auto.
      + inv H'.
        exfalso. auto.
        rewrite apply_r_none with (v := v); auto.
        clear H. clear H2. clear H0. revert l.  induction l0.
        * simpl. unfold apply_r.
          rewrite M.gempty. rewrite gvs. auto.
        * intro. simpl.
          destruct (apply_r_list sig l) eqn:asl.
          simpl.
          unfold apply_r.
          rewrite M.gempty. rewrite gvs. auto.
          simpl in H1.
          destruct (var_dec a v).
          subst.
          simpl.        
          rewrite apply_r_some with (y := e).
          rewrite apply_r_some with (y := e).
          auto. apply M.gss. apply M.gss.
          inv H1. exfalso; auto.
          simpl. rewrite apply_r_set2; auto.
          rewrite apply_r_set2; auto.
          destruct l. simpl in asl. inv asl.
          simpl in asl. inv asl.
          apply IHl0.
          auto.
    - symmetry.
      rewrite apply_r_set_list2; auto.
      assert (Hl0 := Decidable_FromList l0).
      inv Hl0. specialize (Dec (apply_r sig v)). inv Dec.
      + unfold apply_r in H2. destruct (Maps.PTree.get v sig) eqn:gvs.
        * unfold apply_r in H. rewrite gvs in H.
          apply H in H2. inv H2. exfalso; auto.
          exfalso. apply H3. exists v. auto.
        * exfalso; auto.
      + rewrite apply_r_set_list2; auto.
        rewrite apply_r_empty; auto.
  Qed.
  
  
  
  Theorem set_list_rename_all_arl :
    forall l0 l  sig l1,
      Included _ (FromList l0) (Union _ (Complement _  (Range_map sig)) (Complement _ (FromList (apply_r_list sig l1)))) ->
      Disjoint _ (FromList l0) (Dom_map sig) ->
      
      (apply_r_list (set_list (combine l0 (apply_r_list sig l)) (M.empty var))
                    (apply_r_list sig l1)) = 
      (apply_r_list (set_list (combine l0 (apply_r_list sig l)) sig) l1).
  Proof.
    induction l1; intros.
    - auto.
    - simpl.
      rewrite IHl1.
      rewrite set_list_rename_all_ar.
      reflexivity. intros.
      apply H in H1. inv H1. auto.
      left. simpl in H2. intro. apply H2. subst.
      constructor. auto.
      auto.
      intro. intros. apply H in H1. inv H1.
      auto.
      right. intro. apply H2. simpl.
      right. auto.
      auto.
  Qed.    
  
  
  Theorem set_list_rename_all_ns:
    forall l0 l,
      (forall e sig,
         Included _ (FromList l0) (Union _ (Complement _ (Range_map sig)) (dead_var (rename_all_ns sig e))) ->
         Disjoint _ (FromList l0) (Dom_map sig) ->
         rename_all_ns (set_list (combine l0 (apply_r_list sig l)) (M.empty var))
                       (rename_all_ns sig e)  =                                              
         rename_all_ns (set_list (combine l0 (apply_r_list sig l)) sig) e) /\
      (forall f sig,
         Included _ (FromList l0) (Union _ (Complement _ (Range_map sig)) (dead_var_fundefs (rename_all_fun_ns sig f))) ->
         Disjoint _ (FromList l0) (Dom_map sig) ->
         rename_all_fun_ns (set_list (combine l0 (apply_r_list sig l)) (M.empty var))
                           (rename_all_fun_ns sig f)  =                                              
         rename_all_fun_ns (set_list (combine l0 (apply_r_list sig l)) sig) f)
  .
  Proof.
    intros l0 l.
    assert (Hpr := prop_rename_all).
    destruct Hpr as (Hpr1, Hpr2).
    eapply exp_def_mutual_ind; intros; simpl.
    - rewrite set_list_rename_all_arl; auto.
      Focus 2.
      intro. intro. apply H0 in H2. inv H2; auto.
      right. intro. simpl in H3. inv H3; pi0.
      apply not_occur_list_not_in in H4. auto.
      rewrite H; auto.
      intro. intro. apply H0 in H2.
      inv H2. auto.
      right.
      inv H3; pi0. auto.
    - rewrite set_list_rename_all_ar; auto.
      intros. apply H in H1.
      inv H1. auto. left.
      inv H2. intro.
      destruct (cps_util.var_dec x (apply_r sig v)).
      omega.
      auto.
    - rewrite H; auto.
      specialize (H0 sig).
      assert (FromList l0 \subset
                       Union var (Complement var (Range_map sig))
                       (dead_var (rename_all_ns sig (Ecase v l1)))).
      intro; intro. apply H1 in H3. inv H3; auto.
      inv H4; pi0. inv H7; pi0. right.
      eapply num_occur_n.
      constructor; eauto. simpl.
      destruct (cps_util.var_dec x (apply_r sig v)). exfalso; auto.
      auto.
      specialize (H0 H3 H2).
      simpl in H0. inv H0. auto.
      intro; intro. apply H1 in H3. inv H3; auto.
      inv H4; pi0.
      inv H7; pi0. auto.
    - rewrite set_list_rename_all_ar; auto.
      rewrite H; auto.
      intro; intro. apply H0 in H2. inv H2.
      auto.
      right. inv H3; pi0. auto.
      intros. apply H0 in H2. inv H2; auto.
      inv H3; pi0. auto.
    - rewrite H; auto.
      rewrite H0; auto.
      intro; intro. apply H1 in H3; inv H3; auto.
      inv H4; pi0; auto.
      intro; intro. apply H1 in H3; inv H3; auto.
      inv H4; pi0; auto.
    - rewrite set_list_rename_all_ar; auto.
      rewrite set_list_rename_all_arl; auto.
      intro; intro. apply H in H1.
      inv H1; auto.
      right. inv H2; pi0.
      apply  not_occur_list_not_in. auto.
      intros. apply H in H1. inv H1; auto.
      inv H2; pi0; auto.
    - rewrite set_list_rename_all_arl; auto.
      rewrite H; auto.
      intro; intro.
      apply H0 in H2. inv H2; auto. inv H3; pi0.
      auto.
      intro; intro.
      apply H0 in H2. inv H2; auto. inv H3; pi0.
      right. apply not_occur_list_not_in; auto.
    - rewrite set_list_rename_all_ar; auto.
      intro; intro.
      apply H in H1. inv H1; auto.
      inv H2; pi0; auto.
    - rewrite H; auto.
      rewrite H0; auto.
      intro; intros. apply H1 in H3. inv H3; auto.
      inv H4; pi0. auto.
      intro; intros. apply H1 in H3. inv H3; auto.
      inv H4; pi0. auto.
    - auto.
  Qed.

  Theorem FromList_set_list:
    forall {A} x y sig l (l':list A),
      M.get x (set_list (combine l l') sig) = Some y ->
      length l = length l' ->
      FromList l x ->
      FromList l' y.
  Proof.
    induction l; intros.
    inv H1.
    destruct l'. simpl in H0. inv H0.
    simpl in H0.
    simpl in H.
    inv H1.
    rewrite M.gss in H. inv H. constructor. auto.
    destruct (var_dec a x). subst. rewrite M.gss in H.
    inv H; constructor; auto.      
    rewrite M.gso in H.
    right. 
    eapply IHl; auto. auto.
  Qed.


  Theorem num_occur_rename_all_ns_set_list:
    (forall (e : exp) (m : nat) f l x n (sigma : r_map),
       ~ FromList l f ->
       num_occur (rename_all_ns sigma e) f m ->
       num_occur (rename_all_ns (set_list (combine x l) sigma) e) f n -> n <= m).
  Proof.
    induction l; intros.
    destruct x; simpl in H1.
    assert (n = m).
    eapply (proj1 (num_occur_det _ )); eauto.
    subst. constructor.
    assert (n = m).
    eapply (proj1 (num_occur_det _ )); eauto.
    subst. constructor.
    destruct x. simpl in H1.
    assert (n = m).
    eapply (proj1 (num_occur_det _ )); eauto.
    subst. constructor.
    simpl in H1.
    assert (exists n,  num_occur (rename_all_ns (set_list (combine x l) sigma) e) f n) by apply e_num_occur.
    destruct H2.
    etransitivity.
    Focus 2.
    eapply IHl. intro; apply H. constructor 2; auto.
    apply H0. apply H2.
    assert (f <> a). intro. apply H. constructor. auto.
    eapply (proj1 (num_occur_rename_all_ns_set _ _ _ H3)).
    apply H2. apply H1.
  Qed.

  Theorem dead_occur_rename_all_ns_set_list:
    (forall (e : exp) f l x (sigma : r_map),
       ~ FromList l f ->
       num_occur (rename_all_ns sigma e) f 0 ->
       num_occur (rename_all_ns (set_list (combine x l) sigma) e) f 0).
  Proof.
    intros.
    assert (exists n, num_occur (rename_all_ns (set_list (combine x l) sigma) e) f n) by apply e_num_occur.
    destruct H1.
    assert (x0 <= 0).
    eapply num_occur_rename_all_ns_set_list; eauto.
    apply le_n_0_eq in H2. subst; auto.
  Qed.  

  Theorem length_apply_r_list:
    forall sig l,
      length (apply_r_list sig l) = length l.
  Proof.
    induction l; simpl; auto.
  Qed.

  Theorem nthN_map:
    forall A B  f l n v,
      nthN l n = Some v ->
      nthN (@map A B f l) n = Some (f v).
  Proof.
    induction l; intros.
    - inv H.
    - simpl in H. destruct n.
      simpl. inv H; auto.
      apply IHl.
      simpl. destruct p. apply H.
      apply H.
      apply H.
  Qed.        

  Theorem num_occur_fds_le_antimon:
    forall im im',
      b_map_le im im' ->
      forall f,
      forall f4 n m,
        num_occur_fds (inlined_fundefs_f f4 im) f n ->
        num_occur_fds (inlined_fundefs_f f4 im') f m ->
        m <= n. 
  Proof.
    induction f4; simpl; intros.
    - destruct (get_b v im) eqn:gbvim.
      apply H in gbvim.
      rewrite gbvim in H1. eauto.
      inv H0.
      destruct (get_b v im').
      specialize (IHf4 _ _ H10 H1). omega.
      inv H1.
      apply plus_le_compat; eauto.
      apply Nat.eq_le_incl.
      eapply (proj1 (num_occur_det _)); eauto.
    - inv H0; inv H1; auto.
  Qed.

  Theorem num_occur_case_det:
    forall f cl n m ,
      num_occur_case cl f n ->
      num_occur_case cl f m ->
      n = m.
  Proof.
    induction cl; intros; inv H; inv H0; eauto.      
    erewrite IHcl with (n := m0); eauto.
    erewrite (proj1 (num_occur_det _)) with (n1 := n0); eauto.
  Qed.

  
  Theorem num_occur_ec_le_antimon:
    forall im im',
      b_map_le im im' ->
      forall f,
        (forall c n m,
           num_occur_ec (inlined_ctx_f c im) f n ->
           num_occur_ec (inlined_ctx_f c im') f m ->
           m <= n) /\
        (forall cfds n m,
           num_occur_fdc (inlined_fundefs_ctx_f cfds im) f n ->
           num_occur_fdc (inlined_fundefs_ctx_f cfds im') f m ->
           m <= n).
  Proof.
    intros im im' Him f.
    exp_fundefs_ctx_induction IHc IHf; intros nn mm Hn Hm; simpl in *;
    try (inversion Hn; inversion Hm; subst); auto; try (apply plus_le_compat; eauto).
    - intro. simpl in *. inv H. simpl.
      repeat apply plus_le_compat; eauto.
      apply Nat.eq_le_incl.        
      eapply num_occur_case_det; eauto.
      apply Nat.eq_le_incl.        
      eapply num_occur_case_det; eauto.        
    - intro. inversion H0; subst.
      repeat apply plus_le_compat; eauto.
      apply Nat.eq_le_incl.        
      eapply num_occur_case_det; eauto.
      apply Nat.eq_le_incl.        
      eapply num_occur_case_det; eauto.        
    - clear Hm; clear Hn.
      eapply num_occur_fds_le_antimon; eauto.
    - clear Hm; clear Hn.
      apply Nat.eq_le_incl.        
      eapply (proj1 (num_occur_det _)); eauto.
    - apply Nat.eq_le_incl.        
      eapply (proj2 (num_occur_det _)); eauto.
    - apply Nat.eq_le_incl.        
      eapply (proj1 (num_occur_det _)); eauto.
  Qed.    

  Theorem dead_occur_ec_le_antimon:
    forall im im' c f,
      b_map_le im im' ->
      num_occur_ec (inlined_ctx_f c im) f 0 ->
      num_occur_ec (inlined_ctx_f c im') f 0. 
  Proof.
    intros.
    assert (exists n, num_occur_ec (inlined_ctx_f c im') f n) by apply e_num_occur_ec.
    destruct H1.
    assert (x <= 0).
    eapply (proj1 (num_occur_ec_le_antimon _ _ H _)); eauto.
    apply le_n_0_eq in H2.
    subst; auto.
  Qed.
  
  Lemma apply_r_list_push:
    forall v v1 sig l, 
      List.In v1 l ->
      List.In (apply_r sig v1) (apply_r_list (M.set v (apply_r sig v1) sig) l).
  Proof.
    induction l; intros.
    - inv H.
    - inv H.
      + simpl.
        left.
        destruct (var_dec v v1).
        * subst.
          unfold apply_r.
          rewrite M.gss. auto.
        * apply apply_r_set2. auto.
      + simpl. right.
        eauto.
  Qed.
  
  

  
  (* TODO: move to identifiers *)




  Theorem dead_not_free:
    (forall e, Disjoint _ (dead_var e) (occurs_free e)) /\
    (forall fds, Disjoint _ (dead_var_fundefs fds) (occurs_free_fundefs fds)).
  Proof.
    apply exp_def_mutual_ind; intros; repeat normalize_occurs_free; simpl; split.
    -  intro; intro Hdj; inv Hdj.
       inv H0. inv H1; pi0.
       revert H0. apply not_occur_list_not_in. auto.
       inv H0. inv H.  specialize (H0 x); apply H0; auto.
    - intro; intro Hdj; inv Hdj.
      inv H; pi0. inv H0; auto.
    - intro. intro.
      inv H; inv H0. specialize (H2 x). specialize (H x).
      inv H1. inv H3.
      inv H1. inv H0; pi0.
      inv H0; pi0. inv H6; pi0.
      inv H1; auto.
      apply H. split; auto. eapply num_occur_n.
      constructor; auto. apply H10. simpl.
      destruct (cps_util.var_dec x v). exfalso; auto. auto.
    - intro; intro Hdj; inv Hdj.
      inv H0; pi0.
      inv H1. inv H2; auto.
      inv H2. inv H.
      specialize (H2 x). apply H2. split; auto.
    - intro; intro Hdj; inv Hdj.
      inv H1; pi0. inv H2.
      inv H. specialize (H2 x). apply H2. auto.
      inv H1.
      inv H0. specialize (H1 x). apply H1; auto.
    - intro. intro. inv H. inv H0; pi0. inv H1.
      revert H0. apply not_occur_list_not_in. auto.
      inv H0; auto.
    - intro. intro. inv H0. inv H1; pi0.
      inv H2.
      revert H0. apply not_occur_list_not_in. auto.
      inv H0. inv H. specialize (H0 x). apply H0; auto.
    - intro. intro. inv H. inv H1. inv H0; pi0.
    - intro. intro. inv H1. inv H2; pi0. inv H; inv H0.
      specialize (H1 x). specialize (H x). inv H3; auto.
      inv H0; auto. inv H0; auto.
    - intro. intro. inv H. inv H1.
  Qed.

  Theorem precontractfun_sig_nbv:
    forall fds_c sig count sub fds_c' count' sub', 
      precontractfun sig count sub fds_c = (fds_c', count', sub') ->
      eq_env_P (Complement _ (name_in_fundefs fds_c)) sub sub'. 
  Proof.
    induction fds_c; intros.
    - simpl in H. destruct (get_c v count).
      eapply IHfds_c in H. intro. intro. apply H.
      intro; apply H0. simpl. auto.
      remember (precontractfun sig count sub fds_c).
      destruct p. destruct p. symmetry in Heqp.
      apply IHfds_c in Heqp.
      inv H. intro. intro. simpl in H.
      apply Union_DeMorgan in H. inv H.
      rewrite M.gso. apply Heqp. auto.
      intro; apply H0. subst; auto.
    - simpl in H. inv H. intro. intro. auto.
  Qed.
  


  Hint Constructors bound_not_stem_ctx.
  Hint Constructors bound_not_stem_fundefs_ctx.





  Theorem Proper_Intersection:
    forall A : Type, Proper (Same_set A ==> Same_set A ==> Same_set A) (Intersection A).
  Proof.
    intros. intro. intros. intro. intros. split; intro; intros.
    inv H1. apply H in H2. apply H0 in H3. auto.
    inv H1. apply H in H2.
    apply H0 in H3. auto.
  Qed.  



  Theorem ub_disjoint_name_not_stem_ctx:
    forall f5,
      unique_bindings_fundefs_c f5 ->
      Disjoint _ (names_in_fundefs_ctx f5) (bound_not_stem_fundefs_ctx f5).
  Proof.
    induction f5; intros; simpl; try normalize_bound_not_stem_ctx'.
    - inv H.
      apply Union_Disjoint_l. apply Union_Disjoint_r.
      split; intro; intros. intro. inv H. inv H0. apply H5.
      apply bound_var_stem_or_not_stem. auto.
      split; intro; intros. intro. inv H. inv H0. inv H1. apply H6; auto.
      apply Union_Disjoint_r.
      split; intros. intro. inv H. inv H9.
      specialize (H x). apply H. split.
      apply bound_var_stem_or_not_stem; auto.
      apply name_in_fundefs_bound_var_fundefs. auto.
      apply Disjoint_Setminus_r. intro; intros; auto.
    - inv H.
      apply IHf5 in H13.
      apply Union_Disjoint_l; auto.
      split. intro. intro. inv H. inv H0. inv H1. inv H; auto. apply H6.
      apply bound_var_fundefs_stem_or_not_stem.
      right. auto.
      split. intro. intro. inv H. inv H1. inv H. inv H9. specialize (H x). apply H.
      split; auto. 
      apply name_in_bound_var_fundefs_ctx. auto.
      inv H8. specialize (H x). apply H. split; auto.
      apply name_in_bound_var_fundefs_ctx. auto.
      inv H13. specialize (H1 x). apply H1; auto.
  Qed.

  Theorem findtag_map: forall f (c0:cTag) e l,
                         findtag l c0 = Some e ->    
                         @findtag exp
                                  (map (fun p : var * exp => let (k, e0) := p in (k, f e0))
                                       l) c0 = Some (f e).
  Proof.
    induction l; intro. inv H.
    simpl in H. simpl. destruct a.
    destruct (M.elt_eq c c0). inv H; auto.
    apply IHl in H. auto.
  Qed.  
  
  
  Theorem  ub_disjoint_stem_not_stem:
    (forall c,
       unique_bindings_c c ->
       Disjoint _ (bound_stem_ctx c) (bound_not_stem_ctx c)) /\
    (forall f,
       unique_bindings_fundefs_c f ->
       Disjoint _ (bound_stem_fundefs_ctx f) (bound_not_stem_fundefs_ctx f)).
  Proof.    
    apply exp_fundefs_ctx_mutual_ind; intros;  try normalize_bound_stem_ctx'; try normalize_bound_not_stem_ctx'; try rewrite H; eauto 25 with Ensembles_DB.
    -  inv H0. apply Union_Disjoint_l; auto.
       split. intros. intro. inv H0. inv H1. apply H3.
       apply bound_var_stem_or_not_stem. auto.
    - inv H0.
      apply Union_Disjoint_l; auto.
      split. intros. intro. inv H0. inv H1. apply H3.
      apply bound_var_stem_or_not_stem. auto.
    - inv H0.
      apply Union_Disjoint_l; auto.
      split. intros. intro. inv H0. inv H1. apply H3.
      apply bound_var_stem_or_not_stem. auto.
    - inv H0.
      normalize_bound_var_in_ctx. 
      apply Union_Disjoint_r; auto.
      rewrite bound_var_stem_or_not_stem in H8.
      eauto with Ensembles_DB.
    - inv H0.
      apply Union_Disjoint_l; apply Union_Disjoint_r.
      apply Disjoint_Setminus_r. intro; intros; auto.
      apply Disjoint_sym.
      eapply Disjoint_Included_l.
      2: eapply Disjoint_Included_r.
      3: apply H5.
      rewrite bound_var_stem_or_not_stem. auto with Ensembles_DB.
      apply name_in_fundefs_bound_var_fundefs.
      eapply Disjoint_Included_l.
      2: eapply Disjoint_Included_r.
      3: apply H5.
      rewrite bound_var_stem_or_not_stem. auto with Ensembles_DB.
      auto with Ensembles_DB.
      apply H. auto.
    - inv H0.
      apply Union_Disjoint_l; apply Union_Disjoint_r.
      apply Disjoint_sym. eapply Disjoint_Included_r.
      2: apply H5. apply name_in_bound_var_fundefs_ctx.
      apply ub_disjoint_name_not_stem_ctx. auto.
      apply Disjoint_sym. eapply Disjoint_Included_r.
      2: apply H5.
      rewrite bound_var_fundefs_stem_or_not_stem.
      intro; intros. auto.
      apply H. auto.
    - inv H0.
      apply Union_Disjoint_l; apply Union_Disjoint_r.
      apply H; auto.
      split; intro; intros; intro. inv H0. inv H2. inv H10. specialize (H2 x).
      apply H2. split; auto. apply bound_var_stem_or_not_stem. auto.
      apply Disjoint_sym.
      eapply Disjoint_Included_l. 2: apply H8. rewrite bound_var_stem_or_not_stem. auto with Ensembles_DB.
      apply Disjoint_sym.
      eapply Disjoint_Included_l. 2: apply H9.
      auto with Ensembles_DB.
    - inv H0.
      apply Union_Disjoint_r.
      apply Union_Disjoint_r.
      apply Disjoint_sym.
      eapply Disjoint_Included_r. 2: apply H10.
      rewrite bound_var_fundefs_stem_or_not_stem. auto with Ensembles_DB.
      eapply Disjoint_Included_l. 2: apply H9.
      rewrite bound_var_fundefs_stem_or_not_stem. auto with Ensembles_DB.
      apply H. auto.
  Qed.



  Theorem contractcases_corresp:
    forall cl2 cl1 sig c im x count sub,
      (* recursive call to shrink_corresp *)
      (forall e sub' im' sig c count,
         (term_sub_inl_size (e, sub', im') < term_sub_inl_size (Ecase x cl2, sub, im)) ->  
         let ce := (app_ctx_f (rename_all_ctx_ns sig (inlined_ctx_f c im')) (rename_all_ns sig e)) in
         unique_bindings ce ->
         closed ce ->
         c_count ce count ->
         cmap_view_ctx sub' c ->
         inl_inv im' sub' ce ->
         sig_inv_full sig (rename_all_ctx_ns sig (inlined_ctx_f c im')) (rename_all_ns sig e) ->
         forall e' count' im'' BP,
           contract sig count e sub' im' = existT _ (e', count', im'') BP ->
           let ce' := (app_ctx_f (rename_all_ctx_ns sig (inlined_ctx_f c im'')) e') in
           gsr_clos ce ce' /\ c_count ce' count' /\ inl_inv im'' sub' ce' /\
           sig_inv_codom sig (rename_all_ctx_ns sig (inlined_ctx_f c im'')) e') ->
      (* actual statement of contract_case *)
      let ce := (app_ctx_f (rename_all_ctx_ns sig (inlined_ctx_f c im)) (Ecase x (cl1 ++ (rename_all_case sig cl2)))) in
      unique_bindings ce ->
      closed ce ->
      c_count ce count ->
      cmap_view_ctx sub c ->
      inl_inv im sub ce ->
      sig_inv_full sig (rename_all_ctx_ns sig (inlined_ctx_f c im)) (Ecase x (cl1 ++ (rename_all_case sig cl2)))  ->
      forall cl2' count' im' oes pfe pfsub bp,
        contractcases oes (fun rm cm es H => contract rm cm (fst (fst es)) (snd (fst es)) (snd es)) sig count im sub cl2 pfe pfsub = existT _ (cl2', count', im') bp ->
        let ce' := (app_ctx_f (rename_all_ctx_ns sig (inlined_ctx_f c im')) (Ecase x (cl1 ++ cl2'))) in
        gsr_clos ce ce' /\ c_count ce' count' /\ inl_inv im' sub ce' /\
        sig_inv_codom sig (rename_all_ctx_ns sig (inlined_ctx_f c im')) (Ecase x (cl1 ++ cl2'))
  .
  Proof.
    induction cl2; intros cl1 sig c im x count sub;
    intro Hcontract_corresp;
    intros; simpl in H5.
    - 
      inv H5; unfold ce in *; unfold ce' in *; split; auto.
      apply rt_refl.
      split; auto. split; auto.
      apply sig_inv_combine in H4. inv H4. simpl in H6. auto.
    -         
      destruct a.
      remember (contract sig count e sub im) as con_e.        
      destruct con_e.
      destruct x0.
      destruct p.
      simpl in ce.
      assert (Hcl1: (rename_all_ns sig (Ecase x cl1)) = Ecase x cl1 ). {
        rewrite <- (proj1 (rename_all_no_shadow _)).
        apply Disjoint_dom_rename_all.
        
        (* by sig inv dead using H4 *)
        split. intro. intro.
        inv H6.
        inv H7.
        apply H4 in H6.
        destruct H6 as (H6, H6c).
        apply not_bound_dead_or_free in H6.
        inv H6.
        2:               apply H0 in H7; inv H7.
        unfold ce in H7.
        apply num_occur_app_ctx in H7. destructAll; pi0.
        inv H7.
        apply num_occur_app_case in H12.
        destructAll.
        pi0.              
        assert (~(occurs_free (Ecase x cl1)) x0).
        apply not_occurs_not_free.
        eapply num_occur_n.
        constructor; eauto.
        simpl. destruct (cps_util.var_dec x0 x). exfalso; auto. auto.
        auto.
        (* using H4 *)
        eapply sig_inv_dom_mon.
        Focus 2.
        apply sig_inv_combine in H4. destruct H4.
        eauto.
        rewrite bound_var_app_ctx.
        rewrite bound_var_Ecase_app.
        auto with Ensembles_DB.
      }
                                                                       rename c0 into v.
      assert (rename_all_ctx_ns sig (inlined_ctx_f c im)
             |[ Ecase x  (cl1 ++ (v, rename_all_ns sig e) :: rename_all_case sig cl2) ]| =
                                                                                         rename_all_ctx_ns sig (inlined_ctx_f (comp_ctx_f c (Ecase_c x cl1 v Hole_c cl2)) im)
             |[ rename_all_ns sig e]|).
      {
        assert (
            Ecase x (cl1 ++ (v, rename_all_ns sig e) :: rename_all_case sig cl2) =
            rename_all_ns sig (Ecase x (cl1 ++ (v, e) :: cl2))).
        {
          simpl. rewrite list_append_map.
          simpl in Hcl1. inversion Hcl1.
          repeat rewrite H8. 
          repeat rewrite H7.
          reflexivity.
        }
        rewrite H6.
        clear H6.
        do 2 (rewrite <- (proj1 (rename_all_ns_app_ctx _ _))).
        rewrite (proj1 inlined_comp_ctx).
        simpl.          
        rewrite <- app_ctx_f_fuse. 
        simpl. reflexivity.
      }
      symmetry in Heqcon_e.

      eapply Hcontract_corresp with
      (c :=  (comp_ctx_f c (Ecase_c x cl1 v Hole_c cl2)))
        in Heqcon_e; try (rewrite <- H6; auto). 
      Focus 2. unfold term_sub_inl_size. simpl. omega.
      
      (*
        eapply shrink_corresp with
        (c :=  (comp_ctx_f c (Ecase_c x cl1 v Hole_c cl2)))
          in Heqcon_e; try (rewrite <- H6; auto). *)
      Focus 2.
      apply cmap_view_case. auto.

      (* push Disjoint, Unique and Sub_inv through e0 *)
      destruct Heqcon_e as (H7, H8).
      destruct H8 as (H8, H9).
      destruct H9 as (H9, H_sig_r).
      rewrite <- H6 in H7.
      assert (Hub' := gsr_preserves_clos _ _ H H0 H7).
      destructAll.
      apply sig_inv_combine in H4.
      destruct H4 as (H4, H4c).
      assert (Hse := gsr_preserves_sig_dom _ _ _ H H0 H7 H4).
      assert (He0 : rename_all_ns sig e0 = e0). {
        rewrite <- (proj1 (rename_all_no_shadow _)).
        apply Disjoint_dom_rename_all.

        split; intros; intro. inv H12.
        inv H13. apply Hse in H12.
        apply not_bound_dead_or_free in H12.
        inv H12.
        2: apply H11 in H13; inv H13.
        
        apply num_occur_app_ctx in H13; destructAll; pi0; auto.
        apply not_occurs_not_free in H13. auto.
        eapply sig_inv_dom_mon.
        2: apply Hse.
        rewrite bound_var_app_ctx.
        right; auto.
      }
                                                
                                                assert (
                                                  (rename_all_ctx_ns sig
                                                                     (inlined_ctx_f (comp_ctx_f c (Ecase_c x cl1 v Hole_c cl2)) b0)
                                                  |[ rename_all_ns sig e0 ]|) =
                                                  (rename_all_ctx_ns sig
                                                                     (inlined_ctx_f c b0)
                                                  |[  (Ecase x ((cl1++[(v,e0)])++(rename_all_case sig cl2)))]|)).
      {
        assert (Ecase x ((cl1 ++ [(v, e0)]) ++ rename_all_case sig cl2)  =
                rename_all_ns sig (Ecase x ((cl1 ++ [(v, e0)]) ++ cl2))).
        {
          simpl.
          inversion Hcl1.
          rewrite list_append_map.
          rewrite list_append_map.
          simpl.
          repeat rewrite H14.
          repeat rewrite H13.
          rewrite He0. reflexivity.
        }
        rewrite H12. clear H12.
        
        do 2 (rewrite <- (proj1 (rename_all_ns_app_ctx _ _))).
        rewrite (proj1 inlined_comp_ctx).
        simpl.          
        rewrite <- app_ctx_f_fuse. 
        simpl.
        rewrite <- app_assoc. simpl. reflexivity.
      }

      (* I.H. *)
      remember (contractcases oes
                              (fun (rm : r_map) (cm : c_map)
                                   (es : prod (prod exp ctx_map) b_map)
                                   (_ : lt (term_sub_inl_size es) (term_sub_inl_size oes)) =>
                                 contract rm cm
                                          (@fst exp ctx_map (@fst (prod exp ctx_map) b_map es))
                                          (@snd exp ctx_map (@fst (prod exp ctx_map) b_map es))
                                          (@snd (prod exp ctx_map) b_map es)) sig c1 b0 sub cl2
                              (@subcl_e_cons_l v e cl2
                                               (@fst exp ctx_map (@fst (prod exp ctx_map) b_map oes))
                                               (@eq_ind_r (list (prod var exp))
                                                          (@cons (prod cTag exp) (@pair cTag exp v e) cl2)
                                                          (fun x : list (prod var exp) =>
                                                             subcl_e x
                                                                     (@fst exp ctx_map (@fst (prod exp ctx_map) b_map oes)))
                                                          pfe (@cons (prod var exp) (@pair var exp v e) cl2)
                                                          (@eq_refl (list (prod var exp))
                                                                    (@cons (prod cTag exp) (@pair cTag exp v e) cl2))))
                              (@sub_inl_size_compat sub im b0
                                                    (@snd exp ctx_map (@fst (prod exp ctx_map) b_map oes))
                                                    (@snd (prod exp ctx_map) b_map oes) pfsub b)) as cc_ind.
      destruct cc_ind. destruct x0.
      destruct p. 
      symmetry in Heqcc_ind.
      rewrite He0 in H12.
      rewrite H12 in *.
      
      
      eapply  IHcl2 in Heqcc_ind; eauto.
      destruct Heqcc_ind.
      destruct H14.
      destruct H15 as (H15, Hsig_r).
      clear He0.
      inv H5. unfold ce'.
      split.
      eapply rt_trans.
      apply H7.
      do 2 (rewrite <- app_assoc in H13).
      simpl in H13.
      rewrite <- app_assoc.
      simpl.
      auto.
      rewrite <- app_assoc in H14.
      rewrite <- app_assoc in H15.
      split; auto.
      split; auto.
      rewrite <- app_assoc in Hsig_r. 
      simpl in Hsig_r. auto.
      {
        intros.
        eapply Hcontract_corresp; eauto.
        etransitivity. apply H13.
        assert (sub_inl_size sub b0 <= sub_inl_size sub im).
        apply sub_size_le. apply b_map_le_c. auto.
        simpl. unfold term_sub_inl_size. simpl.
        assert ( 1 <= term_size e) by apply min_term_size.
        omega.
      }
      { 
        apply sig_inv_combine.
        split.
        - (* dom *)
          auto.
        - (* codom *)
          intro. intros. apply H_sig_r in H13.
          rewrite H12 in H13.
          destruct H13; auto.
          right.
          repeat normalize_ctx.
          apply bound_stem_comp_ctx_mut in H13. inversion H13; auto.
          simpl in H14. inversion H14. inversion H22.
      }
      intro. intros.
      apply H4 in H7. destruct H7.          
      split.
      +  intro. apply H7.
         apply bound_var_app_ctx.
         apply bound_var_app_ctx in H9.
         repeat normalize_ctx.
         inv H9.
         apply bound_var_ctx_comp_ctx in H10.
         inv H10.
         left; auto.
         right.
         normalize_bound_var.

         apply bound_var_ctx_rename_all_ns in H9.
         simpl in H9.
         normalize_bound_var_ctx_in_ctx.
         inv H9.
         auto.
         inv H10. inv H9.
         right.
         apply bound_var_rename_all_ns with (sigma := sig) in H9.
         simpl in H9. inv H9.
         eapply Bound_Ecase.
         apply H12. right; eauto.                          
         right.
         normalize_bound_var.
         right.
         eapply Bound_Ecase.
         Focus 2.
         left. eauto.
         auto.
      + inv H8.
        * left.
          apply num_occur_app_ctx in H9. destructAll; pi0.
          inv H9; pi0.
          apply num_occur_app_case in H13.
          destructAll; pi0.
          inv H11; pi0.
          simpl.
          apply num_occur_app_ctx. exists 0, 0; split; auto.
          rewrite (proj1 inlined_comp_ctx).
          rewrite (proj1 (rename_all_ctx_ns_comp_ctx _ _)).
          apply num_occur_ec_comp_ctx.
          exists 0, 0. repeat split; auto.
          simpl.
          eapply num_occur_ec_n.
          constructor. simpl in Hcl1. inversion Hcl1.
          rewrite H13. rewrite H13.
          eauto.
          constructor.
          eauto.
          simpl.
          unfold apply_r.
          destruct ( @Maps.PTree.get Maps.PTree.elt x sig) eqn:gxs.
          exfalso.
          apply H4 in gxs.
          destruct gxs.
          apply not_bound_dead_or_free in H11. inv H11.
          apply num_occur_app_ctx in H13.
          destructAll; pi0.
          inv H13.
          destruct (cps_util.var_dec x x). inv H20. apply n1; auto.
          apply H0 in H13. inv H13.
          destruct (cps_util.var_dec y x).
          exfalso; auto.
          auto.
        * right.
          repeat normalize_ctx.
          apply bound_stem_comp_ctx_mut.
          left; auto.              
  Qed.





  (* move to shrink_cps_correct *)
  Theorem gsr_included_bv :
    forall e e',
      gsr_clos e e' ->
      Included _ (bound_var e') (bound_var e).
  Proof.
    intros. induction H.
    - inv H; inv H0; do 2 (rewrite bound_var_app_ctx); repeat normalize_bound_var; eauto with Ensembles_DB.
      + apply Included_Union_compat.
        auto with Ensembles_DB.
        apply Included_Union_compat.
        2: auto with Ensembles_DB.
        rewrite fundefs_append_bound_vars. 2: reflexivity.
        intro. intro.
        rewrite fundefs_append_bound_vars. 2: reflexivity.
        normalize_bound_var. inv H0; auto.
      + do 2 (rewrite bound_var_app_ctx).
        apply Included_Union_compat.
        auto with Ensembles_DB.
        apply Included_Union_compat.
        apply Included_Union_compat.
        auto with Ensembles_DB.
        intro. intros.
        eapply Bound_Ecase. apply H0.
        apply findtag_In_patterns.
        apply H.
        auto with Ensembles_DB.      
      + rewrite bound_var_app_ctx.
        rewrite <- bound_var_rename_all_ns.      
        rewrite bound_var_app_ctx.
        normalize_bound_var. auto with Ensembles_DB.
      + do 2 (rewrite bound_var_app_ctx).
        repeat normalize_bound_var.
        rewrite <- bound_var_rename_all_ns.
        apply Included_Union_compat.
        auto with Ensembles_DB.
        rewrite fundefs_append_bound_vars. 2: reflexivity.
        intro. intros.
        rewrite fundefs_append_bound_vars. 2: reflexivity.
        normalize_bound_var. inv H0; auto with Ensembles_DB.
        inv H2; auto. left. right. right. auto.
        inv H2; auto. left. right. right. auto.            
    - auto with Ensembles_DB.
    - etransitivity; eauto.
  Qed.

  Theorem apply_r_list_In:
    forall v1 sig l,
      List.In v1 l ->
      List.In (apply_r sig v1) (apply_r_list sig l).
  Proof.
    induction l.
    intro. inv H.
    intros. inv H.
    simpl. auto.
    apply IHl in H0. simpl. auto.
  Qed.

  Theorem inlined_fundefs_ctx_append1:
    forall v f l fds_c im fds,
      (inlined_fundefs_ctx_f
         (fundefs_ctx_append (inlined_fundefs_f fds im)
                             (Fcons1_c v f l Hole_c (inlined_fundefs_f fds_c im))) im) = 
      (fundefs_ctx_append (inlined_fundefs_f fds im)
                          (Fcons1_c v f l Hole_c (inlined_fundefs_f fds_c im))).
  Proof.
    induction fds; intros; simpl; auto.
    destruct (get_b v0 im); auto.
    simpl. 
    rewrite IHfds.
    reflexivity.
  Qed.


  Theorem inlined_fundefs_ctx_append_shallow:
    forall v f l fds_c b0 fds,     
      (inlined_fundefs_ctx_f
         (fundefs_ctx_append fds
                             (Fcons1_c v f l Hole_c fds_c)) b0) =
      (fundefs_ctx_append fds
                          (Fcons1_c v f l Hole_c fds_c)).
  Proof.
    intros.
    induction fds.
    - simpl.

      rewrite IHfds. auto.
    - simpl. reflexivity.
  Qed.
  
  
  
  Theorem rename_all_fundefs_ctx_append:
    forall sig fdc fds,
      rename_all_fun_ctx_ns sig (fundefs_ctx_append fds fdc) =
      fundefs_ctx_append (rename_all_fun_ns sig fds)
                         (rename_all_fun_ctx_ns sig fdc).
  Proof.
    induction fds; auto.
    simpl.
    rewrite IHfds. auto.
  Qed.
  
  Theorem app_f_ctx_fundefs_ctx_append:
    forall fdc e fds,
      fundefs_ctx_append fds fdc <[ e ]> =
      fundefs_append fds (fdc <[e]>).
  Proof.
    induction fds; auto.
    simpl; rewrite IHfds. auto.
  Qed.

  

  
  Theorem bound_var_fundefs_ctx_append_f:
    forall im fdc,
      Included _ (names_in_fundefs_ctx fdc)
               (bound_var_fundefs_ctx (inlined_fundefs_ctx_f fdc im)).
  Proof.
    induction fdc.
    - simpl.
      normalize_bound_var_ctx.
      intro. intro. inv H; auto.
      apply name_in_fundefs_bound_var_fundefs in H0.
      auto.
    - simpl.
      normalize_bound_var_ctx.
      intro; intro.
      inv H; auto.
  Qed.
  
  Theorem name_in_fundefs_ctx_append:
    forall fdc fds,
      Same_set _ (names_in_fundefs_ctx (fundefs_ctx_append fds fdc)) (Union _ (name_in_fundefs fds) (names_in_fundefs_ctx fdc)).
  Proof.
    induction fds.
    - simpl. rewrite IHfds; auto with Ensembles_DB.
    - simpl. auto with Ensembles_DB.
  Qed.

  Theorem bound_var_fundefs_ctx_append:
    forall fdc fds,
      Same_set _ (bound_var_fundefs_ctx
                    (fundefs_ctx_append fds fdc))
               (Union _ (bound_var_fundefs fds) (bound_var_fundefs_ctx fdc)).
  Proof.
    induction fds; simpl; normalize_bound_var; try normalize_bound_var_ctx; eauto with Ensembles_DB.
    rewrite IHfds.
    eauto with Ensembles_DB.
  Qed.   

  

  Theorem name_in_fundefs_not_inlined:
    forall f im fds,
      get_b f im = false ->
      (name_in_fundefs fds f <-> name_in_fundefs (inlined_fundefs_f fds im) f).
  Proof.
    induction fds; simpl; intros.
    2: split; intro; auto.
    destruct (var_dec v f).
    - subst. rewrite H. simpl.
      split; intro. left; auto.  left; auto.
    - split. intro. inv H0.
      exfalso. apply n. inv H1. auto.
      apply IHfds in H1; auto.
      destruct (get_b v im); auto. constructor 2. auto.
      intro. right.
      apply IHfds; auto.
      destruct (get_b v im). auto. inv H0.
      exfalso; apply n; inv H1; auto.
      auto.
  Qed.

  Theorem Included_name_in_fundefs_inlined:
    forall im fds,
      Included _ (name_in_fundefs (inlined_fundefs_f fds im)) (name_in_fundefs fds).
  Proof.
    induction fds; eauto with Ensembles_DB.
    simpl. destruct (get_b v im); simpl; auto with Ensembles_DB.
  Qed.   

  
  Theorem name_in_fundefs_not_inlined':
    forall f fds im,
      name_in_fundefs fds f ->
      get_b f im = false ->
      bound_var_fundefs (inlined_fundefs_f fds im) f.
  Proof.
    induction fds; simpl; intros.
    - inv H.
      inv H1.
      rewrite H0.
      apply bound_var_fundefs_Fcons.
      auto.
      specialize (IHfds _ H1 H0).
      destruct (get_b v im); eauto with Ensembles_DB.
    - inv H.
  Qed.


  Theorem fundefs_ctx_append_num_occur:
    forall B1 B2,
    forall (x : var) (n m : nat),
      num_occur_fds B1 x n -> num_occur_fdc B2 x m -> num_occur_fdc (fundefs_ctx_append B1 B2) x (n + m).
  Proof.
    induction B1; intros.
    - simpl in H.
      inv H.
      simpl. 
      eapply num_occur_fdc_n.
      constructor. eauto.     
      apply IHB1; eauto.
      omega.
    - inv H. auto.
  Qed.
  
  Theorem fundefs_ctx_append_num_occur':
    forall (B1: fundefs) B2 (nm : nat) (x : var),
      num_occur_fdc (fundefs_ctx_append B1 B2) x nm ->
      exists n m : nat,
        num_occur_fds B1 x n /\ num_occur_fdc B2 x m /\ n + m = nm.
  Proof.
    induction B1; intros.
    - simpl in H. inv H.
      apply IHB1 in H8. destructAll.
      exists (n + x0), x1. split.
      constructor; auto.
      split; auto. omega.
    - simpl in H. exists 0, nm.
      split; auto. constructor.
  Qed.

  Theorem rename_all_fun_ns_inlined_fundefs:
    forall sig im fds,
      (rename_all_fun_ns sig (inlined_fundefs_f fds im)) = (inlined_fundefs_f (rename_all_fun_ns sig fds) im).
  Proof.
    induction fds; simpl. 
    - destruct (get_b v im).
      + auto.
      + simpl. rewrite IHfds. auto.
    - auto.
  Qed.     

  Theorem update_count_inlined_unaffected:
    forall v0 lx ly count,
      ~FromList lx v0 ->
      ~FromList ly v0 ->
      get_c v0 (update_count_inlined ly lx count) = get_c v0 count.
  Proof.
    induction lx; intros.
    destruct ly; simpl; auto.
    destruct ly. simpl. auto.
    simpl. erewrite IHlx.
    rewrite gdso. rewrite gdso. auto.
    intro; apply H. constructor; auto.
    intro; apply H0. constructor; auto.
    intro; apply H. constructor 2; auto.
    intro; apply H0. constructor 2; auto.
  Qed.
  
  Theorem  update_count_inlined_dom:
    forall v0 lx ly count,
      length lx = length ly ->
      FromList lx v0 ->
      Disjoint _ (FromList ly) (FromList lx) ->
      get_c v0
            (update_count_inlined ly lx count) = 0.
  Proof.
    induction lx; intros. 
    inv H0.
    destruct ly;  inv H.
    simpl.
    assert (Hlx := Decidable_FromList lx).
    inv Hlx. specialize (Dec v0). inv Dec.
    eapply IHlx. auto. auto. split; intro. intro.
    inv H1. specialize (H4 x). apply H4. inv H2. split; constructor 2; auto.
    inv H0.
    rewrite update_count_inlined_unaffected. rewrite gdso.  rewrite gdss. auto.
    inv H1. specialize (H0 v0). intro; subst. apply H0. split; constructor; auto.
    auto.
    inv H1. specialize (H0 v0). intro; apply H0. split. constructor 2; auto.
    constructor. auto.
    exfalso; auto.
  Qed.


  Theorem dead_occur_fds_le_antimon:
    forall im im' : b_map,
      b_map_le im im' ->
      forall (f : var) (f4 : fundefs),
        num_occur_fds (inlined_fundefs_f f4 im) f 0 ->
        num_occur_fds (inlined_fundefs_f f4 im') f 0.
  Proof.
    intros.
    assert (exists n, num_occur_fds (inlined_fundefs_f f4 im') f n) by apply e_num_occur_fds.
    destruct H1. assert (x <= 0).
    eapply num_occur_fds_le_antimon; eauto.
    apply le_n_0_eq in H2. subst; auto.
  Qed.


  Theorem range_map_set_list: forall {A} ly sig lx,
                                Included A (Range_map (set_list (combine lx ly) sig)) (Union _ (Range_map sig) (FromList ly)).
  Proof.
    induction ly.
    - intros. intro. intro. destruct lx; simpl in H; auto.
    - intros. destruct lx. simpl. auto with Ensembles_DB.
      simpl. intro. intro.
      inv H. destruct (var_dec x0 e). 
      + subst. rewrite M.gss in H0. inv H0. right; constructor; auto.
      + rewrite M.gso in H0 by auto.
        assert ( Range_map (set_list (combine lx ly) sig) x). exists x0; auto.
        apply IHly in H.
        inv H; auto. right. constructor 2; auto.
  Qed.      


  


  Inductive sum_range_n: list var -> list var -> exp -> var -> nat -> Prop :=
  | SRN_cons1: forall lx ly e v0 n m x,
                 sum_range_n lx ly e v0 n -> num_occur e x m -> sum_range_n (x::lx) (v0::ly) e v0 (m+n)
  | SRN_cons2: forall lx ly e v n y x,
                 sum_range_n lx ly e v n -> y <> v -> sum_range_n (x::lx) (y::ly) e v n
  | SRN_nil: forall e v,
               sum_range_n nil nil e v 0.



  Theorem e_sum_range_n:
    forall e v lx ly,
      length lx  = length ly ->
      exists n, sum_range_n lx ly e v n.
  Proof.
    induction lx; intros; destruct ly; inv H. exists 0; constructor.
    apply IHlx in H1. inv H1. destruct (var_dec v0 v).
    subst.
    assert (exists n, num_occur e a n) by apply e_num_occur.
    destruct H0. exists (x0+x). constructor; auto.
    exists x. constructor; auto.
  Qed.  

  Fixpoint sum_range lx ly count v0 :=
    match lx, ly with
      | x::lx', y::ly' =>
        if (var_dec v0 y) then              
          get_c x count + sum_range lx' ly' count v0
        else sum_range lx' ly' count v0
      | _, _ => 0
    end.

  Theorem sum_range_set2:
    forall x y v0 count lx ly,
      ~ FromList lx x ->
      sum_range lx ly (M.set x y count) v0 = sum_range lx ly count v0.
  Proof.
    induction lx.
    - intros. destruct ly; auto.
    - intros. destruct ly; auto.
      simpl. rewrite gdso. rewrite IHlx. reflexivity.
      intro; apply H. constructor 2; auto.
      intro; apply H. constructor; auto.
  Qed.

  (* *)
  Theorem update_count_sum_range:
    forall v0 e sig l l0 count n,
      num_occur_list (apply_r_list sig l) v0 <= get_c v0 count ->
      ~ FromList l0 v0 ->
      Disjoint _ (FromList (apply_r_list sig l)) (FromList l0) ->
      (forall x n, FromList l0 x ->
                   num_occur (rename_all_ns sig e) x n ->
                   get_c x count = n) ->
      sum_range_n l0 (apply_r_list sig l) (rename_all_ns sig e) v0 n ->
      NoDup l0 ->
      (get_c v0
             (update_count_inlined (apply_r_list sig l) l0 count ) = 
       get_c v0 count  + n - num_occur_list (apply_r_list sig l) v0).
  Proof.
    induction l; intros.
    - inv H3. simpl. omega.
    - inv H3.
      + simpl in H.
        simpl.
        destruct  (cps_util.var_dec (apply_r sig a) (apply_r sig a)).
        2: exfalso; auto.
        rewrite IHl with (n := n0); eauto.
        rewrite gdss.
        apply H2 in H12.
        rewrite H12. omega.
        constructor; auto.
        rewrite gdss. omega.
        intro; apply H0. constructor 2; auto.
        eapply Disjoint_Included.
        3: apply H1.
        intro; intro; constructor 2; auto.
        intro; intro; constructor 2; auto.
        intros. rewrite gdso. rewrite gdso.
        apply H2; eauto. constructor 2; auto. intro. inv H4; auto.
        intro. inv H1. specialize (H7 (apply_r sig a)). apply H7. split.
        constructor; auto. constructor 2; auto.
        inv H4; auto.
      + simpl.
        simpl in H.
        destruct ( cps_util.var_dec v0 (apply_r sig a)).
        exfalso; auto.
        rewrite IHl with (n := n).
        rewrite gdso by auto. rewrite gdso. reflexivity.
        intro; apply H0. constructor; auto.
        rewrite gdso by auto. rewrite gdso. simpl in H. auto. intro; apply H0. constructor; auto.
        intro; apply H0. constructor 2; auto.
        eapply Disjoint_Included. 3: apply H1.
        intro; intro; constructor 2; auto.
        intro; intro; constructor 2; auto.
        intros. rewrite gdso. rewrite gdso. apply H2.
        constructor 2; auto. auto. inv H4. intro; subst; auto.
        intro. inv H1. specialize (H7 (apply_r sig a)). apply H7. split.
        constructor. auto. constructor 2. auto.
        auto. inv H4; auto.
  Qed.
  
  
  

  Definition set_list_r {A:Type}  (l : list (M.elt * A)) (map: M.t A) : M.t A :=
    fold_left (fun cmap xv => M.set (fst xv) (snd xv) cmap ) l map.

  Theorem set_list_set:
    forall a v lx ly,
      NoDup (a::lx) ->
      forall (sig:M.t var),
        M.set a v (set_list (combine lx ly) sig) =mg=
        set_list (combine lx ly) (M.set a v sig).
  Proof.
    induction lx. intros. simpl. apply smg_refl.
    intros. destruct ly. simpl. apply smg_refl.
    simpl.  eapply smg_trans.
    Focus 2. apply proper_set.
    apply IHlx. inv H. inv H3. constructor; auto. intro; apply H2. constructor 2; auto.
    apply set_set. inv H. intro; apply H2; constructor; auto.
  Qed.  
  
  Theorem set_list_r_eq:
    forall lx ly,
      NoDup lx ->
      forall (sig:M.t var),
        set_list (combine lx ly) sig =mg=
        set_list_r (combine lx ly) sig.
  Proof.
    induction lx. intros. simpl. apply smg_refl.
    intros. destruct ly. apply smg_refl. 
    simpl. eapply smg_trans.
    2: apply IHlx. 
    apply set_list_set. auto. inv H; auto.
  Qed.


  Theorem num_occur_rename_all_set_dead_x:
    forall e x y m sig,
      x<> y ->
      ~ Dom_map sig x ->
      dead_var (rename_all_ns sig e) x ->
      num_occur (rename_all_ns sig e) y m ->
      num_occur (rename_all_ns (M.set x y sig) e) x 0 /\
      num_occur (rename_all_ns (M.set x y sig) e) y m.
  Proof.
    intros.
    split.
    
    assert (exists n,  num_occur (rename_all_ns (M.set x y sig) e) x n) by apply e_num_occur.
    destruct H3.
    assert (x0 <= 0).
    eapply (proj1 (num_occur_rename_all_ns_set _ _ _ H)).
    apply H1. apply H3. 
    assert (x0 = 0) by omega. subst; auto.
    assert (num_occur e x 0).
    eapply not_occur_rename_not_dom; eauto.
    erewrite (proj1 eq_P_rename_all_ns).
    apply H2.
    intro. intro. rewrite M.gso. auto.
    intro; subst; auto.
  Qed.  


  Theorem num_occur_set_arl_s:
    forall x y sig,
      x <> y ->
      ~ Dom_map sig x ->
      forall l,
        num_occur_list (apply_r_list (M.set x y sig) l) y =
        num_occur_list (apply_r_list sig l) y + num_occur_list l x.
  Proof.
    induction l. auto.
    simpl. destruct (cps_util.var_dec x a).
    - subst.
      rewrite apply_r_set1.
      destruct (cps_util.var_dec y y).
      Focus 2. exfalso. apply n; auto.
      rewrite Disjoint_apply_r.
      destruct (cps_util.var_dec y a). exfalso; auto.
      omega.
      split. intro. intro. inv H1. inv H2. apply H0. exists x0. inv H3; auto.
    - rewrite apply_r_set2 by auto.
      destruct (cps_util.var_dec y (apply_r sig a)); omega.
  Qed.    
  
  Theorem num_occur_rename_all_set_x:
    forall x y sig,
      x <> y ->
      ~ Dom_map sig x ->
      (forall e n m,
         num_occur e x n ->
         num_occur (rename_all_ns sig e) y m ->
         num_occur (rename_all_ns (M.set x y sig) e) y (n+m)) /\
      (forall fds n m,
         num_occur_fds fds x n ->
         num_occur_fds (rename_all_fun_ns sig fds) y m ->
         num_occur_fds (rename_all_fun_ns (M.set x y sig) fds) y (n+m)).
  Proof.
    intros x y sig Hxy Hdom.
    apply exp_def_mutual_ind; intros; simpl in *; try (inv H0; inv H1).
    - specialize (H _ _ H8 H7).
      eapply num_occur_n.
      constructor. eauto.
      rewrite num_occur_set_arl_s; auto.
      omega.
    - inv H; inv H0.
      inv H5; inv H4.
      eapply num_occur_n. constructor; eauto. constructor.
      assert (Hn := num_occur_set_arl_s _ _ _ Hxy Hdom [v]). 
      simpl in Hn. simpl. unfold var in *.
      omega.
    - inv H1; inv H2. inv H7; inv H6.
      specialize (H _ _ H8 H7).
      assert (num_occur (Ecase v l) x ( num_occur_list [v] x + m)).
      constructor; auto.
      assert (num_occur (Ecase (apply_r sig v) (rename_all_case sig l)) y ( num_occur_list [apply_r sig v] y + m0)).
      constructor; auto.
      specialize (H0 _ _ H1 H2).
      inv H0. 
      eapply num_occur_n.
      constructor. constructor; eauto.
      simpl. omega.      
    - specialize (H _ _ H9 H8).
      eapply num_occur_n. constructor; eauto. 
      assert (Hn := num_occur_set_arl_s _ _ _ Hxy Hdom [v0]).
      simpl in Hn. simpl. unfold var in *.
      omega.
    - inv H1; inv H2.
      specialize (H _ _ H8 H9).
      specialize (H0 _ _ H5 H4).
      eapply num_occur_n. constructor; eauto.
      omega.
    - inv H; inv H0.
      eapply num_occur_n. constructor; eauto.
      assert (Hn := num_occur_set_arl_s _ _ _ Hxy Hdom (v::l)).
      simpl in Hn. simpl.
      unfold var in *. omega.
    - specialize (H _ _ H8 H7).
      eapply num_occur_n. constructor. eauto.
      rewrite num_occur_set_arl_s; auto. omega.
    - inv H; inv H0.
      eapply num_occur_n. constructor.
      assert (Hn := num_occur_set_arl_s _ _ _ Hxy Hdom [v]).
      simpl in Hn. simpl. unfold var in *.
      omega.
    - inv H1; inv H2. specialize (H _ _ H10 H9).
      specialize (H0 _ _ H11 H12).
      eapply num_occur_fds_n. constructor; eauto. omega.  
    - inv H; inv H0. constructor.
  Qed.

  Theorem sum_range_length:
    forall v0 e lx ly n,
      sum_range_n lx ly e v0 n ->
      length lx = length ly.
  Proof.
    induction lx; intros. inv H; auto.
    inv H. apply IHlx in H2. simpl; auto.
    apply IHlx in H2. simpl; auto.
  Qed.

  Theorem sum_range_not_occur:
    forall v e ly lx,
      ~ FromList ly v ->
      length lx = length ly ->
      sum_range_n lx ly e v 0.
  Proof.
    induction ly; intros.
    - destruct lx; inv H0.
      constructor.
    - destruct lx; inv H0.
      constructor 2. apply IHly. intro; apply H.
      constructor 2; auto. auto.
      intro; apply H.
      constructor; auto.
  Qed.

  Theorem num_occur_set_list_r:
    forall  m v0 sig e lx ly n, 
      Disjoint _ (Dom_map sig) (FromList lx) -> 
      Disjoint _ (FromList lx) (FromList ly) ->
      NoDup lx ->
      Included _ (FromList lx) (Union _ (Complement _ (Range_map sig)) (dead_var (rename_all_ns sig e))) ->
      sum_range_n lx ly (rename_all_ns sig e) v0 n ->
      num_occur (rename_all_ns sig e) v0 m ->
      ~ FromList lx v0 ->
      num_occur (rename_all_ns (set_list (combine lx ly) sig) e) v0 (n + m).
  Proof.
    induction lx.
    - intros. inv H3. simpl.  auto.
    - intros.
      rename H5 into Hv0.
      inv H3.
      + simpl.
        assert (H7' := H7).
        eapply IHlx in H7; eauto.
        assert (FromList (a::lx) a) by (constructor; auto).
        apply H2 in H3. inv H3.
        * assert (num_occur e a m0).
          assert (exists n, num_occur e a n) by apply e_num_occur.
          destruct H3. assert (x = m0).
          eapply num_occur_sig_unaffected; eauto. 
          inv H. specialize (H6 a). intro. apply H6. split; auto. constructor; auto.
          subst; auto.
          replace (m0 + n0 + m) with (m0 + (n0 + m)) by omega.
          eapply num_occur_rename_all_set_x; eauto.
          inv H0. intro. specialize (H6 a). apply H6; subst.
          split; constructor; auto.
          intro. 
          apply Dom_map_set_list in H6.
          inv H6.  inv H1; auto. inv H. specialize (H6 a). apply H6; split; auto.
          constructor; auto.
          eapply sum_range_length; eauto.
        * assert (m0 = 0). eapply (proj1 (num_occur_det _)); eauto.
          subst.
          apply not_occur_rename_not_dom in H5.
          replace (0 + n0 + m) with (0 + (n0 + m)) by omega.
          eapply num_occur_rename_all_set_x; eauto.
          inv H0. intro. specialize (H3 a). subst. apply H3. split; constructor; auto.
          intro. apply Dom_map_set_list in H3. inv H3. inv H1; auto.
          inv H. specialize (H3 a). apply H3. split; auto. constructor; auto.
          eapply sum_range_length; eauto.
          intro. inv H. specialize (H6 a). apply H6. split; auto.
          constructor; auto.
        * eapply Disjoint_Included_r. 2: apply H.
          intro; intro. constructor 2; auto.
        * eapply Disjoint_Included. 3: apply H0. 
          intro; intro. constructor 2; auto.
          intro; intro. constructor 2; auto.
        *  inv H1; auto.
        *    intro. intro; apply H2; constructor 2; auto.
        * intro; apply Hv0. constructor 2; auto.
      + simpl.
        inv H1.
        assert (H7' := H7).
        apply IHlx in H7; auto.
        assert (exists n,  num_occur (rename_all_ns (M.set a y (set_list (combine lx ly0) sig)) e) v0 n) by apply e_num_occur. destruct H1.
        assert ((n + m) = x).
        eapply num_occur_rename_all_ns_set_unchanged.  4: apply H7.
        4: apply H1. intro.
        apply  Dom_map_set_list in H3. inv H3; auto.
        inv H. specialize (H3 a). apply H3. split; auto.
        constructor; auto.
        apply sum_range_length in H7'. auto.
        intro; apply Hv0. constructor; auto.
        auto.
        rewrite H3. auto.
        eapply Disjoint_Included_r. 2: apply H. intro; intro. constructor 2; auto.
        eapply Disjoint_Included.
        3: apply H0.
        intro; intro; constructor 2; auto.
        intro; intro; constructor 2; auto.
        intro; intro; apply H2. constructor 2; auto.
        intro; apply Hv0. constructor 2; auto.
  Qed.

  (** update_count_inlined correctly updates the count after inlining a function *)
  Theorem count_inlining:
    forall sig x x1 v f l0 e x2 x0 l count inl,
      let ce := (rename_all_ctx_ns sig
                                   (inlined_ctx_f
                                      (comp_ctx_f x
                                                  (Efun1_c
                                                     (fundefs_append x1 (Fcons (apply_r sig v) f l0 e x2)) x0))
                                      inl) |[ Eapp (apply_r sig v) f (apply_r_list sig l) ]| ) in
      c_count ce  count ->
      closed ce ->
      unique_bindings ce ->
      get_b (apply_r sig v) inl = false ->
      sig_inv_full sig (rename_all_ctx_ns sig
                                          (inlined_ctx_f
                                             (comp_ctx_f x
                                                         (Efun1_c
                                                            (fundefs_append x1 (Fcons (apply_r sig v) f l0 e x2)) x0)) inl))  (rename_all_ns sig (Eapp v f l)) ->
      num_occur ce (apply_r sig v) 1 ->
      length l0 = length l ->
      c_count
        (rename_all_ctx_ns sig
                           (inlined_ctx_f (comp_ctx_f x (Efun1_c (fundefs_append x1 x2) x0)) inl)
        |[ rename_all_ns (set_list (combine l0 (apply_r_list sig l)) sig) e ]|)
        (update_count_inlined (apply_r_list sig l) l0
                              (M.set (apply_r sig v) 0 count)).
  Proof.
    intros.
    rename H4 into Hsv1.
    rename H5 into Hl0l.
    intro.
    assert (Hc_v0 := H v0).
    apply num_occur_app_ctx in Hc_v0. destructAll.


    assert (Disjoint _ [set apply_r sig v] (FromList l0)).
    { (* by unique bindings *)
      split; intros; intro. inv H7.
      inv H8.
      apply ub_app_ctx_f in H1; destructAll.
      repeat normalize_ctx.
      apply ub_comp_ctx_f in H1; destructAll.
      inv H10.
      repeat normalize_ctx.
      eapply fundefs_append_unique_bindings_l in H15.
      2: reflexivity.  destructAll.
      simpl in H12.  rewrite H2 in H12.
      inv H12. auto.    
    }
    
    assert (Disjoint _ (FromList  (apply_r_list sig l)) (FromList l0)).
    { (* due to unique_binding and closed *)
      split. intro. intro.
      inv H8.
      
      assert (occurs_free (rename_all_ns sig (Eapp v f l)) x5) by (constructor; auto).
      assert (~ occurs_free ce x5). intro. apply H0 in H11. inv H11.

      apply (proj1 (occurs_free_app_bound_stem _ _ H8)) in H11.
      
      unfold ce in H11.
      apply ub_app_ctx_f in H1; destructAll.

      repeat normalize_ctx.
      apply ub_comp_ctx_f in H1; destructAll.
      apply bound_stem_comp_ctx_mut in H11. inv H11.

      inv H15. specialize (H11 x5).
      apply H11. split.
      apply bound_stem_var. auto.

      constructor. repeat normalize_ctx.
      eapply fundefs_append_bound_vars. reflexivity.
      right. simpl. rewrite H2. constructor. auto.

      simpl in H16. inv H16.
      inv H14. repeat normalize_ctx.
      eapply fundefs_append_unique_bindings_l in H18.
      2: reflexivity. destructAll.

      eapply fundefs_append_name_in_fundefs in H19. 2: reflexivity.
      inv H19.

      inv H16.
      specialize (H19 x5). apply H19. split.
      apply name_in_fundefs_bound_var_fundefs. auto.
      simpl. rewrite H2. simpl. constructor. auto.

      simpl in H18. rewrite H2 in H18.
      simpl in H14. rewrite H2 in H14. inv H14.
      simpl in H18. inv H18.
      inv H14; auto.
      inv H28. specialize (H18 x5).
      apply H18.
      split; auto.
      apply name_in_fundefs_bound_var_fundefs. auto.
      simpl in H14. inv H14. inv H20.
      specialize (H11 x5). apply H11. split; auto.
      apply bound_stem_var; auto.
      apply bound_var_rename_all_ns_fundefs.
      repeat normalize_ctx.
      eapply fundefs_append_bound_vars.
      reflexivity. right.
      simpl. rewrite H2. constructor. auto.
    }
    assert (Disjoint _ (bound_var_ctx (rename_all_ctx_ns sig
                                                         (inlined_ctx_f (comp_ctx_f x (Efun1_c (fundefs_append x1 x2) x0)) inl))) (FromList l0)).
    {
      split; intro.
      intro.  inv H9.
      unfold ce in H1.    
      repeat normalize_ctx.
      apply ub_app_ctx_f in H1; destructAll.
      apply ub_comp_ctx_f in H1. destructAll.
      apply bound_var_ctx_comp_ctx in H10. inv H10.
      inv H14. specialize (H10 x5). apply H10. split; auto.
      simpl. constructor. repeat normalize_ctx.
      eapply fundefs_append_bound_vars. reflexivity.
      right. simpl. rewrite H2. constructor. auto.
      simpl in H15. inv H15.
      repeat normalize_ctx.
      eapply fundefs_append_bound_vars in H18. 2: reflexivity.    
      simpl in H13. inv H13.
      repeat normalize_ctx.
      eapply fundefs_append_unique_bindings_l in H17. 2: reflexivity.
      destructAll.   
      inv H18.
      inv H15. specialize (H18 x5).
      apply H18. split; auto. simpl. rewrite H2.
      constructor; auto.
      simpl in H13. rewrite H2 in H13. inv H13.
      inv H27. specialize (H13 x5). apply H13. split; auto.
      simpl in H13. inv H13. inv H19. specialize (H10 x5).
      apply H10. split; auto.
      repeat normalize_ctx.
      eapply fundefs_append_bound_vars. reflexivity. right. simpl. rewrite H2.
      constructor; auto.
    }    
    assert (Included _ (FromList l0) 
                     ( dead_var (rename_all_ctx_ns sig
                                                   (inlined_ctx_f
                                                      (comp_ctx_f x
                                                                  (Efun1_c
                                                                     (fundefs_append x1 x2) x0))
                                                      inl) |[ Eapp (apply_r sig v) f (apply_r_list sig l) ]| ))).
    { intro. intro. apply num_occur_app_ctx.
      unfold ce in *. repeat normalize_ctx.
      assert (Hx5_c: ~ bound_var_ctx (rename_all_ctx_ns sig (inlined_ctx_f x inl)) x5).
      intro. inv H9.
      specialize (H12 x5). apply H12.
      split; auto. apply bound_var_ctx_comp_ctx. auto.
      
      exists 0, 0. split; auto.
      - apply num_occur_ec_comp_ctx.
        exists 0, 0. split; auto.
        + apply not_bound_dead_or_free_ctx in Hx5_c. inv Hx5_c. auto.
          rewrite <- app_ctx_f_fuse in H0.
          apply closed_app_ctx in H0.
          apply H0 in H11. inv H11.
        + split; auto.
          assert (~ occurs_free (rename_all_ctx_ns sig
                                                   (inlined_ctx_f
                                                      (Efun1_c
                                                         (fundefs_append x1 (Fcons (apply_r sig v) f l0 e x2)) x0)
                                                      inl) |[ Eapp (apply_r sig v) f (apply_r_list sig l) ]|) x5).
          eapply not_occurs_free_ctx_not_bound.
          intro.
          rewrite <- app_ctx_f_fuse in H0. apply H0 in H11. inv H11.
          auto.
          
          apply not_occur_free_Efun in H11. inv H11.
          rewrite inlined_fundefs_append in H12.
          rewrite rename_all_ns_fundefs_append in H12.
          apply not_occurs_free_fundefs_append in H12.
          inv H12.
          rewrite inlined_fundefs_append in *.
          rewrite rename_all_ns_fundefs_append in *.
          assert (Hname_x5:
                    ~
                      In var
                      (name_in_fundefs
                         (fundefs_append (rename_all_fun_ns sig (inlined_fundefs_f x1 inl))
                                         (rename_all_fun_ns sig
                                                            (inlined_fundefs_f (Fcons (apply_r sig v) f l0 e x2) inl)))) x5).
          {
            intro.
            eapply fundefs_append_name_in_fundefs in H12. 2: reflexivity.
            inv H9. specialize (H15 x5).
            apply H15. split. apply bound_var_ctx_comp_ctx.
            right. constructor.
            repeat normalize_ctx.
            eapply fundefs_append_bound_vars. reflexivity.
            inv H12. left. 
            apply name_in_fundefs_bound_var_fundefs. auto.
            simpl in H9. rewrite H2 in H9. simpl in H9. inv H9.
            exfalso. inv H7. specialize (H9 x5). apply H9. split; auto.
            right. apply name_in_fundefs_bound_var_fundefs; auto.
            auto.
          }
          assert (H11' :
                    In var
                       (Complement var (occurs_free_fundefs
                                          (rename_all_fun_ns sig (inlined_fundefs_f x1 inl)))) x5).
          intro. apply H11. split; auto. 
          clear H11.
          
          assert (H13' :
                    In var
                       (Complement var
                                   (occurs_free
                                      (rename_all_ctx_ns sig (inlined_ctx_f x0 inl)
                                      |[ Eapp (apply_r sig v) f (apply_r_list sig l) ]|))) x5).
          intro. apply H13. split; auto.  clear H13.
          assert (H14' :
                    In var
                       (Complement var
                                   (occurs_free_fundefs
                                      (rename_all_fun_ns sig
                                                         (inlined_fundefs_f (Fcons (apply_r sig v) f l0 e x2)
                                                                            inl)))) x5).
          intro. apply H14. split; auto.  clear H14.

          eapply Complement_Proper in H14'.
          Focus 2. simpl. rewrite H2.
          simpl.  
          symmetry. apply occurs_free_fundefs_Fcons.
          assert (H14'' : In var (Complement var
                                             (occurs_free_fundefs
                                                (rename_all_fun_ns sig (inlined_fundefs_f x2 inl)))) x5).
          intro. apply H14'. right. split; auto.
          intro. inv H7. specialize (H13 x5). apply H13; auto. 
          clear H14'.
          apply not_free_dead_or_bound in H13'. inv H13'.
          Focus 2. exfalso. inv H9. specialize (H12 x5). apply H12. split; auto. 
          apply bound_var_ctx_comp_ctx. right. simpl. apply identifiers.Bound_Fun12_c.
          apply bound_var_app_ctx in H11. inv H11; auto. inv H9.
          
          apply not_free_bound_or_not_occur in H11'. inv H11'.
          Focus 2. exfalso. inv H9. specialize (H13 x5). apply H13. split; auto.
          apply bound_var_ctx_comp_ctx.
          right. constructor. rewrite inlined_fundefs_append.
          normalize_ctx.
          eapply fundefs_append_bound_vars.
          reflexivity. left; auto.

          apply not_free_bound_or_not_occur in H14''. inv H14''.
          Focus 2. exfalso. inv H9.  specialize (H14 x5). apply H14. split; auto. apply bound_var_ctx_comp_ctx.
          right. constructor. rewrite inlined_fundefs_append.
          normalize_ctx.
          eapply fundefs_append_bound_vars.
          reflexivity. auto.
          simpl. 
          eapply num_occur_ec_n. constructor.
          apply num_occur_app_ctx in H11; destructAll; pi0. eauto.
          repeat normalize_ctx. 
          eapply fundefs_append_num_occur.
          reflexivity. eauto. eauto.
          auto. 
      - split. eapply num_occur_n.
        constructor.
        assert (num_occur_list (apply_r_list sig l) x5 = 0).
        apply not_occur_list_not_in. intro. inv H8.
        specialize (H12 x5). apply H12; auto.
        assert (num_occur_list [apply_r sig v] x5 = 0).
        apply not_occur_list_not_in. intro. inv H7.
        specialize (H13 x5). apply H13. split; auto.
        inv H12. constructor. inv H7.
        simpl in *. rewrite H11. omega.
        auto.
    }
    assert (forall vx n m, FromList l0 vx ->
                           num_occur ce vx n ->
                           num_occur (rename_all_ns sig e) vx m ->
                           n = m).
    {
      intros.
      apply num_occur_app_ctx in H12. destructAll.
      apply H10 in H11. apply num_occur_app_ctx in H11. destructAll; pi0.
      assert (x6 = 0). eapply (proj1 (num_occur_det _)); eauto. subst.

      repeat normalize_ctx.
      apply num_occur_ec_comp_ctx in H11; destructAll; pi0.
      apply num_occur_ec_comp_ctx in H12. destructAll.
      assert (x6 = 0). eapply num_occur_ec_det; eauto.
      subst.
      simpl in *. inv H16; pi0.
      inv H17. assert (n = 0). eapply num_occur_ec_det; eauto.
      subst.
      repeat normalize_ctx.
      apply fundefs_append_num_occur' in H24. destructAll.
      apply fundefs_append_num_occur' in H23; destructAll; pi0.
      assert (x5 = 0). eapply (proj2 (num_occur_det _)); eauto. subst.
      simpl in H17. rewrite H2 in H17. inv H17.
      assert (m0 = 0). eapply (proj2 (num_occur_det _)); eauto. subst.
      simpl. do 2 (rewrite plus_0_r).
      eapply (proj1 (num_occur_det _)); eauto. 
    }    
    assert (Hl0 := Decidable_FromList l0). destruct Hl0.
    specialize (Dec v0). inv Dec.


    (* x5 is in l0 *)
    apply num_occur_app_ctx. exists 0, 0. split.
    apply H10 in H12. apply num_occur_app_ctx in H12; destructAll; pi0.
    auto.
    split.
    { assert  (Hl0 := Decidable_Range_map sig).
      inv Hl0. specialize (Dec v0). destruct Dec.
      - inv H13. apply H3 in H14. destructAll.
        inv H14.
        + apply dead_occur_rename_all_ns_set_list.
          inv H8. intro. specialize (H14 v0).
          apply H14; auto.
          apply num_occur_app_ctx in H15. destructAll; pi0.
          repeat normalize_ctx.
          apply num_occur_ec_comp_ctx in H14.
          destructAll; pi0.
          inv H16; pi0.
          repeat normalize_ctx.
          apply fundefs_append_num_occur' in H22.
          destructAll; pi0.
          simpl in H17. rewrite H2 in H17. inv H17; pi0. auto.
        + exfalso. inv H9. specialize (H14 v0). apply H14. repeat normalize_ctx. split; auto.
          apply bound_var_ctx_comp_ctx. 
          apply bound_stem_comp_ctx_mut in H15. destruct H15. left.
          apply bound_stem_var; auto.
          simpl in H9. right. inv H9.
          constructor.
          repeat normalize_ctx.
          eapply fundefs_append_bound_vars. reflexivity.
          eapply fundefs_append_name_in_fundefs in H18. 2: reflexivity.        
          inv H18. left. apply name_in_fundefs_bound_var_fundefs. auto.
          simpl in H9. rewrite H2 in H9. inv H9. exfalso. inv H7. specialize (H9 x6).
          apply H9; auto.
          right. apply name_in_fundefs_bound_var_fundefs. auto.
          apply bound_var_Fun1_c. right. apply bound_stem_var. auto.
      - apply num_occur_rename_all_ns_kill.
        intro. apply range_map_set_list in H14. inv H14. auto.
        inv H8. specialize (H14 v0). apply H14; auto.
        apply Dom_map_set_list.
        rewrite length_apply_r_list. auto.  auto.
    }
    rewrite update_count_inlined_dom. auto.
    rewrite length_apply_r_list. auto.
    auto. auto.
    
    assert (exists n, sum_range_n l0 (apply_r_list sig l) (rename_all_ns sig e) v0 n).
    apply e_sum_range_n. rewrite length_apply_r_list. auto.
    destruct H13.
    assert (Hn_v0 := H v0).
    apply num_occur_app_ctx in Hn_v0; destructAll. repeat normalize_ctx.
    apply num_occur_ec_comp_ctx in H14. destructAll. repeat normalize_ctx.
    simpl in H17. inv H17. repeat normalize_ctx.
    apply fundefs_append_num_occur' in H23. destructAll. simpl in H18. rewrite H2 in H18. inv H18.
    inv H15. simpl in H16.

    assert (Hnd_l0 : NoDup l0). apply ub_app_ctx_f in H1; destructAll; repeat normalize_ctx.
    apply ub_comp_ctx_f in H1; destructAll; repeat normalize_ctx. inv H19.
    repeat normalize_ctx. eapply fundefs_append_unique_bindings_l in H25. 2: reflexivity.
    destructAll. simpl in H22; rewrite H2 in H22. inv H22. auto.

    
    apply num_occur_app_ctx.  eexists. eexists.
    split. apply num_occur_ec_comp_ctx. eexists. eexists. split; eauto.
    split. simpl. constructor. eauto. repeat normalize_ctx.
    eapply fundefs_append_num_occur. reflexivity. eauto. eauto. reflexivity.
    split.
    apply num_occur_set_list_r.
    split; intro. intro. destruct H15.
    inv H15. apply H3 in H19.  destructAll. apply H15.
    apply bound_var_app_ctx. left. apply bound_var_ctx_comp_ctx. right. constructor.
    repeat normalize_ctx.  eapply fundefs_append_bound_vars. reflexivity. right. simpl. rewrite H2.
    constructor. auto. 
    auto with Ensembles_DB. auto. 
    {
      intro. intro. assert (Hsr := Decidable_Range_map sig). inv Hsr. specialize (Dec x7).
      destruct Dec; auto.
      right. inv H18. apply H3 in H19. destructAll. inv H19.
      apply num_occur_app_ctx in H21; destructAll; pi0.
      apply num_occur_ec_comp_ctx in H19; destructAll; pi0.
      simpl in H22. inv H22; pi0. repeat normalize_ctx.
      eapply fundefs_append_num_occur' in H30.  destructAll; pi0.
      simpl in H23. rewrite H2 in H23. inv H23; pi0. auto.
      exfalso.
      inv H9. specialize (H19 x7). apply H19.
      split; auto. apply bound_stem_comp_ctx_mut in H21.
      apply bound_var_ctx_comp_ctx.
      inv H21. left. apply bound_stem_var; auto.
      right. simpl in *.  inv H9.
      constructor.
      repeat normalize_ctx. eapply fundefs_append_name_in_fundefs in H24. 2: reflexivity.
      apply name_in_fundefs_bound_var_fundefs. eapply fundefs_append_name_in_fundefs. reflexivity.
      inv H24; auto. simpl in H9. rewrite H2 in H9. simpl in H9. inv H9.
      exfalso. inv H7. specialize (H9 x7). apply H9; auto.
      auto.
      apply bound_stem_var in H24. auto.        
    }
    apply H13. apply H27. auto.
    erewrite update_count_sum_range; eauto.

    destruct (cps_util.var_dec v0 (apply_r sig v)).
    (* apply_r sig v *) subst. rewrite gdss.
    specialize (H (apply_r sig v)). assert ( (get_c (apply_r sig v) count) = 1).
    eapply (proj1 (num_occur_det _)); eauto. rewrite H16 in H15. clear H16.
    assert (x8 + (n + (x6 + (n0 + m)))  = 0) by omega. pi0.
    assert (num_occur_list (apply_r_list sig l) (apply_r sig v) = 0) by omega. rewrite H16. omega.
    
    rewrite gdso by auto. unfold maps_util.getd.  unfold get_c in H16. rewrite H16.
    omega.

    destruct (cps_util.var_dec v0 (apply_r sig v)).
    subst. rewrite gdss.
    specialize (H (apply_r sig v)). assert ( (get_c (apply_r sig v) count) = 1).
    eapply (proj1 (num_occur_det _)); eauto.
    rewrite H15 in H. apply num_occur_app_ctx in H; destructAll. inv H18.
    simpl in H19. destruct  (cps_util.var_dec (apply_r sig v) (apply_r sig v)). omega.
    exfalso; auto.
    rewrite gdso by auto. unfold get_c in H16; unfold maps_util.getd. omega.

    intros. rewrite gdso. specialize (H x7). specialize (H11 _ _ _ H15 H H18). auto.
    intro. inv H7. specialize (H21 (apply_r sig v)). apply H21. split; auto. 
  Qed.

  
  (** postcontractfun reduces or preserves the names of functions *)
  Theorem postcontractfun_name_in_fundefs:
    forall {fds_c  im sub count sig},
    forall {oes fds_c' count' im' pfe pfsub bp},
      postcontractfun oes (fun rm cm es H => contract rm cm (fst (fst es)) (snd (fst es)) (snd es)) sig count im sub fds_c pfe pfsub = existT _ (fds_c', count', im')  bp ->
      (Included _ (name_in_fundefs fds_c') (name_in_fundefs fds_c)).
  Proof.
    induction fds_c; intros.
    - simpl in H.
      destruct (get_b v im).
      + apply IHfds_c in H.
        simpl. auto with Ensembles_DB.
      + destruct (get_c v count).
        apply IHfds_c in H.
        simpl. auto with Ensembles_DB.
        destruct (contract sig count e sub im).
        destruct x. destruct p.
        remember  (postcontractfun oes
                                   (fun (rm : r_map) (cm : c_map)
                                        (es : prod (prod exp ctx_map) b_map)
                                        (_ : lt (term_sub_inl_size es) (term_sub_inl_size oes)) =>
                                      contract rm cm
                                               (@fst exp ctx_map (@fst (prod exp ctx_map) b_map es))
                                               (@snd exp ctx_map (@fst (prod exp ctx_map) b_map es))
                                               (@snd (prod exp ctx_map) b_map es)) sig c b0 sub fds_c
                                   (@subfds_Fcons v f l e fds_c
                                                  (@fst exp ctx_map (@fst (prod exp ctx_map) b_map oes))
                                                  (@eq_ind_r fundefs (Fcons v f l e fds_c)
                                                             (fun x : fundefs =>
                                                                subfds_e x
                                                                         (@fst exp ctx_map (@fst (prod exp ctx_map) b_map oes)))
                                                             pfe (Fcons v f l e fds_c)
                                                             (@eq_refl fundefs (Fcons v f l e fds_c))))
                                   (@tsis_sub_pcf' sub im
                                                   (@snd exp ctx_map (@fst (prod exp ctx_map) b_map oes))
                                                   (@snd (prod exp ctx_map) b_map oes) b0 pfsub b)).
        destruct s. destruct x. destruct p. symmetry  in Heqs.
        apply IHfds_c in Heqs.
        inv H. simpl. auto with Ensembles_DB.
    - simpl in H. inv H. auto with Ensembles_DB.
  Qed.      

(** postcontractfun removes dead functions and processed the terms according to the shrink rewrite system. Also, none of the functions in fds and fds_c are ever eligible to be inlined *)
  Theorem postcontractfun_corresp:
    forall fds_c fds e c im sub count sig,
      (* recursive call to shrink_corresp *)
      (forall eb sub' im' sig c count,
         (term_sub_inl_size (eb, sub', im') < funs_size fds_c + sub_inl_size sub im) ->  
         let ce := (app_ctx_f (rename_all_ctx_ns sig (inlined_ctx_f c im')) (rename_all_ns sig eb)) in
         unique_bindings ce ->
         closed ce ->
         c_count ce count ->
         cmap_view_ctx sub' c ->
         inl_inv im' sub' ce ->
         sig_inv_full sig (rename_all_ctx_ns sig (inlined_ctx_f c im')) (rename_all_ns sig eb) ->
         forall e' count' im'' BP,
           contract sig count eb sub' im' = existT _ (e', count', im'') BP ->
           let ce' := (app_ctx_f (rename_all_ctx_ns sig (inlined_ctx_f c im'')) e') in
           gsr_clos ce ce' /\ c_count ce' count' /\ inl_inv im'' sub' ce' /\
           sig_inv_codom sig (rename_all_ctx_ns sig (inlined_ctx_f c im'')) e') ->
      (* actual statement for postcontractfun *)        
      let ce := (app_ctx_f (rename_all_ctx_ns sig (inlined_ctx_f (comp_ctx_f c (Efun1_c (fundefs_append fds fds_c) Hole_c)) im)) (rename_all_ns sig e)) in
      (Disjoint _ (name_in_fundefs fds) (Dom_map_b im)) ->
      unique_bindings ce ->
      closed ce -> 
      c_count ce count ->
      cmap_view_ctx sub c ->
      inl_inv im sub ce ->
      sig_inv_full sig (rename_all_ctx_ns sig (inlined_ctx_f (comp_ctx_f c (Efun1_c (fundefs_append fds fds_c) Hole_c)) im)) (rename_all_ns sig e) ->
      forall oes fds_c' count' im' pfe pfsub bp,
        postcontractfun oes (fun rm cm es H => contract rm cm (fst (fst es)) (snd (fst es)) (snd es)) sig count im sub fds_c pfe pfsub = existT _ (fds_c', count', im')  bp ->
        let ce' := (app_ctx_f (rename_all_ctx_ns sig (inlined_ctx_f (comp_ctx_f c (Efun1_c (fundefs_append fds fds_c') Hole_c)) im')) (rename_all_ns sig e)) in
        gsr_clos ce ce' /\ c_count ce' count' /\ inl_inv im' sub ce' /\
        sig_inv_codom sig (rename_all_ctx_ns sig (inlined_ctx_f (comp_ctx_f c (Efun1_c (fundefs_append fds fds_c') Hole_c)) im')) (rename_all_ns sig e) /\ (rename_all_fun_ns sig (inlined_fundefs_f fds_c' im') = fds_c') /\ (Disjoint _ (name_in_fundefs fds) (Dom_map_b im')).
  Proof.
    induction fds_c;
    intros fds e0 c im sub count sig Hcontract_corresp ce Hdjfds;
    intros.
    Focus 2. 
    simpl in H5. inv H5.
    unfold ce in *; unfold ce'.
    split; auto.
    apply rt_refl.
    split; auto. split; auto.
    apply sig_inv_combine in H4. destruct H4. auto.
    
    simpl in H5.
    destruct (get_b v im) eqn:gbvim.
    - (* get_b v im = true *)
      assert (
          (inlined_ctx_f
             (comp_ctx_f c
                         (Efun1_c (fundefs_append fds (Fcons v f l e fds_c)) Hole_c))
             im) =
          (inlined_ctx_f
             (comp_ctx_f c (Efun1_c (fundefs_append fds fds_c) Hole_c))
             im)).
      { do 2 (rewrite (proj1 inlined_comp_ctx)).
        simpl.
        do 2 (rewrite inlined_fundefs_append).
        simpl.
        rewrite gbvim.
        reflexivity.
      }
      unfold ce in *.
      rewrite H6 in *.        
      eapply IHfds_c in H5; eauto. 
      intros. eapply Hcontract_corresp; eauto.
      etransitivity. apply H7. simpl.
      omega.

    - (* get_b v im = false *)
      destruct (get_c v count) eqn:gvc.
      + (* get_c v count = 0 i.e. dead fun *)
        assert (Hgsr_dead: gsr_clos ce (rename_all_ctx_ns sig
                                                          (inlined_ctx_f
                                                             (comp_ctx_f c
                                                                         (Efun1_c (fundefs_append fds fds_c) Hole_c))
                                                             im) |[ rename_all_ns sig e0 ]|)).
        {
          (* by Fun_rem_s *)
          unfold ce.
          do 2 (rewrite (proj1 inlined_comp_ctx)).
          simpl.
          do 2 (rewrite inlined_fundefs_append).
          simpl. rewrite gbvim.
          do 2 (rewrite (proj1 (rename_all_ctx_ns_comp_ctx _ _))).
          do 2 (rewrite <- app_ctx_f_fuse).
          constructor. constructor.
          simpl.
          do 2 (rewrite rename_all_ns_fundefs_append).
          simpl.
          apply Fun_rem_s.
          specialize (H1 v).
          rewrite gvc in H1.
          unfold ce in H1.
          rewrite (proj1 inlined_comp_ctx) in H1.
          simpl in H1.
          rewrite (inlined_fundefs_append) in H1.
          rewrite (proj1 (rename_all_ctx_ns_comp_ctx _ _)) in H1.
          rewrite <- app_ctx_f_fuse in H1.
          apply num_occur_app_ctx in H1.
          destructAll; pi0.
          simpl in H6.
          rewrite rename_all_ns_fundefs_append in H6.
          rewrite gbvim in H6.
          simpl in H6.
          auto.
        }
        assert (Ht := gsr_preserves_clos _ _ H H0 Hgsr_dead).
        destruct Ht as (Hub_dead, Hdj_dead).
        apply sig_inv_combine in H4. destruct H4 as (H4, H4c).
        assert (Hsig_dead := gsr_preserves_sig_dom _ _ _ H H0 Hgsr_dead H4).
        
        (* I.H. *)
        eapply IHfds_c in H5; eauto.
        * destructAll.
          unfold ce'; split; auto.
          eapply rt_trans; eauto.
        * intros.
          eapply Hcontract_corresp; eauto.
          etransitivity. apply H6. simpl.
          omega.
        * intro.
          specialize (H1 v0).
          unfold ce in H1.
          repeat normalize_ctx.
          apply num_occur_app_ctx in H1.
          destructAll.
          apply num_occur_ec_comp_ctx in H1.
          destructAll.
          simpl in H8.
          repeat normalize_ctx.
          inv H8.
          rewrite gbvim in H14.
          apply fundefs_append_num_occur' in H14. destructAll.
          simpl in H9. inv H9.
          eapply num_occur_n.
          apply num_occur_app_ctx. eexists; eexists.
          split.
          apply num_occur_ec_comp_ctx.
          eexists; eexists.
          split; eauto.
          simpl.
          repeat normalize_ctx.
          split. constructor; eauto.
          eapply fundefs_append_num_occur.  reflexivity.
          eauto. eauto.
          reflexivity.
          split; eauto.
          unfold dec_census.
          
          rewrite <- ((proj1 combine_minus_census_correct) _ _ _).
          rewrite gccombine_sub. rewrite H7.
          assert (get_c v0 (init_census (rename_all_ns sig e)) = n0).
          eapply (proj1 (num_occur_det _)).
          apply init_census_correct. auto.
          rewrite H9. omega.  
        * intro. intro.
          apply H3 in H6.
          unfold ce in H6.
          destruct H6.
          split.
          {
            intro.
            apply H6.
            apply bound_var_app_ctx in H8.
            apply bound_var_app_ctx.
            inv H8.
            left.
            repeat (normalize_ctx; simpl).
            rewrite gbvim.
            simpl.
            rewrite (proj1 (bound_var_ctx_comp_ctx)).
            rewrite (proj1 (bound_var_ctx_comp_ctx)) in H9.
            inv H9; auto.
            right.
            normalize_bound_var_ctx'.
            simpl in H8.
            repeat (normalize_ctx; simpl).
            rewrite fundefs_append_bound_vars.
            2: reflexivity.
            normalize_bound_var.
            normalize_bound_var_ctx_in_ctx'.
            rewrite fundefs_append_bound_vars in H8.
            2: reflexivity.
            destruct H8.
            left. 
            destruct H8; auto.
            auto.
            right. auto.              
          }
          {
            intros.
            apply H7 in H8.
            eapply Disjoint_Included_l.
            2: apply H8.
            repeat (normalize_ctx; simpl).
            do 2 (rewrite bound_var_app_ctx).
            do 2 (rewrite (proj1 bound_var_ctx_comp_ctx)).
            repeat normalize_bound_var_ctx'.
            rewrite fundefs_append_bound_vars.
            2: reflexivity.
            intro. intros.
            rewrite fundefs_append_bound_vars.
            2: reflexivity.
            rewrite gbvim.
            simpl.
            repeat normalize_bound_var.
            destruct H9; auto.
            destruct H9; auto.
            destruct H9; auto.
            destruct H9; auto.
            eauto 25 with Ensembles_DB.
          }
        * apply sig_inv_combine. split; auto.
          intro. intros.
          apply H4c in H6.
          inv H6.
          left.
          apply num_occur_app_ctx in H7. destructAll; pi0.
          repeat normalize_ctx.
          apply num_occur_ec_comp_ctx in H6.
          destructAll; pi0.
          simpl in H8. inv H8; pi0.
          rewrite inlined_fundefs_append in H14.
          rewrite rename_all_ns_fundefs_append in H14.
          apply fundefs_append_num_occur' in H14.
          destructAll; pi0.
          simpl in H9. rewrite gbvim in H9. simpl in H9. inv H9; pi0.
          simpl.
          apply num_occur_app_ctx. exists 0, 0.
          split; auto. apply num_occur_ec_comp_ctx. exists 0, 0.
          split; auto. split; auto.
          eapply num_occur_ec_n.
          constructor. constructor.
          rewrite inlined_fundefs_append.
          rewrite rename_all_ns_fundefs_append.
          eapply fundefs_append_num_occur.
          reflexivity.
          eauto. eauto. auto.                        
          (* either  y = v and y is dead in ce OR y <> v and y is bound stem *)
          repeat normalize_ctx.
          apply bound_stem_comp_ctx_mut in H7.
          inv H7.
          right.
          apply bound_stem_comp_ctx_mut. left; auto.
          simpl in H6. inv H6.
          rewrite inlined_fundefs_append in H10.
          rewrite rename_all_ns_fundefs_append in H10. simpl in H10.
          rewrite gbvim in H10.            
          eapply fundefs_append_name_in_fundefs in H10.
          2: reflexivity.
          inv H10.
          (* fds *)
          right. apply bound_stem_comp_ctx_mut.
          right. simpl. constructor.
          repeat normalize_ctx.
          eapply fundefs_append_name_in_fundefs. reflexivity. auto.
          simpl in H6. inv H6. 
          (* v case, dead *)
          inv H7.
          left.
          specialize (H1 y).
          rewrite gvc in H1.
          apply num_occur_app_ctx in H1. destructAll; pi0.
          repeat normalize_ctx.
          apply num_occur_ec_comp_ctx_mut in H1.
          destructAll; pi0.
          simpl in H7. inv H7; pi0.
          repeat normalize_ctx.            
          apply fundefs_append_num_occur' in H13.
          destructAll; pi0.
          simpl in H8. rewrite gbvim in H8.
          simpl in H8. inv H8; pi0. simpl.
          apply num_occur_app_ctx. exists 0, 0. split; auto.
          apply num_occur_ec_comp_ctx_mut. exists 0, 0. split; auto.
          split; auto.
          eapply num_occur_ec_n. constructor; auto. constructor.
          repeat normalize_ctx. eapply fundefs_append_num_occur.
          reflexivity. eauto. eauto. auto.
          (* fds_c *)
          right. simpl.  apply bound_stem_comp_ctx_mut.
          right. simpl. constructor.
          repeat normalize_ctx.
          eapply fundefs_append_name_in_fundefs. reflexivity. auto.
          inv H10. 
      + (* get_c v count = (S n) *)
        (* contract on e *)
        remember  (contract sig count e sub im).
        destruct s.
        destruct x.
        destruct p.
        symmetry in Heqs.
        assert (
            rename_all_ctx_ns sig
                              (inlined_ctx_f
                                 (comp_ctx_f c
                                             (Efun1_c (fundefs_append fds (Fcons v f l e fds_c)) Hole_c))
                                 im) |[ rename_all_ns sig e0 ]| =
                                                                (rename_all_ctx_ns sig (inlined_ctx_f (comp_ctx_f c ( 
                                                                                                                    Efun2_c  (fundefs_ctx_append (inlined_fundefs_f fds im) (Fcons1_c v f l Hole_c (inlined_fundefs_f fds_c im))) e0)) im) |[ rename_all_ns sig e ]|)).
        { 
          do 2 (rewrite <- (proj1 (rename_all_ns_app_ctx _ _))).
          repeat normalize_ctx.
          simpl.
          do 2 (rewrite <- app_ctx_f_fuse).
          simpl.
          repeat normalize_ctx.
          simpl.
          rewrite gbvim.
          simpl.
          rewrite inlined_fundefs_ctx_append1.
          rewrite rename_all_fundefs_ctx_append.
          rewrite app_f_ctx_fundefs_ctx_append.
          simpl.
          reflexivity.
        }
        unfold ce in *; rewrite H6 in *.
        
        eapply Hcontract_corresp with (c := 
                                         (comp_ctx_f c
                                                     (Efun2_c
                                                        (fundefs_ctx_append (inlined_fundefs_f fds im)
                                                                            (Fcons1_c v f l Hole_c (inlined_fundefs_f fds_c im))) e0))) in Heqs; eauto.
        Focus 2. unfold term_sub_inl_size; simpl. omega. (* rewrite funs_size_append. simpl.
          omega. *)
        (*          eapply shrink_corresp in Heqs; eauto.  *)
        (* can add shallow Efun2_c *)
        2: (apply cmap_view_efun2; auto).
        
        
        (* I H *)
        destruct Heqs.
        destruct H8.
        assert (Ht := gsr_preserves_clos _ _ H H0 H7).
        destruct Ht as (Hub_post, Hdj_post).
        apply sig_inv_combine in H4.
        destruct H4 as (H4, H4c).
        rewrite H6 in H4.
        assert (Hsig_post := gsr_preserves_sig_dom _ _ _ H H0 H7 H4).
        
        destruct H9 as (H9, Hsig_r).

        assert (He1 : e1 = rename_all_ns sig e1).
        {
          rewrite <- (proj1 (rename_all_no_shadow _)).
          symmetry.
          apply rename_sig_dead.
          intro.             intros.
          apply Hsig_post in H10.
          apply not_bound_dead_or_free in H10.
          inv H10.
          2: apply Hdj_post in H11; inv H11.
          
          apply num_occur_app_ctx in H11.
          destructAll; pi0.
          auto.
          eapply sig_inv_dom_mon.
          2: apply Hsig_post.
          rewrite bound_var_app_ctx.
          right;
            auto.
        }
        
        
        assert
        ( (rename_all_ctx_ns sig
                             (inlined_ctx_f
                                (comp_ctx_f c
                                            (Efun2_c
                                               (fundefs_ctx_append (inlined_fundefs_f fds im)
                                                                   (Fcons1_c v f l Hole_c (inlined_fundefs_f fds_c im)))
                                               e0)) b0) |[ e1 ]|) =
          (rename_all_ctx_ns sig
                             (inlined_ctx_f
                                (comp_ctx_f c
                                            (Efun1_c
                                               (fundefs_append (fundefs_append fds (Fcons v f l e1 Fnil)) fds_c) Hole_c)) b0) |[ rename_all_ns sig e0 ]|)).
        { 
          rewrite He1 at 1.
          clear He1.
          repeat (normalize_ctx; simpl).
          destruct (get_b v b0) eqn:gvb0.
          - (* v wasn't eligible to be inlined *)
            apply H9 in gvb0.
            destructAll.
            exfalso.
            apply H10.
            apply bound_var_app_ctx.
            left.
            normalize_bound_var_ctx.
            right.
            simpl.
            normalize_bound_var_ctx.
            left.
            rewrite <- (proj2 (bound_var_ctx_rename_all_ns _)).
            apply bound_var_fundefs_ctx_append_f.
            apply name_in_fundefs_ctx_append.
            right. simpl. auto.
          - simpl.
            do 2 (rewrite <- app_ctx_f_fuse).
            simpl.
            assert ((inlined_fundefs_ctx_f
                       (fundefs_ctx_append (inlined_fundefs_f fds im)
                                           (Fcons1_c v f l Hole_c (inlined_fundefs_f fds_c im))) b0)  =
                    fundefs_ctx_append (inlined_fundefs_f fds b0)
                                       (Fcons1_c v f l Hole_c (inlined_fundefs_f fds_c b0))).
            {
              rewrite inlined_fundefs_ctx_append_shallow.
              erewrite eq_b_inlined_fundefs.
              erewrite eq_b_inlined_fundefs with (fds := fds_c).
              reflexivity.
              {
                intro.
                intro.
                destruct (get_b x b0) eqn:gxb0.
                destruct (get_b x im) eqn:gxim.
                reflexivity.
                
                (* prove that this is false *)
                exfalso.
                apply H9 in gxb0.
                destruct gxb0.
                apply H11.
                apply bound_var_app_ctx.
                left.
                apply bound_var_ctx_comp_ctx.
                right.
                simpl.
                rewrite inlined_fundefs_ctx_append_shallow.
                normalize_bound_var_ctx.
                left.
                rewrite <- (proj2 (bound_var_ctx_rename_all_ns  _)).
                rewrite bound_var_fundefs_ctx_append.
                right.
                apply bound_var_Fcons1_c.
                right. right.
                right.
                apply name_in_fundefs_not_inlined'; auto.

                destruct (get_b x im) eqn:gxim.
                assert (H' := b).
                apply b_map_le_c in H'.
                simpl in H'.
                apply H' in gxim.
                rewrite gxim in gxb0.  auto.
                reflexivity.
              } 
              {
                intro.
                intro.
                destruct (get_b x b0) eqn:gxb0.
                destruct (get_b x im) eqn:gxim.
                reflexivity.
                
                (* prove that this is false *)
                exfalso.
                apply H9 in gxb0.
                destruct gxb0.
                apply H11.
                apply bound_var_app_ctx.
                left.
                apply bound_var_ctx_comp_ctx.
                right.
                simpl.
                rewrite inlined_fundefs_ctx_append_shallow.
                normalize_bound_var_ctx.
                left.
                rewrite <- (proj2 (bound_var_ctx_rename_all_ns  _)).
                rewrite bound_var_fundefs_ctx_append.
                left.
                apply name_in_fundefs_not_inlined'; auto.

                destruct (get_b x im) eqn:gxim.
                assert (H' := b).
                apply b_map_le_c in H'.
                simpl in H'.
                apply H' in gxim.
                rewrite gxim in gxb0.  auto.
                reflexivity.
              } 
            }
            rewrite H10.
            rewrite rename_all_fundefs_ctx_append.
            simpl.
            rewrite app_f_ctx_fundefs_ctx_append. simpl.
            rewrite <- fundefs_append_assoc.
            simpl. reflexivity.
        }

        rewrite H10 in *.
        remember ( postcontractfun oes
                                   (fun (rm : r_map) (cm : c_map)
                                        (es : prod (prod exp ctx_map) b_map)
                                        (_ : lt (term_sub_inl_size es) (term_sub_inl_size oes)) =>
                                      contract rm cm
                                               (@fst exp ctx_map (@fst (prod exp ctx_map) b_map es))
                                               (@snd exp ctx_map (@fst (prod exp ctx_map) b_map es))
                                               (@snd (prod exp ctx_map) b_map es)) sig c0 b0 sub fds_c
                                   (@subfds_Fcons v f l e fds_c
                                                  (@fst exp ctx_map (@fst (prod exp ctx_map) b_map oes))
                                                  (@eq_ind_r fundefs (Fcons v f l e fds_c)
                                                             (fun x : fundefs =>
                                                                subfds_e x
                                                                         (@fst exp ctx_map (@fst (prod exp ctx_map) b_map oes)))
                                                             pfe (Fcons v f l e fds_c)
                                                             (@eq_refl fundefs (Fcons v f l e fds_c))))
                                   (@tsis_sub_pcf' sub im
                                                   (@snd exp ctx_map (@fst (prod exp ctx_map) b_map oes))
                                                   (@snd (prod exp ctx_map) b_map oes) b0 pfsub b)).
        destruct s.
        destruct x.
        destruct p.
        symmetry in Heqs.
        eapply IHfds_c  in Heqs; eauto.
        clear He1.
        destruct Heqs as (H11, Heqs).
        destruct Heqs as (H12, Heqs).
        destruct Heqs as (H13, Heqs).
        inv H5.
        unfold ce'.
        split; auto.
        eapply rt_trans.
        apply H7.
        rewrite <- fundefs_append_assoc in H11.
        rewrite <- fundefs_append_assoc in H11. simpl in H11.
        rewrite <- fundefs_append_assoc.  simpl.
        auto.
        split; auto.
        rewrite <- fundefs_append_assoc in H12.
        auto.
        rewrite <- fundefs_append_assoc in H13.
        split; auto.
        rewrite <- fundefs_append_assoc in Heqs. auto.
        destruct Heqs as (Heqs, Hf0).
        split; auto.
        { simpl.
          destruct (get_b v im') eqn:gbim'.
          -  (* v should not be eligible to be inlined *)
            exfalso.
            destruct Hf0.
            inversion H14. specialize (H15 v).
            apply H15. split.
            eapply fundefs_append_name_in_fundefs. reflexivity.
            right. constructor. auto.
            auto. 
          - destruct Hf0. split.
            + simpl. rewrite H5.
              assert (He1 : e1 = rename_all_ns sig e1).
              {
                clear H5.
                rewrite <- (proj1 (rename_all_no_shadow _)).
                symmetry.
                apply rename_sig_dead.
                intro.             intros.
                apply Hsig_post in H5.
                apply not_bound_dead_or_free in H5.
                inversion H5.
                2: apply Hdj_post in H15; inversion H15.
                rewrite <- H10 in H15.                  
                apply num_occur_app_ctx in H15.
                destructAll; pi0.
                auto.
                rewrite <- H10 in Hsig_post.
                eapply sig_inv_dom_mon.
                2: apply Hsig_post.
                rewrite bound_var_app_ctx.
                right;
                  auto.
              }
              rewrite <- He1.
              reflexivity.
            + eapply Disjoint_Included_l.
              2: apply H14.
              intro. intro.
              eapply fundefs_append_name_in_fundefs. reflexivity. auto.
        }
        { intros.
          eapply Hcontract_corresp; eauto.
          unfold term_sub_inl_size in *.
          simpl in *.
          etransitivity. 
          apply H11. 
          assert (sub_inl_size sub b0 <= sub_inl_size sub im).
          eapply sub_size_le.
          apply b_map_le_c; auto.
          omega.
        }
        { rewrite <- H10 in H9.
          split; intro.
          intro. destruct H11. apply H9 in H12.
          inversion H12. apply H13.
          apply bound_var_app_ctx. left.
          apply bound_var_ctx_rename_all_ns.
          rewrite (proj1 inlined_comp_ctx).
          apply bound_var_ctx_comp_ctx. right. simpl. 
          rewrite inlined_fundefs_ctx_append_shallow.
          constructor.
          eapply fundefs_append_name_in_fundefs in H11.
          2: reflexivity.
          apply bound_var_fundefs_ctx_append.
          inversion H11.
          - left.
            rewrite Disjoint_inlined_fds'.
            apply name_in_fundefs_bound_var_fundefs. auto.
            auto.
          - right. simpl in H15. inversion H15. inversion H17.  constructor.
            inversion H17.
        }
        {
          intro; intros.
          assert (H11' := H11).
          split.
          apply Hsig_post in H11. auto.
          apply Hsig_r in H11.
          inversion H11.
          - left.
            apply num_occur_app_ctx in H12.  destruct H12. destruct H12. inversion H12.
            inversion H14. pi0.
            destruct H14.
            clear H14.
            clear H16.
            rewrite He1 in H15.
            clear He1.
            subst.
            repeat normalize_ctx.
            apply num_occur_ec_comp_ctx in H13.
            destructAll; pi0.
            simpl in H17. inv H17; pi0.
            rewrite inlined_fundefs_ctx_append_shallow in H24.
            rewrite rename_all_fundefs_ctx_append in H24.
            apply fundefs_ctx_append_num_occur' in H24.
            destructAll; pi0.
            simpl in H18.  inv H18; pi0.
            apply num_occur_app_ctx. exists 0, 0.
            split; auto.
            apply num_occur_ec_comp_ctx.
            exists 0, 0.
            split; auto. split; auto.
            simpl.
            eapply num_occur_ec_n. constructor.
            eauto.
            rewrite inlined_fundefs_append.
            rewrite rename_all_ns_fundefs_append.
            eapply fundefs_append_num_occur.
            reflexivity.
            rewrite inlined_fundefs_append.
            rewrite rename_all_ns_fundefs_append.
            eapply fundefs_append_num_occur.
            reflexivity.
            rewrite rename_all_fun_ns_inlined_fundefs in H17.
            rewrite rename_all_fun_ns_inlined_fundefs.
            eapply dead_occur_fds_le_antimon. simpl in b.
            apply b_map_le_c. eauto. auto.
            simpl. destruct (get_b v b0).
            simpl. constructor. simpl. eapply num_occur_fds_n.
            constructor. eauto. constructor.
            auto.
            rewrite rename_all_fun_ns_inlined_fundefs in H29.
            rewrite rename_all_fun_ns_inlined_fundefs.
            eapply dead_occur_fds_le_antimon. simpl in b.
            apply b_map_le_c. eauto. auto.
            auto.
          - apply H4c in H11'.
            inversion H11'.
            + (* by no zombie *)
              rewrite <- H6 in H7.
              apply shrink_no_zombie in H7.
              apply H7 in H13. left; auto.
            + repeat normalize_ctx.                
              apply bound_stem_comp_ctx_mut in H12.
              inversion H12.
              right.
              apply bound_stem_comp_ctx_mut.
              left; auto.
              simpl in H14.
              inversion H14.
              rewrite inlined_fundefs_ctx_append_shallow in H19.
              (* if inlined by b0, then dead, o.w. name *)
              destruct (get_b y b0) eqn:gbvb0.
              * left.  apply H9 in gbvb0. destruct gbvb0.
                apply not_bound_dead_or_free in H20.
                inversion H20.
                auto.                  
                apply Hdj_post in H22.
                inv H22.
              * right. apply bound_stem_comp_ctx_mut. 
                right. simpl. constructor.
                rewrite rename_all_fun_ns_inlined_fundefs.
                apply name_in_fundefs_not_inlined; auto.
                rewrite rename_all_fundefs_ctx_append in H19. 
                apply name_in_fundefs_ctx_append in H19. 
                rewrite rename_all_ns_fundefs_append.
                eapply fundefs_append_name_in_fundefs.
                reflexivity.                  
                inversion H19.
                left.
                rewrite rename_all_ns_fundefs_append.
                eapply fundefs_append_name_in_fundefs. reflexivity. left.
                rewrite rename_all_fun_ns_inlined_fundefs in H20.                  
                eapply Included_name_in_fundefs_inlined. eauto. simpl in H20.
                inversion H20. inversion H22.
                left.                   rewrite rename_all_ns_fundefs_append.
                eapply fundefs_append_name_in_fundefs.
                reflexivity. right. simpl. auto.
                right.
                eapply Included_name_in_fundefs_inlined.
                rewrite rename_all_fun_ns_inlined_fundefs in H22. 
                eauto. 
              *  
                rewrite inlined_fundefs_ctx_append_shallow in H19.
                rewrite rename_all_fundefs_ctx_append in H19.
                apply  bound_stem_fundefs_append in H19. simpl in H19.
                rewrite bound_stem_Fcons1_c in H19. inversion H19.
                inversion H20.
                (* cannot be l because then violated unique_binding due to H13 *)
                apply bound_stem_comp_ctx_mut in H13. inversion H13.
                apply ub_app_ctx_f in H.
                destruct H.
                apply ub_comp_ctx_f in H. destruct H.
                destruct H25.
                inversion H26. 
                specialize (H27 y).  exfalso. apply H27.
                split. apply bound_var_stem_or_not_stem; auto.
                simpl. constructor.
                rewrite inlined_fundefs_ctx_append_shallow.
                rewrite rename_all_fundefs_ctx_append.
                apply bound_var_fundefs_ctx_append.
                right. simpl. constructor. auto.                

                simpl in H22. inversion H22.
                rewrite rename_all_fun_ns_inlined_fundefs in H27.
                {
                  (* either y is inlined in b0 (and not in im) and then it is dead, o.w. bound stem *)
                  destruct (get_b y b0) eqn:gbvb0.
                  * left.  apply H9 in gbvb0. destruct gbvb0.
                    apply not_bound_dead_or_free in H28.
                    inversion H28.
                    auto.                  
                    apply Hdj_post in H30.
                    inv H30.
                  * right. apply bound_stem_comp_ctx_mut. 
                    right. simpl. constructor.
                    rewrite rename_all_fun_ns_inlined_fundefs.
                    apply name_in_fundefs_not_inlined; auto.
                    apply Included_name_in_fundefs_inlined in H27.
                    rewrite <- fundefs_append_assoc. simpl.
                    repeat normalize_ctx.
                    eapply fundefs_append_name_in_fundefs in H27.
                    2: reflexivity.
                    eapply fundefs_append_name_in_fundefs. reflexivity.
                    inversion H27. auto. simpl in H28. inversion H28.
                    right; auto.
                    right. simpl. auto.
                }
                inversion H27. 
        }
        {
          intro. intros. assert (H7' := H7).
          apply H4 in H7.
          destruct H7.
          split.
          rewrite <- H6.
          auto.
          inv H8.
          - repeat normalize_ctx.
            apply num_occur_app_ctx in H9.
            destructAll; pi0.
            apply num_occur_ec_comp_ctx in H8.
            destructAll; pi0.
            simpl in H10. inv H10; pi0. repeat normalize_ctx.
            apply fundefs_append_num_occur' in H16. destructAll; pi0.
            simpl in H11. rewrite gbvim in H11. simpl in H11. inv H11; pi0.
            left.
            apply num_occur_app_ctx. exists 0, 0.
            split; auto.
            apply num_occur_ec_comp_ctx. exists 0, 0.
            split; auto.
            split; auto.
            simpl.
            eapply num_occur_ec_n.
            constructor; eauto.
            rewrite inlined_fundefs_ctx_append_shallow.               
            rewrite rename_all_fundefs_ctx_append.
            apply fundefs_ctx_append_num_occur; eauto.
            simpl. constructor. constructor.
            eauto. auto.              
          - right.
            repeat normalize_ctx.
            apply bound_stem_comp_ctx_mut in H9.
            apply bound_stem_comp_ctx_mut.
            inversion H9.
            + left. auto.
            + simpl in H8. inv H8.
              right. simpl. constructor.
              repeat normalize_ctx.
              eapply fundefs_append_name_in_fundefs in H14.
              2: reflexivity.
              rewrite inlined_fundefs_ctx_append_shallow.
              rewrite rename_all_fundefs_ctx_append.
              apply name_in_fundefs_ctx_append.
              inv H14.
              auto.
              right. simpl in H8. rewrite gbvim in H8.
              simpl in H8. simpl. auto.
              inv H14.
        }
  Qed.

(** dec_census_all_case removes all the occurences of variables in all branches from their respective tally in count *)
  Theorem dec_census_all_case_count: forall sig count v l n,
                                       num_occur_case (rename_all_case sig l) v n  ->
                                       get_c v (dec_census_all_case sig l count) = get_c v count - n.
  Proof.
    induction l; intros.
    - simpl.
      inv H. omega.
    - simpl. simpl in H. destruct a.
      inv H.
      unfold dec_census.
      apply IHl in H6. 
      assert (Hcc := combine_minus_census_correct).
      destruct Hcc. rewrite <- H.
      rewrite gccombine_sub.
      rewrite H6.
      assert (n0 = (get_c v (init_census (rename_all_ns sig e)))).
      eapply (proj1 (num_occur_det _)); eauto.
      apply init_census_correct.
      rewrite <- H1. omega.
  Qed.

  (** dec_census_case removes all the occurences of variables in all branches EXCEPT
      for the first branch matching the given tag from their respective tally in count  *)
  Theorem dec_census_case_count: forall sig v c0 e m count l n,
                                   num_occur_case (rename_all_case sig l) v n ->
                                   findtag l c0 = Some e ->
                                   num_occur (rename_all_ns sig e) v m ->
                                   get_c v (dec_census_case sig l c0 count) = get_c v count -  (n - m).
  Proof.
    induction l.
    intros. inv H0.
    intros. simpl in *.
    destruct a.
    destruct (var_dec v0 c0).
    - destruct (M.elt_eq v0 c0).
      2: exfalso; auto.
      subst. inv H0. inv H.
      eapply dec_census_all_case_count in H7.
      rewrite H7.
      assert (n0 = m).
      eapply (proj1 (num_occur_det _)); eauto.
      subst. omega.
    - destruct (M.elt_eq v0 c0).
      exfalso; auto.
      inv H. specialize (IHl _ H8 H0 H1).
      unfold dec_census.
      assert (Hcc := combine_minus_census_correct).
      destruct Hcc. rewrite <- H.
      rewrite gccombine_sub. rewrite IHl.
      assert (Hinc := init_census_correct).
      destruct Hinc. specialize (H3 (rename_all_ns sig e0)).
      specialize (H3 v).
      
      assert (get_c v (init_census (rename_all_ns sig e0)) = n2). eapply (proj1 (num_occur_det _)); eauto.
      rewrite H5.
      assert (m <= m0).
      eapply num_occur_case_le.
      apply findtag_In in H0.
      
      eapply in_map with (f := (fun (p:var*exp) => let (k, e) := p in
                                                   (k, rename_all_ns sig e))) in H0.
      apply H0.
      apply H8. auto.
      omega.
  Qed.

  (** dec_census_case properly updates the count after case folding *)
  Theorem c_count_fold_case:
    forall c c0 v e sig (l:list (cTag * exp)) count,
      c_count (c |[rename_all_ns sig (Ecase v l) ]|)  count ->
      findtag l c0 = Some e -> 
      c_count (c |[ rename_all_ns sig e ]|)
              (dec_census_case sig l c0 (dec_census_list sig [v] count)).
  Proof.
    intros. intro.
    specialize (H v0).
    apply num_occur_app_ctx in H.
    destructAll.
    assert (exists n, num_occur (rename_all_ns sig e) v0 n) by apply e_num_occur.
    destruct H3.
    apply num_occur_app_ctx. exists x, x1.
    split; auto. split; auto.
    inv H1. 
    erewrite dec_census_case_count; eauto.
    unfold dec_census_list. simpl.
    simpl in H2.
    assert (x1 <= n).
    {
      eapply num_occur_case_le. 2: apply H8.
      apply findtag_In in H0.        
      eapply in_map with (f := (fun (p:var*exp) => let (k, e) := p in
                                                   (k, rename_all_ns sig e))) in H0.
      apply H0. 
      auto.
    }
    destruct (cps_util.var_dec v0 (apply_r sig v)).
    - subst. rewrite gdss. rewrite H2.
      omega.
    - rewrite gdso by auto.
      unfold maps_util.getd.
      unfold get_c in H2.
      omega.
  Qed.
  

  (** main theorem! contract produces an output term related to the input by the shrink rewrite system. 
      The output count is correct for the output state, and the returned maps respect their respective invariant *)
  Theorem shrink_corresp:
    forall e sub im sig c count,
      let ce := (app_ctx_f (rename_all_ctx_ns sig (inlined_ctx_f c im)) (rename_all_ns sig e)) in
      unique_bindings ce ->
      closed ce ->
      c_count ce count ->
      cmap_view_ctx sub c ->
      inl_inv im sub ce ->
      sig_inv_full sig (rename_all_ctx_ns sig (inlined_ctx_f c im)) (rename_all_ns sig e) ->
      forall e' count' im' BP,
        contract sig count e sub im = existT _ (e', count', im') BP ->
        let ce' := (app_ctx_f (rename_all_ctx_ns sig (inlined_ctx_f c im')) e') in
        gsr_clos ce ce' /\ c_count ce' count' /\ inl_inv im' sub ce' /\
        sig_inv_codom sig (rename_all_ctx_ns sig (inlined_ctx_f c im')) e' .
  Proof.
    intros e sub inl. remember (1 + term_sub_inl_size (e, sub,inl)) as n. assert (n > term_sub_inl_size (e, sub, inl)). omega. clear Heqn. revert e sub inl H. induction n; intros. inversion H. destruct e; rewrite contract_eq in H6.
    - (* constr *)
      destruct (get_c v count) eqn:gvc.
      + (* dead constr *)
        simpl in ce.
        assert (gsr_clos ce (rename_all_ctx_ns sig (inlined_ctx_f c inl) |[ (rename_all_ns sig e) ]|)).
        { unfold ce.
          constructor. constructor.
          constructor.
          specialize (H2 v). unfold ce in H2.
          apply num_occur_app_ctx in H2. rewrite gvc in H2. destructAll; pi0.
          inv H7; pi0; auto. rewrite H8. auto.
        }
        assert (Hub := gsr_preserves_clos _ _ H0 H1 H7).
        destruct Hub as (Hub, Hdj).
        assert (H5' := H5).
        apply sig_inv_combine in H5.
        destruct H5 as (H5, H5cod).
        assert (Hse := gsr_preserves_sig_dom _ _ _ H0 H1 H7 H5).           
        simpl in H6.
        eapply IHn in H6; eauto.
        destruct H6.
        destruct H8.
        unfold ce'.
        split.
        eapply rt_trans.
        apply H7.
        auto.
        split; auto.
        unfold term_sub_inl_size in *. simpl in *.
        omega.
        {
          intro. specialize (H2 v0).
          unfold ce in H2.
          apply num_occur_app_ctx in H2. destructAll.
          inv H8.
          apply num_occur_app_ctx.
          exists x, n0.
          repeat split; auto.
          unfold dec_census_list.
          rewrite <- combine_minus_census_list.
          rewrite gccombine_sub.
          rewrite H9.
          rewrite update_census_list_correct.
          rewrite apply_r_list_empty.
          unfold get_c. rewrite M.gempty. omega.
        }
        intro. intros. apply H4 in H8.
        destructAll.
        assert (Included _ (bound_var (rename_all_ctx_ns sig (inlined_ctx_f c inl) |[ rename_all_ns sig e ]|)) (bound_var ce)).
        unfold ce.
        repeat rewrite bound_var_app_ctx.
        apply Included_Union_compat.
        reflexivity.
        rewrite bound_var_Econstr. left; auto.          
        split; auto.
        intro; apply H8.
        apply H10. auto.
        intros. apply H9 in H11.
        eapply Disjoint_Included_l.
        2: apply H11. auto.
        simpl in H5'.
        rewrite inv_app_Econstr in H5'.
        apply sig_inv_full_dead_l in H5'.
        auto.
      + (* live constr *)
        assert (M.get v sub = None) by (eapply sub_none_from_pre; simpl; eauto; simpl; auto).
        
        assert (rename_all_ctx_ns sig (inlined_ctx_f c inl)
               |[ rename_all_ns sig (Econstr v c0 l e)]|  =
                                                          (rename_all_ctx_ns sig (inlined_ctx_f (comp_ctx_f c (Econstr_c v c0 l Hole_c)) inl)
                                                          |[ rename_all_ns sig e ]|)) by ctx_inl_push.
        remember (contract sig count e (M.set v (SVconstr c0 l) sub) inl).
        symmetry in Heqs.
        destruct s.
        destruct x.
        destruct p.
        eapply IHn with (c := (comp_ctx_f c (Econstr_c v c0 l Hole_c))) in Heqs; unfold ce in *; try rewrite H8 in *; eauto.
        {
          destruct Heqs. destruct H10. destruct H11 as (H11, Hsig).
          assert (rename_all_ctx_ns sig (inlined_ctx_f c im')
                 |[ Econstr v c0 (apply_r_list sig l) e0 ]| = 
                                                            (rename_all_ctx_ns sig
                                                                               (inlined_ctx_f (comp_ctx_f c (Econstr_c v c0 l Hole_c)) im')
                                                            |[ e0 ]|)).              
          rewrite (proj1 inlined_comp_ctx).
          rewrite (proj1 (rename_all_ctx_ns_comp_ctx _ _)).              
          rewrite <- app_ctx_f_fuse.
          simpl. auto.            
          
          destruct (get_c v c1) eqn:gvc1.
          - (* dead post *)
            inv H6.
            split.
            2: split.
            + eapply rt_trans.
              apply H9.
              rewrite <- H12.
              unfold ce'.
              constructor.
              constructor.
              constructor.
              specialize (H10 v).
              rewrite gvc1 in H10.
              apply num_occur_app_ctx in H10; destructAll; pi0; auto.
            + intro. specialize (H10 v0).
              unfold ce'.
              apply num_occur_app_ctx in H10. destructAll.
              rewrite (proj1 inlined_comp_ctx) in H6.
              rewrite (proj1 (rename_all_ctx_ns_comp_ctx _ _)) in H6.
              
              apply num_occur_ec_comp_ctx in H6; destructAll.
              simpl in H14. inv H14. inv H21. simpl in H13.                                
              
              apply num_occur_app_ctx.
              exists x1, x0. split; auto. split; auto.
              
              unfold dec_census_list.
              rewrite <- combine_minus_census_list.
              rewrite gccombine_sub.
              rewrite H13.
              rewrite update_census_list_correct.
              rewrite apply_r_list_empty.
              unfold get_c. rewrite M.gempty. omega.
            + split.
              split; intros. 
              assert (H6' := H6).
              apply H11 in H6.                
              destruct H6.
              intro; apply H6.
              unfold ce' in H14.              
              apply bound_var_app_ctx in H14.
              apply bound_var_app_ctx. inv H14.
              left. rewrite (proj1 inlined_comp_ctx).
              rewrite (proj1 (rename_all_ctx_ns_comp_ctx _ _)).
              rewrite (proj1 bound_var_ctx_comp_ctx).
              left; auto. right; auto.                 
              apply H11 in H6. destruct H6.
              destruct (var_dec f v).
              * exfalso.
                apply H6; subst.
                apply bound_var_app_ctx.
                left. rewrite (proj1 inlined_comp_ctx).
                rewrite (proj1 (rename_all_ctx_ns_comp_ctx _ _)).
                rewrite (proj1 bound_var_ctx_comp_ctx).
                right.
                simpl. auto.
              *
                assert ( M.get f (M.set v (SVconstr c0 l) sub) = Some (SVfun t xs m) ).
                rewrite M.gso; auto. 
                apply H14 in H15. 
                eapply Disjoint_Included_l.
                2: apply H15.
                unfold ce'.
                do 2 (rewrite bound_var_app_ctx).
                rewrite (proj1 inlined_comp_ctx).
                rewrite (proj1 (rename_all_ctx_ns_comp_ctx _ _)).
                rewrite (proj1 bound_var_ctx_comp_ctx).
                eauto with Ensembles_DB.
              * intro.
                intros. apply Hsig in H6.
                inv H6.
                left. 
                apply num_occur_app_ctx in H13. destructAll; pi0.
                apply num_occur_app_ctx. exists 0, 0. repeat split; auto.
                repeat normalize_ctx.
                apply num_occur_ec_comp_ctx in H6.
                destructAll; pi0. auto.
                (* either y is v and it is dead OR it isn't and it is bound in c *)
                repeat normalize_ctx.
                apply bound_stem_comp_ctx_mut in H13. inv H13.
                right. auto.
                simpl in H6. inv H6.
                left.
                specialize (H10 y). rewrite gvc1 in H10.
                apply num_occur_app_ctx in H10.
                destructAll; pi0.
                apply num_occur_ec_comp_ctx in H6.
                destructAll; pi0.
                apply num_occur_app_ctx. eauto.
                inv H18.
          - (* live post *)
            inv H6.
            unfold ce'; rewrite H12.
            split; auto.
            split; auto.
            split. 
            intro. intros.
            assert (H6' := H6).
            apply H11 in H6. destruct H6.
            split; auto.
            intros.
            destruct (var_dec f v).
            + (* impossible, then v is inlined but bound *)
              exfalso.
              subst.
              apply H11 in H6'.
              destruct H6'.
              apply H15.
              rewrite (proj1 inlined_comp_ctx).
              rewrite (proj1 (rename_all_ctx_ns_comp_ctx _ _)).
              apply bound_var_app_ctx.
              left.
              apply bound_var_ctx_comp_ctx.
              right. simpl. constructor.
            + assert ( M.get f (M.set v (SVconstr c0 l) sub) = Some (SVfun t xs m)).
              rewrite M.gso; auto.
              apply H13 in H15. auto.
            +  intro. intros.
               assert (H6' := H6).
               apply Hsig in H6.
               inv H6.
               left.
               apply num_occur_app_ctx in H13. destructAll; pi0.
               repeat normalize_ctx.
               apply num_occur_ec_comp_ctx in H6. destructAll; pi0.
               simpl in H14.
               apply num_occur_app_ctx.
               exists 0, 0; split; auto.
               split; auto.
               eapply num_occur_n.
               constructor. eauto.
               inv H14; pi0. rewrite H14. auto.                 
               
               repeat normalize_ctx.
               apply bound_stem_comp_ctx_mut in H13.
               inv H13. right. auto.
               simpl in H6. inv H6.
               apply H5 in H6'.
               inv H6'. inv H13.
               specialize (H2 y). rewrite gvc in H2.
               assert (S n0 = 0).
               eapply (proj1 (num_occur_det _)); eauto.
               rewrite H8 in H14. auto. inv H13.
               exfalso.
               rewrite <- H8 in H0.
               apply ub_app_ctx_f in H0.
               destructAll.
               inv H15.
               specialize (H16 y).
               apply H16. split; auto.
               apply bound_stem_var. auto.
               simpl. constructor.
               inv H18.
        }          
        (* size *)
        eapply NPeano.Nat.lt_le_trans.
        apply constr_sub_size.
        omega.
        (* cmap_view *)
        apply cmap_view_constr; eauto.
        (* inl_inv *)
        { intro. intros. apply H4 in H9.
          destruct H9.
          split; auto.
          intros.
          destruct (var_dec f v).
          subst.
          rewrite M.gss in H11. inv H11.
          rewrite M.gso in H11; auto.
          eapply H10; eauto.
        }
        (* sig inv *)
        intro; intros.
        apply H5 in H9.
        destruct H9.
        split.
        simpl in H9.
        intro; apply H9.
        repeat normalize_ctx.
        rewrite <- app_ctx_f_fuse in H11.
        simpl in H11. auto.
        inv H10.
        left.
        repeat normalize_ctx.
        rewrite <- app_ctx_f_fuse. simpl. simpl in H11.
        auto.
        right.
        repeat normalize_ctx.
        apply bound_stem_comp_ctx_mut.
        auto.
    - (* case *)  
      simpl in H6. 
      destruct ( M.get (apply_r sig v) sub ) eqn:garvs; [destruct s|].
      +  destruct (findtag l c0) eqn:ftlc0.
         * (* folded case *)
           assert (gsr_clos
                     ce 
                     (rename_all_ctx_ns sig (inlined_ctx_f c inl)
                     |[ rename_all_ns sig e ]|)).
           {
             apply H3 in garvs.
             destructAll.
             unfold ce. repeat normalize_ctx.
             do 2 (rewrite <- app_ctx_f_fuse).
             constructor. constructor. simpl.
             apply Constr_case_s.
             apply findtag_map. auto.
           }
           assert (Hub' := gsr_preserves_clos _ _ H0 H1 H7).
           destructAll.
           apply sig_inv_combine in H5.
           destruct H5 as (H5, H5c).
           assert (Hse := gsr_preserves_sig_dom _ _ _ H0 H1 H7 H5).
           assert (H_bv : Included _ (bound_var  (rename_all_ctx_ns sig (inlined_ctx_f c inl) |[ 
                                                    rename_all_ns sig e ]|)) (bound_var ce)).
           {
             unfold ce. do 2 (rewrite bound_var_app_ctx).
             apply Included_Union_compat. auto with Ensembles_DB.
             simpl. intro. intros. eapply Bound_Ecase with (c := c0).
             apply H10.
             apply findtag_In_patterns in ftlc0.
             eapply in_map with (f := (fun p : var * exp => let (k, e0) := p in (k, rename_all_ns sig e0)))  in ftlc0.  auto.
           }
           
           eapply IHn in H6; eauto.
           destructAll.
           split.
           econstructor 3. apply H7. apply H6. split; auto.
           unfold term_sub_inl_size in *.
           simpl in *.
           assert ( term_size e < term_size (Ecase v l)).
           eapply case_size.
           apply findtag_In. eauto.
           simpl in H10. omega.
           { (* count for folded case *)
             apply c_count_fold_case; auto.
           }
           { (* inl for folded case *)
             intro. intros.
             apply H4 in H10.
             destruct H10. split.
             intro. apply H10. apply H_bv. auto.
             intros. apply H11 in H12.
             eapply Disjoint_Included_l. apply H_bv. auto.               
           }
           { (* sig inv for folded case *)
             intro. intros. split.
             apply H5 in H10. intro; apply H10.
             apply H_bv; auto.
             apply H5c in H10. inv H10; auto.
             left. apply num_occur_app_ctx in H11.
             destructAll; pi0.
             apply num_occur_app_ctx. exists 0, 0. split; auto. split; auto.
             simpl in H11.
             inv H11; pi0.
             assert (exists n, num_occur (rename_all_ns sig e) y n) by apply e_num_occur.
             destruct H12.
             assert (x0 <= 0).
             eapply num_occur_case_le. 2: apply H15.
             apply findtag_In in ftlc0.
             eapply in_map with (f := (fun p : var * exp => let (k, e0) := p in (k, rename_all_ns sig e0))) in ftlc0.
             eauto.
             auto.
             apply le_n_0_eq in H13; subst; auto.
           }             
         * (* case not found, same as fun. 
               contractcases_corresp with cl1 = nil and x = apply_r sig x*)
           remember (contractcases
                       (@pair (prod exp ctx_map) b_map
                              (@pair exp ctx_map (Ecase v l) sub) inl)
                       (fun (rm : r_map) (cm : c_map)
                            (es : prod (prod exp ctx_map) b_map)
                            (_ : lt (term_sub_inl_size es)
                                    (term_sub_inl_size
                                       (@pair (prod exp ctx_map) b_map
                                              (@pair exp ctx_map (Ecase v l) sub) inl))) =>
                          contract rm cm
                                   (@fst exp ctx_map (@fst (prod exp ctx_map) b_map es))
                                   (@snd exp ctx_map (@fst (prod exp ctx_map) b_map es))
                                   (@snd (prod exp ctx_map) b_map es)) sig count inl sub l
                       (@subcl_refl v l) (le_n (sub_inl_size sub inl))) as Hcc. 
           destruct Hcc. destruct x. destruct p.
           symmetry in HeqHcc.
           eapply contractcases_corresp with (x := apply_r sig v) (cl1 := nil) (c := c) in HeqHcc; eauto.
           Focus 2. intros.
           eapply IHn; eauto.
           unfold term_sub_inl_size in *.
           simpl in H7. simpl in *. omega.
           inv H6.
           simpl in *.
           destructAll. split; auto. 
      + (* fun *)
        remember (contractcases
                    (@pair (prod exp ctx_map) b_map
                           (@pair exp ctx_map (Ecase v l) sub) inl)
                    (fun (rm : r_map) (cm : c_map)
                         (es : prod (prod exp ctx_map) b_map)
                         (_ : lt (term_sub_inl_size es)
                                 (term_sub_inl_size
                                    (@pair (prod exp ctx_map) b_map
                                           (@pair exp ctx_map (Ecase v l) sub) inl))) =>
                       contract rm cm
                                (@fst exp ctx_map (@fst (prod exp ctx_map) b_map es))
                                (@snd exp ctx_map (@fst (prod exp ctx_map) b_map es))
                                (@snd (prod exp ctx_map) b_map es)) sig count inl sub l
                    (@subcl_refl v l) (le_n (sub_inl_size sub inl))) as Hcc. 
        destruct Hcc. destruct x. destruct p.
        symmetry in HeqHcc.
        eapply contractcases_corresp with (x := apply_r sig v) (cl1 := nil) (c := c) in HeqHcc; eauto.
        Focus 2. intros.
        eapply IHn; eauto.
        unfold term_sub_inl_size in *.
        simpl in H7. simpl in *. omega.
        inv H6.
        simpl in *.
        destructAll. split; auto. 
      + (* None *)
        remember (contractcases
                    (@pair (prod exp ctx_map) b_map
                           (@pair exp ctx_map (Ecase v l) sub) inl)
                    (fun (rm : r_map) (cm : c_map)
                         (es : prod (prod exp ctx_map) b_map)
                         (_ : lt (term_sub_inl_size es)
                                 (term_sub_inl_size
                                    (@pair (prod exp ctx_map) b_map
                                           (@pair exp ctx_map (Ecase v l) sub) inl))) =>
                       contract rm cm
                                (@fst exp ctx_map (@fst (prod exp ctx_map) b_map es))
                                (@snd exp ctx_map (@fst (prod exp ctx_map) b_map es))
                                (@snd (prod exp ctx_map) b_map es)) sig count inl sub l
                    (@subcl_refl v l) (le_n (sub_inl_size sub inl))) as Hcc. 
        destruct Hcc. destruct x. destruct p.
        symmetry in HeqHcc.
        eapply contractcases_corresp with (x := apply_r sig v) (cl1 := nil) (c := c) in HeqHcc; eauto.
        Focus 2. intros.
        eapply IHn; eauto.
        unfold term_sub_inl_size in *.
        simpl in H7. simpl in *. omega.
        inv H6.
        simpl in *.
        destructAll. split; auto.                    
    - (* proj *)
      destruct (get_c v count) eqn: gvc.
      { (* dead v pre *)
        simpl in H6.
        assert (gsr_clos ce 
                         (rename_all_ctx_ns sig (inlined_ctx_f c inl) |[ rename_all_ns sig e ]|)).
        constructor. constructor.
        simpl. apply Proj_dead_s.
        specialize (H2 v). rewrite gvc in H2.
        apply num_occur_app_ctx in H2. destructAll; pi0.
        inv H7; pi0. auto.
        assert (Hub := gsr_preserves_clos _ _ H0 H1 H7).
        destruct Hub.
        apply sig_inv_combine in H5.
        destruct H5 as (H5, H5cod).
        assert (Hse := gsr_preserves_sig_dom _ _ _ H0 H1 H7 H5).
        apply IHn with (c := c) in H6; auto.
        destructAll.
        split.
        econstructor 3. apply H7. auto.
        split. auto. split; auto.
        unfold term_sub_inl_size in *. simpl. simpl in H. omega.
        intro. specialize (H2 v1). apply num_occur_app_ctx in H2.
        destructAll. inv H10.
        eapply num_occur_n.
        apply num_occur_app_ctx. exists x, n1. split; auto.
        unfold dec_census_list.
        rewrite <- combine_minus_census_list.
        rewrite gccombine_sub.
        rewrite H11.
        rewrite update_census_list_correct.
        rewrite apply_r_list_empty.
        unfold get_c. rewrite M.gempty.
        simpl. omega.

        eapply inl_inv_mon. 2: apply H4.
        unfold ce.
        do 2 (rewrite bound_var_app_ctx).
        simpl. normalize_bound_var.
        auto with Ensembles_DB.
        
        eapply sig_inv_full_dead_l.
        rewrite <- inv_app_Eproj.
        simpl in *.
        apply sig_inv_combine. split; eauto.
      }
      simpl in H6.
      destruct (M.get (apply_r sig v0) sub) eqn:garv0s; [destruct s|].
      + (* constr *)
        destruct (nthN l n0) eqn:n0thl.
        * (* constant folding *)
          assert (Hgvs : M.get v sig = None).
          { destruct (M.get v sig) eqn:gvs.
            apply H5 in gvs.
            inv gvs.
            exfalso.
            apply H7.
            apply bound_var_app_ctx.
            right; simpl; auto.
            auto.
          }
          assert (Hbv :
                    ~ bound_var_ctx
                      (rename_all_ctx_ns sig (inlined_ctx_f c inl)) v).
          {
            unfold ce in H0. apply ub_app_ctx_f in H0.
            intro.
            destructAll.
            inv H9.
            specialize (H10 v).
            apply H10.
            split; simpl; auto.
          }
          apply H3 in garv0s.
          destructAll.
          assert (H_rn_ctx:
                    (rename_all_ctx_ns (M.set v (apply_r sig v1) sig)
                                       (inlined_ctx_f (comp_ctx_f x (Econstr_c (apply_r sig v0) c1 l x0)) inl) =
                     (rename_all_ctx_ns sig
                                        (inlined_ctx_f (comp_ctx_f x (Econstr_c (apply_r sig v0) c1 l x0)) inl)))).
          {
            apply eq_P_rename_all_ctx_ns.
            intro; intro.
            destruct (var_dec x1 v).
            - subst. exfalso.
              apply H7.
              eapply not_occur_rename_ctx_not_dom with (sig := sig).
              intro. inv H8. rewrite Hgvs in H9; inv H9.                    
              assert (~ occurs_free_ctx (rename_all_ctx_ns sig
                                                           (inlined_ctx_f
                                                              (comp_ctx_f x (Econstr_c (apply_r sig v0) c1 l x0)) inl)) v).
              intro.
              apply closed_app_ctx in H1.
              apply H1 in H8. inv H8.
              apply not_free_dead_or_bound_ctx in H8.
              inv H8; auto.
              exfalso; auto.                                        
            - rewrite M.gso; auto.
          }
          assert (Hee : rename_all_ns (M.set v (apply_r sig v1) (M.empty var)) (rename_all_ns sig e) =
                        ( rename_all_ns (M.set v (apply_r sig v1) sig) e )).
          {
            assert (Decidable (Range_map sig)) by apply Decidable_Range_map. 
            assert (sig_inv_dom sig e).
            {
              intro.
              intros.
              apply H5 in H8; destructAll.
              intro; apply H8.
              apply bound_var_app_ctx.
              right.
              simpl; normalize_bound_var.
              left.
              eapply  bound_var_rename_all_ns in H10.
              eauto.                                        
            }                                      
            inv H7. specialize (Dec v).
            inv Dec.
            + (* then v doesn't occur *)
              inv H7. apply H5 in H9. inv H9.
              inv H10.
              * (* by eq_P_rename_all_ns *)
                assert ( rename_all_ns (M.set v (apply_r sig v1) sig) e =  rename_all_ns  sig e).
                {
                  apply eq_P_rename_all_ns.
                  intro. intros. destruct (var_dec x2 v).
                  subst.
                  exfalso. apply H10.
                  apply num_occur_app_ctx in H9; destructAll; pi0.
                  simpl in H11. inv H11; pi0.
                  eapply not_occur_rename_not_dom; eauto.
                  intro. inv H12. rewrite Hgvs in H13. inv H13.  
                  rewrite M.gso; auto.
                }
                rewrite H10.
                
                assert (rename_all_ns (M.set v (apply_r sig v1) (M.empty var)) (rename_all_ns sig e)  = rename_all_ns (M.empty var) (rename_all_ns sig e)).
                {
                  unfold rename.
                  apply eq_P_rename_all_ns.
                  intro. intros. destruct (var_dec x2 v).
                  subst.
                  exfalso. apply H11. apply num_occur_app_ctx in H9.
                  destructAll; pi0.
                  simpl in H12; inv H12; pi0; auto.
                  rewrite M.gso; auto.
                }
                rewrite H11.
                rewrite <- (proj1 rename_all_ns_empty).
                reflexivity.
              * (* Impossible due to unique_bindings *)
                apply ub_app_ctx_f in H0.
                destructAll.
                inv H11. specialize (H12 v).
                exfalso.
                apply H12.
                apply bound_stem_var in H9.
                split; simpl; repeat normalize_ctx; auto.
            + (* then rename v (rename_all e) = rename_all+v e *)
              rewrite one_rename_all_ns.
              reflexivity. auto. intro. inv H9.
              unfold var in *. rewrite H10 in Hgvs. inv Hgvs.
          }
          assert (gsr_clos (rename_all_ctx_ns sig
                                              (inlined_ctx_f (comp_ctx_f x (Econstr_c (apply_r sig v0) c1 l x0))
                                                             inl) |[ rename_all_ns sig (Eproj v c0 n0 v0 e) ]|)
                           (rename_all_ctx_ns (M.set v (apply_r sig v1) sig)
                                              (inlined_ctx_f (comp_ctx_f x (Econstr_c (apply_r sig v0) c1 l x0)) inl)
                           |[ rename_all_ns (M.set v (apply_r sig v1) sig) e ]|)).
          { eapply rt_trans. 
            - simpl.
              rewrite (proj1 inlined_comp_ctx).
              simpl.
              rewrite (proj1 (rename_all_ctx_ns_comp_ctx _ _)).
              rewrite <- app_ctx_f_fuse.
              simpl. constructor.
              constructor. apply Constr_proj_s.
              unfold apply_r_list.
              apply nthN_map. eauto.
            - (* 2 parts : *)
              destruct (M.get v sig) eqn:gvs.
              inv Hgvs.
              (*) context is unchanged by extra sig *)
              
              rewrite H_rn_ctx.
              repeat normalize_ctx. simpl.
              rewrite <- app_ctx_f_fuse.
              (* ) rename v (rename_all e) = rename_all+v e by  *)
              rewrite <- Hee. apply rt_refl.
          }                
          assert (Hub' := gsr_preserves_clos _ _ H0 H1 H7).
          
          destructAll.
          eapply IHn in H6; eauto.
          assert (rename_all_ctx_ns (M.set v (apply_r sig v1) sig)
                                    (inlined_ctx_f
                                       (comp_ctx_f x (Econstr_c (apply_r sig v0) c1 l x0)) im')  =
                  (rename_all_ctx_ns sig 
                                     (inlined_ctx_f
                                        (comp_ctx_f x (Econstr_c (apply_r sig v0) c1 l x0)) im'))).
          {
            apply eq_P_rename_all_ctx_ns.
            intro; intro.
            destruct (var_dec x1 v).
            - subst.
              exfalso.
              apply H10. 
              (* num occur e v <= num_occur (rename sig e) v, ~ bound occur and not occurs free so dead (also bound_var_ctx_inlined_antimon from inl to im' *)
              assert (~ occurs_free_ctx  (rename_all_ctx_ns sig
                                                            (inlined_ctx_f
                                                               (comp_ctx_f x (Econstr_c (apply_r sig v0) c1 l x0)) inl)) v).
              apply closed_app_ctx in H1.
              intro.
              apply H1 in H11. inv H11.
              apply not_free_dead_or_bound_ctx in H11.
              inv H11.
              + apply not_occur_rename_ctx_not_dom  in H12.
                eapply dead_occur_ec_le_antimon; eauto.
                apply b_map_le_c. auto.                  
                intro. inv H11. apply H5 in H13.
                inv H13. apply H11.
                apply bound_var_app_ctx. right. simpl; auto.
              + exfalso.
                apply ub_app_ctx_f in H0.
                destructAll.
                inv H16. specialize (H17 v).
                apply H17. split; auto. simpl. constructor.
            - rewrite M.gso by auto; auto.
          }
          rewrite H10 in *.
          destruct H6 as (H6, H11).
          destruct H11 as (H11, H12).
          destruct H12 as (H12, Hsigc).
          destructAll.
          split; auto.
          eapply rt_trans.
          2: apply H6.
          apply H7.
          split; auto.
          split; auto.
          { (* returned sig_inv_codom *)
            intro. intros.
            assert (x1 <> v).
            intro; subst.
            rewrite H13 in Hgvs. inv Hgvs.
            assert (M.get x1 (M.set v (apply_r sig v1) sig) = Some y).
            rewrite M.gso; auto.
            apply Hsigc in H15. auto.
          }
          {             (* size *)
            unfold term_sub_inl_size in *.
            simpl in *; omega.
          }
          {             (* c_count for projection folding*)
            (* TODO: redo using rename_all_set_x *)
            rewrite H_rn_ctx.


            rewrite <- Hee.
            intro. assert (H2' := H2). specialize (H2 v2).
            apply num_occur_app_ctx in H2; destructAll.
            inv H10.

            assert (Hvv1 : v <> apply_r sig v1).
            {
              intro. unfold apply_r in H10.
              destruct ( @Maps.PTree.get M.elt v1 sig) eqn:gv1s. 
              subst. apply H5 in gv1s. destructAll.
              inv H12.
              specialize (H2' e0).
              rewrite gvc in H2'. assert (S n1 = 0).
              eapply (proj1 (num_occur_det _)); eauto.
              inv H12.
              apply ub_app_ctx_f in H0. destructAll.
              inv H14.
              specialize (H15 e0).
              apply H15. split.
              apply bound_stem_var. auto.
              simpl. constructor.
              subst.
              assert (~ bound_var_ctx
                        (rename_all_ctx_ns sig
                                           (inlined_ctx_f x inl)) (apply_r sig v1)).
              intro. apply Hbv. repeat normalize_ctx.
              apply bound_var_ctx_comp_ctx. left.
              unfold apply_r in H10. rewrite gv1s in H10. auto.
              unfold ce in H1. repeat normalize_ctx.
              rewrite <- app_ctx_f_fuse in H1.
              assert (occurs_free (rename_all_ctx_ns sig
                                                     (inlined_ctx_f (Econstr_c (apply_r sig v0) c1 l x0) inl)
                                  |[ rename_all_ns sig (Eproj v1 c0 n0 v0 e) ]|) (apply_r sig v1)).
              simpl. constructor.
              apply nthN_In in n0thl.
              apply apply_r_list_In. auto.               
              eapply occurs_free_ctx_not_bound in H12. 2: apply H10.
              apply H1 in H12. inv H12.
            }
            assert (Hnv := H2' v).
            assert (Hnv1 := H2' (apply_r sig v1)).
            apply num_occur_app_ctx in Hnv. destruct Hnv. destruct H10.
            destruct H10 as (Hnvc, (Hnve, Hnv_c)).
            assert (x2 = 0).
            eapply closed_not_occurs_in_context in Hbv.
            eapply (num_occur_ec_det); eauto.
            apply closed_app_ctx in H1. auto.
            subst. inv Hnve. rename H18 into Hnve.                           

            apply num_occur_app_ctx in Hnv1. destruct Hnv1. destruct H10.
            destruct H10 as (Hnv1c, (Hnv1e, Hnv1_c)).
            inv Hnv1e. rename H18 into Hnv1e.
            assert (Hrm := num_occur_rename_mut).
            specialize (Hrm _ _ Hvv1). inv Hrm. clear H12.
            specialize (H10 _ _ _ Hnve Hnv1e). destruct H10 as (Hnev_post, Hnev1_post).

            
            
            
            destruct (var_dec v2 v).             
            {               (* v2 = v *)
              subst. rewrite gdss.

              apply num_occur_app_ctx. exists 0, 0.
              split; auto.                 
            }
            

            rewrite gdso; auto.
            destruct (var_dec v2 (apply_r sig v1)).
            (* v2 = (apply_r sig v1) *)
            {
              apply num_occur_app_ctx.
              exists x2, (n3+n4). rewrite e0. split; auto. split; auto.
              rewrite gdss. rewrite Hnv1_c.
              rewrite gvc in Hnv_c.
              assert (num_occur_list [apply_r sig v0] v = 0). (* by UB *)
              simpl. destruct (cps_util.var_dec v (apply_r sig v0)); auto.
              subst. exfalso. apply ub_app_ctx_f in H0; destructAll. inv H12.
              specialize (H13 (apply_r sig v0)). apply H13. split.
              repeat normalize_ctx. apply bound_var_ctx_comp_ctx. right. simpl. constructor; auto. constructor.
              assert (num_occur_list [apply_r sig v0] (apply_r sig v1) = 0).
              simpl.  destruct (cps_util.var_dec (apply_r sig v1) (apply_r sig v0)); auto.
              subst. exfalso.
              assert (~ bound_var_ctx (rename_all_ctx_ns sig (inlined_ctx_f x inl)) (apply_r sig v0)) (* by UB *).
              intro. apply ub_app_ctx_f in H0; destructAll.
              repeat normalize_ctx. apply ub_comp_ctx_f in H0; destructAll.
              inv H16. specialize (H17 (apply_r sig v0)). apply H17. split; auto. simpl. constructor.
              unfold ce in H1.
              repeat normalize_ctx. 
              rewrite <- app_ctx_f_fuse in H1.
              assert (occurs_free (rename_all_ctx_ns sig
                                                     (inlined_ctx_f (Econstr_c (apply_r sig v0) c1 l x0) inl)
                                  |[ rename_all_ns sig (Eproj v c0 n0 v0 e) ]|) (apply_r sig v0)).
              simpl. constructor.
              rewrite <- e1.
              apply apply_r_list_In. apply nthN_In in n0thl. auto.
              eapply occurs_free_ctx_not_bound in H13.
              2: apply H12. apply H1 in H13. inv H13.
              
              unfold var in *. rewrite H10 in *. rewrite H12.
              omega.                                
            }

            (* v2 <> v <> (apply_r sig v1) *)
            rewrite gdso; auto.
            apply num_occur_app_ctx.
            exists x1, n2.  split; auto. split.
            assert (exists n,  num_occur
                                 (rename_all_ns (M.set v (apply_r sig v1) (M.empty var))
                                                (rename_all_ns sig e)) v2  n) by apply e_num_occur. destruct H10.
            assert (n2 = x3).
            eapply num_occur_sig_unaffected; eauto.
            intro. inv H12. rewrite M.gso in H13 by auto.
            rewrite M.gempty in H13. inv H13.
            intro. inv H12. destruct (var_dec x4 v).
            subst. rewrite M.gss in H13. inv H13; auto.
            rewrite M.gso in H13. rewrite M.gempty in H13. inv H13. auto.
            rewrite H12. auto.
            rewrite get_c_minus.
            simpl in H11.
            destruct (cps_util.var_dec v2 (apply_r sig v0)).
            subst. rewrite gdss. omega.
            rewrite gdso by auto. rewrite gdempty. omega.
          }
          {            (* inl_inv *)
            intro. intros.
            apply H4 in H10. unfold ce in H10.
            destruct H10.
            split.
            - intro; apply H10.
              apply bound_var_app_ctx in H12.
              inv H12.
              rewrite <- (proj1 (bound_var_ctx_rename_all_ns _ )) in H13.
              apply bound_var_app_ctx.
              left.
              rewrite <- (proj1 (bound_var_ctx_rename_all_ns _ )).
              auto.
              apply bound_var_app_ctx.
              right.
              apply bound_var_rename_all_ns.
              apply bound_var_rename_all_ns in H13.                
              auto.
            - intros. apply H11 in H12.
              eapply Disjoint_Included_l.
              2: apply H12.
              do 2 rewrite bound_var_app_ctx.
              
              do 2 (rewrite <- (proj1 (bound_var_ctx_rename_all_ns _ ))).
              do 2 (rewrite <- (bound_var_rename_all_ns)).
              normalize_bound_var.
              auto with Ensembles_DB.
          }
          {            (* sig_inv *)              
            intro. intros.
            destruct (var_dec x1 v).
            -  subst. rewrite M.gss in H10.
               inv H10.
               split.
               + intro.
                 unfold ce in H0.
                 apply ub_app_ctx_f in H0.
                 destructAll.
                 apply bound_var_app_ctx in H10.
                 inv H10.
                 apply bound_var_ctx_rename_all_ns in H13.
                 inv H12.
                 specialize (H10 v).
                 apply H10.
                 split.
                 2: simpl; auto.
                 apply bound_var_ctx_rename_all_ns.
                 auto.
                 apply bound_var_rename_all_ns in H13.
                 simpl in H11. inv H11.
                 apply H15.
                 apply bound_var_rename_all_ns. auto.
               + (* apply_r sig v1  has to be bound in x since ce is closed
   by occurs_free_app_bound_stem
                  *)
                 right.
                 repeat normalize_ctx.
                 apply bound_stem_comp_ctx_mut.
                 left.                  
                 eapply occurs_free_app_bound_stem.
                 Focus 2.
                 intro.
                 rewrite <- app_ctx_f_fuse in H9.
                 apply H9 in H10.
                 inv H10.
                 simpl.
                 constructor.
                 apply nthN_In in n0thl.
                 revert n0thl.
                 apply apply_r_list_push.
            - rewrite M.gso in H10 by auto.
              apply H5 in H10.
              destruct H10. split.
              + intro; apply H10.
                apply bound_var_app_ctx.                  
                apply bound_var_app_ctx in H12.
                inv H12.
                apply bound_var_ctx_rename_all_ns in H13.                  
                left.
                apply bound_var_ctx_rename_all_ns. auto.
                right. simpl. constructor.
                apply bound_var_rename_all_ns in H13.
                apply bound_var_rename_all_ns. auto.
              + inv H11.
                * (* y cannot be (apply_r sig v1) because the latter occurs in l *)
                  rewrite H_rn_ctx.
                  left.
                  apply num_occur_app_ctx in H12.
                  destructAll; pi0.
                  eapply num_occur_app_ctx. exists 0, 0.
                  split; auto.
                  split; auto.
                  inv H12; pi0.
                  assert (y <> apply_r sig v1).
                  {
                    intro. subst.
                    repeat normalize_ctx.
                    apply num_occur_ec_comp_ctx in H11.
                    destructAll; pi0.
                    simpl in H13. inv H13; pi0.
                    apply not_occur_list_not_in in H13.
                    apply nthN_In in n0thl.
                    apply H13.
                    apply in_map. auto.
                  }
                  simpl.
                  apply num_occur_rename_all_ns_dead_set; auto.
                *  apply bound_stem_ctx_rename_all_ns in H12.
                   right.
                   apply bound_stem_ctx_rename_all_ns. auto.
          }
        * (* same as fun and none *)
          assert (rename_all_ctx_ns sig (inlined_ctx_f c inl)
                 |[ rename_all_ns sig (Eproj v c0 n0 v0 e) ]| =
                                                              rename_all_ctx_ns sig (inlined_ctx_f (comp_ctx_f c (Eproj_c v c0 n0 v0 Hole_c)) inl)
                 |[ rename_all_ns sig e ]|) by             ctx_inl_push.
          remember (contract sig count e sub inl).
          destruct s. destruct x. destruct p.
          symmetry in Heqs.
          unfold ce in *; rewrite H7 in *.
          eapply IHn in Heqs; eauto.

          destructAll.
          destruct (get_c v c2) eqn:gvc2.
          {  (* dead v post *)
            inv H6.
            split.
            econstructor 3.
            apply H8.
            unfold ce'.
            repeat normalize_ctx.
            rewrite <- app_ctx_f_fuse.
            constructor. constructor.
            simpl. eapply Proj_dead_s.
            specialize (H9 v). rewrite gvc2 in H9.
            apply num_occur_app_ctx in H9; destructAll; pi0.
            apply num_occur_ec_comp_ctx in H6; destructAll; pi0.
            auto.
            split.

            intro. specialize (H9 v1).
            apply num_occur_app_ctx in H9.
            destructAll.
            repeat normalize_ctx.
            apply num_occur_ec_comp_ctx in H6. destructAll. simpl in H13. inv H13.
            eapply num_occur_n.
            apply num_occur_app_ctx. exists x1, x0. split; auto.
            inv H21. 
            unfold dec_census_list.
            rewrite <- combine_minus_census_list.
            rewrite gccombine_sub.
            rewrite H12.
            rewrite update_census_list_correct.
            rewrite apply_r_list_empty.
            unfold get_c. rewrite M.gempty.
            simpl. omega.

            split. eapply inl_inv_mon.
            2: apply H10. unfold ce'.
            do 2 (rewrite bound_var_app_ctx).
            repeat normalize_ctx.
            simpl. rewrite (proj1 bound_var_ctx_comp_ctx).
            eauto with Ensembles_DB.

            intro. intros. destruct (var_dec y v).
            (* y = v *)
            subst. left. specialize (H9 v). rewrite gvc2 in H9.
            apply num_occur_app_ctx in H9. destructAll; pi0.
            repeat normalize_ctx.
            apply num_occur_ec_comp_ctx in H9; destructAll; pi0.
            eapply num_occur_app_ctx. exists 0, 0; split; auto.
            (* y <> v *)
            apply H11 in H6. inv H6.
            left.
            apply num_occur_app_ctx in H12; destructAll; pi0.
            repeat normalize_ctx.
            apply num_occur_ec_comp_ctx in H6; destructAll; pi0.
            eapply num_occur_app_ctx. exists 0, 0; split; auto.
            right.
            repeat normalize_ctx.
            apply bound_stem_comp_ctx_mut in H12.
            inv H12. auto.
            exfalso. inv H6. auto. inv H18.              
          }
          inv H6.
          assert ( (rename_all_ctx_ns sig
                                      (inlined_ctx_f (comp_ctx_f c (Eproj_c v c0 n0 v0 Hole_c)) im')
                   |[ e0 ]|) = rename_all_ctx_ns sig (inlined_ctx_f c im')
                  |[ Eproj v c0 n0 (apply_r sig v0) e0 ]|) by  ctx_inl_push. 
          unfold ce';  rewrite <- H6.
          split; auto. split; auto. split; auto.
          { (* sig_inv_codom push proj *)
            intro. intros. destruct (var_dec y v).
            (* y = v *)
            subst. apply H5 in H12. inv H12.
            inv H14.
            (** by no zombie *)
            left.
            rewrite <- H6. eapply shrink_no_zombie.
            apply H8.
            rewrite H7 in H12. auto.
            (** imposible due to unique binding *)
            exfalso.
            apply ub_app_ctx_f in H0. destructAll.
            repeat normalize_ctx. apply ub_comp_ctx_f in H0.
            destructAll. inv H17.
            specialize (H18 v). apply H18.
            split. apply bound_stem_var. auto.
            simpl. constructor.

            (* y <> v *)
            apply H11 in H12. inv H12.
            rewrite H6 in H13. auto.        
            repeat normalize_ctx.              
            apply bound_stem_comp_ctx_mut in H13.
            inv H13.
            auto.
            simpl in H12. inv H12.
            exfalso. auto.
            inv H19.
          }
          unfold term_sub_inl_size in *. simpl. simpl in H. omega.
          apply cmap_view_proj; auto.
          repeat normalize_ctx.
          apply sig_inv_full_push. simpl. simpl in H5. auto.            
      + (* fun *)
        assert (rename_all_ctx_ns sig (inlined_ctx_f c inl)
               |[ rename_all_ns sig (Eproj v c0 n0 v0 e) ]| =
                                                            rename_all_ctx_ns sig (inlined_ctx_f (comp_ctx_f c (Eproj_c v c0 n0 v0 Hole_c)) inl)
               |[ rename_all_ns sig e ]|) by             ctx_inl_push.
        remember (contract sig count e sub inl).
        destruct s. destruct x. destruct p.
        symmetry in Heqs.
        unfold ce in *; rewrite H7 in *.
        eapply IHn in Heqs; eauto.

        destructAll.
        destruct (get_c v c1) eqn:gvc2.
        {  (* dead v post *)
          inv H6.
          split.
          econstructor 3.
          apply H8.
          unfold ce'.
          repeat normalize_ctx.
          rewrite <- app_ctx_f_fuse.
          constructor. constructor.
          simpl. eapply Proj_dead_s.
          specialize (H9 v). rewrite gvc2 in H9.
          apply num_occur_app_ctx in H9; destructAll; pi0.
          apply num_occur_ec_comp_ctx in H6; destructAll; pi0.
          auto.
          split.

          intro. specialize (H9 v1).
          apply num_occur_app_ctx in H9.
          destructAll.
          repeat normalize_ctx.
          apply num_occur_ec_comp_ctx in H6. destructAll. simpl in H13. inv H13.
          eapply num_occur_n.
          apply num_occur_app_ctx. exists x1, x0. split; auto.
          inv H21. 
          unfold dec_census_list.
          rewrite <- combine_minus_census_list.
          rewrite gccombine_sub.
          rewrite H12.
          rewrite update_census_list_correct.
          rewrite apply_r_list_empty.
          unfold get_c. rewrite M.gempty.
          simpl. omega.

          split. eapply inl_inv_mon.
          2: apply H10. unfold ce'.
          do 2 (rewrite bound_var_app_ctx).
          repeat normalize_ctx.
          simpl. rewrite (proj1 bound_var_ctx_comp_ctx).
          eauto with Ensembles_DB.

          intro. intros. destruct (var_dec y v).
          (* y = v *)
          subst. left. specialize (H9 v). rewrite gvc2 in H9.
          apply num_occur_app_ctx in H9. destructAll; pi0.
          repeat normalize_ctx.
          apply num_occur_ec_comp_ctx in H9; destructAll; pi0.
          eapply num_occur_app_ctx. exists 0, 0; split; auto.
          (* y <> v *)
          apply H11 in H6. inv H6.
          left.
          apply num_occur_app_ctx in H12; destructAll; pi0.
          repeat normalize_ctx.
          apply num_occur_ec_comp_ctx in H6; destructAll; pi0.
          eapply num_occur_app_ctx. exists 0, 0; split; auto.
          right.
          repeat normalize_ctx.
          apply bound_stem_comp_ctx_mut in H12.
          inv H12. auto.
          exfalso. inv H6. auto. inv H18.              
        }
        inv H6.
        assert ( (rename_all_ctx_ns sig
                                    (inlined_ctx_f (comp_ctx_f c (Eproj_c v c0 n0 v0 Hole_c)) im')
                 |[ e1 ]|) = rename_all_ctx_ns sig (inlined_ctx_f c im')
                |[ Eproj v c0 n0 (apply_r sig v0) e1 ]|) by  ctx_inl_push. 
        unfold ce';  rewrite <- H6.
        split; auto. split; auto. split; auto.
        { (* sig_inv_codom push proj *)
          intro. intros. destruct (var_dec y v).
          (* y = v *)
          subst. apply H5 in H12. inv H12.
          inv H14.
          (** by no zombie *)
          left.
          rewrite <- H6. eapply shrink_no_zombie.
          apply H8.
          rewrite H7 in H12. auto.
          (** imposible due to unique binding *)
          exfalso.
          apply ub_app_ctx_f in H0. destructAll.
          repeat normalize_ctx. apply ub_comp_ctx_f in H0.
          destructAll. inv H17.
          specialize (H18 v). apply H18.
          split. apply bound_stem_var. auto.
          simpl. constructor.

          (* y <> v *)
          apply H11 in H12. inv H12.
          rewrite H6 in H13. auto.        
          repeat normalize_ctx.              
          apply bound_stem_comp_ctx_mut in H13.
          inv H13.
          auto.
          simpl in H12. inv H12.
          exfalso. auto.
          inv H19.
        }
        unfold term_sub_inl_size in *. simpl. simpl in H. omega.
        apply cmap_view_proj; auto.
        repeat normalize_ctx.
        apply sig_inv_full_push. simpl. simpl in H5. auto.            
      + (* none *)
        assert (rename_all_ctx_ns sig (inlined_ctx_f c inl)
               |[ rename_all_ns sig (Eproj v c0 n0 v0 e) ]| =
                                                            rename_all_ctx_ns sig (inlined_ctx_f (comp_ctx_f c (Eproj_c v c0 n0 v0 Hole_c)) inl)
               |[ rename_all_ns sig e ]|) by             ctx_inl_push.
        remember (contract sig count e sub inl).
        destruct s. destruct x. destruct p.
        symmetry in Heqs.
        unfold ce in *; rewrite H7 in *.
        eapply IHn in Heqs; eauto.

        destructAll.
        destruct (get_c v c1) eqn:gvc2.
        {  (* dead v post *)
          inv H6.
          split.
          econstructor 3.
          apply H8.
          unfold ce'.
          repeat normalize_ctx.
          rewrite <- app_ctx_f_fuse.
          constructor. constructor.
          simpl. eapply Proj_dead_s.
          specialize (H9 v). rewrite gvc2 in H9.
          apply num_occur_app_ctx in H9; destructAll; pi0.
          apply num_occur_ec_comp_ctx in H6; destructAll; pi0.
          auto.
          split.

          intro. specialize (H9 v1).
          apply num_occur_app_ctx in H9.
          destructAll.
          repeat normalize_ctx.
          apply num_occur_ec_comp_ctx in H6. destructAll. simpl in H13. inv H13.
          eapply num_occur_n.
          apply num_occur_app_ctx. exists x1, x0. split; auto.
          inv H21. 
          unfold dec_census_list.
          rewrite <- combine_minus_census_list.
          rewrite gccombine_sub.
          rewrite H12.
          rewrite update_census_list_correct.
          rewrite apply_r_list_empty.
          unfold get_c. rewrite M.gempty.
          simpl. omega.

          split. eapply inl_inv_mon.
          2: apply H10. unfold ce'.
          do 2 (rewrite bound_var_app_ctx).
          repeat normalize_ctx.
          simpl. rewrite (proj1 bound_var_ctx_comp_ctx).
          eauto with Ensembles_DB.

          intro. intros. destruct (var_dec y v).
          (* y = v *)
          subst. left. specialize (H9 v). rewrite gvc2 in H9.
          apply num_occur_app_ctx in H9. destructAll; pi0.
          repeat normalize_ctx.
          apply num_occur_ec_comp_ctx in H9; destructAll; pi0.
          eapply num_occur_app_ctx. exists 0, 0; split; auto.
          (* y <> v *)
          apply H11 in H6. inv H6.
          left.
          apply num_occur_app_ctx in H12; destructAll; pi0.
          repeat normalize_ctx.
          apply num_occur_ec_comp_ctx in H6; destructAll; pi0.
          eapply num_occur_app_ctx. exists 0, 0; split; auto.
          right.
          repeat normalize_ctx.
          apply bound_stem_comp_ctx_mut in H12.
          inv H12. auto.
          exfalso. inv H6. auto. inv H18.              
        }
        inv H6.
        assert ( (rename_all_ctx_ns sig
                                    (inlined_ctx_f (comp_ctx_f c (Eproj_c v c0 n0 v0 Hole_c)) im')
                 |[ e0 ]|) = rename_all_ctx_ns sig (inlined_ctx_f c im')
                |[ Eproj v c0 n0 (apply_r sig v0) e0 ]|) by  ctx_inl_push. 
        unfold ce';  rewrite <- H6.
        split; auto. split; auto. split; auto.
        { (* sig_inv_codom push proj *)
          intro. intros. destruct (var_dec y v).
          (* y = v *)
          subst. apply H5 in H12. inv H12.
          inv H14.
          (** by no zombie *)
          left.
          rewrite <- H6. eapply shrink_no_zombie.
          apply H8.
          rewrite H7 in H12. auto.
          (** imposible due to unique binding *)
          exfalso.
          apply ub_app_ctx_f in H0. destructAll.
          repeat normalize_ctx. apply ub_comp_ctx_f in H0.
          destructAll. inv H17.
          specialize (H18 v). apply H18.
          split. apply bound_stem_var. auto.
          simpl. constructor.

          (* y <> v *)
          apply H11 in H12. inv H12.
          rewrite H6 in H13. auto.        
          repeat normalize_ctx.              
          apply bound_stem_comp_ctx_mut in H13.
          inv H13.
          auto.
          simpl in H12. inv H12.
          exfalso. auto.
          inv H19.
        }
        unfold term_sub_inl_size in *. simpl. simpl in H. omega.
        apply cmap_view_proj; auto.
        repeat normalize_ctx.
        apply sig_inv_full_push. simpl. simpl in H5. auto.            
    - (* fun *)
      remember (precontractfun sig count sub f).
      destruct p.
      destruct p.
      symmetry in Heqp.
      assert (Heqp' := Heqp).
      eapply precontractfun_corresp with (fds := Fnil) in Heqp; eauto.
      destruct Heqp as (H7, H8).
      destruct H8 as (H8, (H9, (H10, H_sig_pre))).
      assert (Hub' := gsr_preserves_clos _ _ H0 H1 H7).
      destruct Hub'.
      assert (H5' := H5).
      apply sig_inv_combine in H5.
      destruct H5 as (H5, H5co).
      assert (Hse := gsr_preserves_sig_dom _ _ _ H0 H1 H7 H5).
      simpl in *.
      assert ((rename_all_ctx_ns sig (inlined_ctx_f c inl)
              |[ rename_all_ns sig (Efun f0 e) ]|) =
              (rename_all_ctx_ns sig (inlined_ctx_f (comp_ctx_f c (Efun1_c f0 Hole_c)) inl)
              |[ rename_all_ns sig e ]|)).
      {
        ctx_inl_push.
        rewrite Disjoint_inlined_fds.
        reflexivity.
        split. intros. intro.
        destruct H13.
        inv H14. apply H9 in H16.
        destruct H16.
        apply H14.
        apply bound_var_app_ctx.
        right.
        constructor.
        apply bound_var_rename_all_ns_fundefs.
        auto.
      }
      simpl in H13.
      rewrite H13 in *.
      remember (contract sig c1 e c0 inl ).
      destruct s. destruct x.
      destruct p.
      symmetry in Heqs.
      eapply IHn in Heqs; eauto.
      destructAll.
      {
        assert (Hube0 := gsr_preserves_clos _ _ H11 H12 H14).
        destructAll.
        assert (Hse0 := gsr_preserves_sig_dom _ _ _ H11 H12 H14 Hse).
        
        (* show that e0 = rename_all_ns sig e0 *)
        assert (rename_all_ns sig e0 = e0).
        { rewrite <- (proj1 (rename_all_no_shadow _)).
          apply Disjoint_dom_rename_all.
          split. intro. intro. inv H20. inv H21.
          apply Hse0 in H20.
          apply not_bound_dead_or_free in H20.
          inv H20. apply num_occur_app_ctx in H21. destructAll; pi0.
          assert (Hne := (proj1 dead_not_free) e0).
          inv Hne. specialize (H23 x). auto.
          apply H19 in H21. inv H21.
          eapply sig_inv_dom_mon.
          2: apply Hse0.
          rewrite bound_var_app_ctx.  auto with Ensembles_DB.
        }
        (* replace f0 by fundefs_append Fnil f0 *)
        (* use postcontractfun_corresp *)
        remember ( postcontractfun
                     (@pair (prod exp ctx_map) b_map
                            (@pair exp ctx_map (Efun f0 e) sub) b0)
                     (fun (rm : r_map) (cm : c_map)
                          (es : prod (prod exp ctx_map) b_map)
                          (_ : lt (term_sub_inl_size es)
                                  (term_sub_inl_size
                                     (@pair (prod exp ctx_map) b_map
                                            (@pair exp ctx_map (Efun f0 e) sub) b0))) =>
                        contract rm cm
                                 (@fst exp ctx_map (@fst (prod exp ctx_map) b_map es))
                                 (@snd exp ctx_map (@fst (prod exp ctx_map) b_map es))
                                 (@snd (prod exp ctx_map) b_map es)) sig c2 b0 sub f0
                     (@subfds_refl e f0) (le_n (sub_inl_size sub b0))).
        destruct s. destruct x. destruct p.
        symmetry in Heqs.
        assert (Hf0n := postcontractfun_name_in_fundefs Heqs). 
        eapply postcontractfun_corresp with (c := c) (e := e0) (fds := Fnil) in Heqs; try (rewrite H20); eauto.
        Focus 2. intros.
        eapply IHn; eauto. 
        assert  (funs_size f0 + sub_inl_size sub b0 <
                 term_sub_inl_size (Efun f e, sub, inl)).
        unfold term_sub_inl_size; simpl.
        assert (sub_inl_size sub b0 <= sub_inl_size sub inl).
        apply sub_size_le. apply b_map_le_c. auto.
        symmetry in Heqp'. apply precontractfun_size in Heqp'. 
        omega. auto.          
        assert ( S n >  funs_size f0 + sub_inl_size sub b0). omega.
        eapply gt_trans_S. apply H30. auto.
        - destruct Heqs as (Heqs1, (Heqs2, (Heqs3, (Heqs4, (Heqs5, Heqs6))))).
          rewrite H20 in *. simpl in *.
          assert (Heqs_ub := gsr_preserves_clos _ _ H18 H19 Heqs1).
          destruct Heqs_ub as (Heqs_ub, Heqs_c).
          assert (Heqs_dom := gsr_preserves_sig_dom _ _ _ H18 H19 Heqs1 Hse0).
          assert (rename_all_ctx_ns sig
                                    (inlined_ctx_f (comp_ctx_f c (Efun1_c f1 Hole_c)) b2) |[ e0
                                                                                           ]| =
                                                                                              rename_all_ctx_ns sig
                                                                                                                (inlined_ctx_f c  b2) |[ Efun f1 e0
                                                                                                                                       ]|).
          repeat normalize_ctx. rewrite <- app_ctx_f_fuse. simpl.
          rewrite Heqs5. reflexivity.
          rewrite H21 in *.
          clear H20. clear Heqs5.
          destruct f1.
          + inv H6.
            split; auto.
            unfold ce'. unfold ce.
            econstructor 3.
            2: apply Heqs1.
            econstructor 3; eauto.
            split; auto.
            split; auto.
            {
              intro. intros.
              assert (H6' := H6).
              apply Heqs4 in H6.
              rewrite H21 in H6. inv H6; auto.
              repeat normalize_ctx.                
              apply bound_stem_comp_ctx_mut in H20.
              inv H20; auto.
              inv H6.
              assert (Hf2 := Decidable_name_in_fundefs f0). inv Hf2.
              specialize (Dec y). inv Dec.
              apply H_sig_pre in H6'.
              destruct H6'. inv H22.
              left. 
              eapply shrink_no_zombie.
              econstructor 3.
              apply H14. auto.
              rewrite <- H13. auto.
              (* violates unique_binding *)
              exfalso.
              rewrite <- H13 in H11.
              apply ub_app_ctx_f in H11. destructAll.
              inv H25. specialize (H26 y).
              apply H26. split.
              apply bound_stem_var. auto.
              constructor. apply bound_var_rename_all_ns_fundefs.
              apply name_in_fundefs_bound_var_fundefs. auto.
              
              exfalso.  apply H6. apply Hf0n.
              apply Included_name_in_fundefs_inlined with (im := im').
              simpl.
              apply name_in_fundefs_rename_all_ns in H24. auto.
              
              inv H24.
            }
          + (* additional RW with Fun_dead_s on Fnil *)              
            inv H6.
            split; auto.
            econstructor 3. econstructor 3.
            apply H7.
            apply H14.
            econstructor 3. apply Heqs1. 
            unfold ce'.
            constructor. constructor. constructor.
            apply Forall_nil.
            split.
            intro. specialize (Heqs2 v). apply num_occur_app_ctx in Heqs2. destructAll.
            apply num_occur_app_ctx. exists x, x0. inv H20. inv H28. split; auto.
            split; auto.  rewrite plus_0_r. auto.
            split.
            eapply inl_inv_mon. 2: apply Heqs3.
            unfold ce'. do 2 (rewrite bound_var_app_ctx).
            repeat normalize_bound_var.  auto with Ensembles_DB.
            intro. intros. apply Heqs4 in H6.
            inv H6.  rewrite H21 in H20. apply num_occur_app_ctx in H20.
            destructAll; pi0.
            inv H20; pi0. left.
            apply num_occur_app_ctx. exists 0, 0; auto.
            right.
            apply bound_stem_ctx_rename_all_ns.
            apply bound_stem_ctx_rename_all_ns in H20.
            normalize_ctx. apply bound_stem_comp_ctx_mut in H20.
            inv H20; auto.
            inv H6. inv H24. inv H24.
        - split. intro. intro. destruct H21. inv H21.
        - (* inl_inv pre post *)
          intro. intros.
          split.
          apply H16 in H21. destruct H21. apply H21.
          intros.
          assert (Hf := Decidable_name_in_fundefs f).
          inversion Hf. specialize (Dec f2).
          inversion Dec.
          destruct (get_b f2 inl) eqn:gf2i.
          + apply H4 in gf2i.
            destruct gf2i.
            apply H25 in H22.
            eapply Disjoint_Included_l.
            2: apply H22.              
            apply gsr_included_bv.
            econstructor 3.
            apply H7. auto.
          + (* this violates unique_binding *)
            exfalso. apply H3 in H22. clear H20. destructAll.
            apply ub_app_ctx_f in H0. destructAll. inv H22.
            specialize (H24 f2). apply H24. split.
            repeat normalize_ctx. apply bound_var_ctx_comp_ctx.
            right. simpl. constructor. rewrite inlined_fundefs_append.
            apply bound_var_rename_all_ns_fundefs.
            eapply fundefs_append_bound_vars. reflexivity.
            right.
            simpl. rewrite gf2i. constructor. auto.
            constructor.
            apply bound_var_rename_all_ns_fundefs.
            apply name_in_fundefs_bound_var_fundefs. auto.
          + eapply H16. apply H21.
            erewrite <- H22.
            symmetry.
            eapply precontractfun_sig_nbv.
            apply Heqp'. apply H23.
        - (* sig_inv_full pre post *)
          apply sig_inv_combine. simpl. split; auto.
      } 
      {
        assert ((forall im, sub_inl_size c0 im <= funs_size f + sub_inl_size sub im /\ funs_size f0 <= funs_size f))%nat. eapply precontractfun_size. eauto.  unfold term_sub_inl_size. simpl. unfold term_sub_inl_size in H; simpl in H. specialize (H14 inl). omega.
      }
      {         (* sig_inv for rec call *)
        apply sig_inv_combine.
        split.
        auto.
        intro. intros. apply H_sig_pre in H14. inv H14.
        destruct H16. rewrite H13 in H14. auto.
        right.
        repeat normalize_ctx.
        apply bound_stem_comp_ctx_mut.
        auto.
      }
    - (* app *)
      simpl in H6.
      destruct (get_c (apply_r sig v) count) eqn:garvc; [ | destruct n0].        
      + (* dead fun -> impossible*)
        exfalso.
        specialize (H2 (apply_r sig v)).
        rewrite garvc in H2.
        unfold ce in H2.
        apply num_occur_app_ctx in H2.
        destructAll; pi0.
        simpl in H7. inv H7.
        destruct (cps_util.var_dec (apply_r sig v) (apply_r sig v)).
        inv H13.
        apply n0; auto.
      + (* only occ *)
        destruct ( M.get (apply_r sig v) sub ) eqn:garvs; [destruct s|].
        * (* constr, ill-typed but eh *)
          inv H6.
          unfold ce in *; unfold ce' in *.
          split; auto.
          simpl. apply rt_refl.
          split; auto. split; auto.
          simpl in H5. apply sig_inv_combine in H5. destruct H5. auto.
        * (* eligible to be inlined? *)
          destruct (andb (Pos.eqb f0 f) (Nat.eqb (length l) (length l0))) eqn:Hel.
          {
            (* function inlining *)
            apply andb_true_iff in Hel.
            destruct Hel as (Hel1, Hel2).
            apply Peqb_true_eq in Hel1.
            apply beq_nat_true in Hel2. subst.
            
            assert (garvs' := garvs).
            apply H3 in garvs.
            destructAll.
            simpl in ce.
            (* sig v wasn't inlined before not dead *)
            assert (Hsvi : get_b (apply_r sig v) inl = false).
            {
              destruct (get_b (apply_r sig v) inl) eqn:gbvi.
              - (* impossible because not dead *)
                exfalso.
                apply H4 in gbvi.
                destructAll.                
                apply not_bound_dead_or_free in H7.
                inv H7.
                2: apply H1 in H9; inv H9.
                
                apply num_occur_app_ctx in H9.
                destructAll; pi0.
                inv H9.
                destruct ( cps_util.var_dec (apply_r sig v) (apply_r sig v)).
                inv H15.
                apply n0; auto.
              - auto.
            }
            assert (H_inl_nbv : forall y,   In var (Union var [set apply_r sig v] (FromList l0)) y ->  ~ bound_var_ctx (inlined_ctx_f (comp_ctx_f x (Efun1_c (fundefs_append x1 x2) x0)) inl) y).
            {
              intros. intro.
              apply ub_app_ctx_f in H0.
              destructAll.
              repeat normalize_ctx.
              apply ub_comp_ctx_f in H0.
              destructAll.
              simpl in H11.
              inv H11.
              rewrite inlined_fundefs_append in H16.
              rewrite rename_all_ns_fundefs_append in H16.                 
              eapply fundefs_append_unique_bindings_l in H16.
              2: reflexivity.
              destructAll. simpl in H13.
              rewrite Hsvi in H13.
              simpl in H13. inv H13.
              
              apply bound_var_ctx_comp_ctx in H8.
              
              inv H8.
              inv H12. specialize (H8 y).
              apply H8. split.
              apply bound_var_ctx_rename_all_ns. auto.
              apply bound_var_ctx_rename_all_ns.
              simpl. constructor.
              rewrite inlined_fundefs_append.
              eapply fundefs_append_bound_vars.
              reflexivity. right. simpl. rewrite Hsvi.
              constructor. simpl. auto. 
              simpl in H13.
              inv H13.

              rewrite inlined_fundefs_append in H19.
              eapply fundefs_append_bound_vars in H19.
              2: reflexivity.
              inv H19.
              (* in x1 *)
              inv H14.
              specialize (H13 y). apply H13.
              split; auto.
              apply bound_var_rename_all_ns_fundefs.
              auto.
              simpl. rewrite Hsvi. simpl. constructor. auto.

              (* in x2 *)
              inv H7.
              apply H23. apply bound_var_rename_all_ns_fundefs. inv H13. auto.
              inv H25. specialize (H7 y).
              apply H7. split; auto.
              apply bound_var_rename_all_ns_fundefs.
              auto.

              (* in x0 *)
              inv H17.
              specialize (H8 y).
              apply H8.
              split. apply bound_var_ctx_rename_all_ns.
              auto.
              apply bound_var_rename_all_ns_fundefs.
              rewrite inlined_fundefs_append.
              eapply fundefs_append_bound_vars.
              reflexivity.
              right. simpl; rewrite Hsvi.
              constructor.  auto.
            }
            
            assert (rename_all_ctx_ns sig
                                      (inlined_ctx_f
                                         (comp_ctx_f x
                                                     (Efun1_c
                                                        (fundefs_append x1 (Fcons (apply_r sig v) f l0 e x2)) x0))
                                         inl) |[ Eapp (apply_r sig v) f (apply_r_list sig l) ]| =
                                                                                                (rename_all_ctx_ns sig (inlined_ctx_f x inl)) |[ 
                      Efun (fundefs_append (rename_all_fun_ns sig (inlined_fundefs_f x1 inl)) (Fcons (apply_r sig v) f l0 (rename_all_ns sig e) (rename_all_fun_ns sig (inlined_fundefs_f x2 inl)))) (rename_all_ctx_ns sig (inlined_ctx_f x0 inl) |[ Eapp (apply_r sig v) f (apply_r_list sig l)  ]|)
                    ]|).
            {
              ctx_inl_push.
              rewrite inlined_fundefs_append.
              rewrite rename_all_ns_fundefs_append.
              simpl. rewrite Hsvi. auto.
            }
            assert (H_inl_ctx: (rename_all_ctx_ns (set_list (combine l0 (apply_r_list sig l)) sig)
                                                  (inlined_ctx_f (comp_ctx_f x (Efun1_c (fundefs_append x1 x2) x0))
                                                                 (M.set (apply_r sig v) true inl)) =
                                (rename_all_ctx_ns (set_list (combine l0 (apply_r_list sig l)) sig)
                                                   (inlined_ctx_f (comp_ctx_f x (Efun1_c (fundefs_append x1 (Fcons (apply_r sig v) f l0 e x2)) x0))
                                                                  (M.set (apply_r sig v) true inl))))).
            repeat normalize_ctx. simpl. do 2 (rewrite inlined_fundefs_append).
            simpl. unfold get_b. rewrite M.gss. reflexivity.


            assert (Hdjl0 : Disjoint _ (name_in_fundefs
                                          (rename_all_fun_ns sig
                                                             (inlined_fundefs_f
                                                                (fundefs_append x1 (Fcons (apply_r sig v) f l0 e x2)) inl))) (FromList l0)).
            {
              apply ub_app_ctx_f in H0; destructAll.
              repeat normalize_ctx.
              apply ub_comp_ctx_f in H0; destructAll.
              simpl in H10.
              inv H10. rewrite inlined_fundefs_append in H15.
              rewrite rename_all_ns_fundefs_append in H15.
              eapply fundefs_append_unique_bindings_l in H15.
              2: reflexivity.
              destructAll.
              split. intro. intro. inv H15.
              rewrite fundefs_append_name_in_fundefs in H17.
              2: reflexivity.
              inv H17. inv H13.
              specialize (H17 x3).
              apply H17.
              split. apply name_in_fundefs_bound_var_fundefs.
              auto.
              simpl. rewrite Hsvi. simpl. constructor. auto.
              simpl in H15. rewrite Hsvi in H15.
              simpl in H15. simpl in H12. rewrite Hsvi in H12.
              inv H12. inv H15. apply H28. inv H12; auto.
              inv H26. specialize (H15 x3).
              apply H15. split.
              apply name_in_fundefs_bound_var_fundefs. auto.
              auto.
            }
            assert (H8  := H_inl_nbv).
            
            assert (H_dead_l0 :
                      forall x3, FromList l0 x3 ->
                                 In var
                                    (dead_var_ctx
                                       (inlined_ctx_f (comp_ctx_f x (Efun1_c (fundefs_append x1 x2) x0)) inl))
                                    x3).
            {
              assert (H9 := true).

              (* show that x3 cannot be in the Dom of sig *)
              intros.
              assert (~ (Dom_map sig x3)).

              intro. inv H11. apply H5 in H12.
              destructAll.
              apply H11. apply bound_var_app_ctx. left.
              repeat normalize_ctx.
              apply bound_var_ctx_comp_ctx.
              right. simpl. constructor.
              apply bound_var_rename_all_ns_fundefs.
              rewrite inlined_fundefs_append.
              eapply fundefs_append_bound_vars.
              reflexivity.
              right.
              simpl. rewrite Hsvi.
              constructor. right. auto.
              
              (* show that it cannot be in x, x1, x2 or x0 *)                 
              repeat normalize_ctx.
              assert ( ~ bound_var_ctx
                         (comp_ctx_f (inlined_ctx_f x inl)
                                     (inlined_ctx_f (Efun1_c (fundefs_append x1 x2) x0) inl)) x3) by (apply H8; auto).
              clear H8. 
              apply num_occur_ec_comp_ctx. exists 0, 0; auto.
              split.

              (* x *)
              assert (~ bound_var_ctx (rename_all_ctx_ns sig (inlined_ctx_f x inl)) x3).
              intro; apply H12.
              apply bound_var_ctx_rename_all_ns in H8.
              apply bound_var_ctx_comp_ctx. auto.
              eapply not_occur_rename_ctx_not_dom. apply H11.
              apply closed_not_occurs_in_context; auto.
              unfold ce in H1.
              simpl in H1.
              repeat normalize_ctx.
              rewrite <- app_ctx_f_fuse in H1.                  
              apply closed_app_ctx in H1.
              auto.
              
              split; auto.
              unfold ce in H1. repeat normalize_ctx.
              rewrite <- app_ctx_f_fuse in H1.
              assert (~ occurs_free (rename_all_ctx_ns sig
                                                       (inlined_ctx_f
                                                          (Efun1_c
                                                             (fundefs_append x1 (Fcons (apply_r sig v) f l0 e x2)) x0)
                                                          inl) |[ Eapp (apply_r sig v) f (apply_r_list sig l) ]|) x3).
              eapply not_occurs_free_ctx_not_bound.
              intro. apply H1 in H8. inv H8.
              intro.
              apply H12. apply bound_var_ctx_comp_ctx.
              left.
              apply bound_var_ctx_rename_all_ns in H8. auto.
              simpl in H8.
              
              apply not_occur_free_Efun in H8. inv H8.
              rewrite inlined_fundefs_append in H13.
              rewrite rename_all_ns_fundefs_append in H13.
              apply not_occurs_free_fundefs_append in H13.
              inv H13.
              rewrite inlined_fundefs_append in H14.
              rewrite rename_all_ns_fundefs_append in H14.
              assert (H8' :
                        In var
                           (Complement var (occurs_free_fundefs
                                              (rename_all_fun_ns sig (inlined_fundefs_f x1 inl)))) x3).
              intro. apply H8. split; auto. intro. inv Hdjl0. specialize (H17 x3). apply H17; auto.
              clear H8.
              assert (H14' :
                        In var
                           (Complement var
                                       (occurs_free
                                          (rename_all_ctx_ns sig (inlined_ctx_f x0 inl)
                                          |[ Eapp (apply_r sig v) f (apply_r_list sig l) ]|))) x3).
              intro. apply H14. split; auto. intro. inv Hdjl0. specialize (H16 x3). apply H16; auto. clear H14.
              assert (H15' :
                        In var
                           (Complement var
                                       (occurs_free_fundefs
                                          (rename_all_fun_ns sig
                                                             (inlined_fundefs_f (Fcons (apply_r sig v) f l0 e x2)
                                                                                inl)))) x3).
              intro. apply H15. split; auto. intro. inv Hdjl0. specialize (H14 x3). apply H14; auto. clear H15.
              eapply Complement_Proper in H15'.
              Focus 2. simpl. rewrite Hsvi.
              simpl.  
              symmetry. apply occurs_free_fundefs_Fcons.
              assert (H15'' : In var (Complement var
                                                 (occurs_free_fundefs
                                                    (rename_all_fun_ns sig (inlined_fundefs_f x2 inl)))) x3).
              intro. apply H15'. right. split; auto.
              intro. inv Hdjl0. specialize (H14 x3). apply H14. split; auto.
              eapply fundefs_append_name_in_fundefs. reflexivity.
              right. simpl. rewrite Hsvi. simpl. constructor. auto.
              clear H15'.
              apply not_free_dead_or_bound in H14'. inv H14'.
              Focus 2. exfalso. apply H12. apply bound_var_app_ctx in H8. inv H8.
              apply bound_var_ctx_comp_ctx. right. simpl. apply identifiers.Bound_Fun12_c.
              apply bound_var_ctx_rename_all_ns in H13. auto. inv H13.
              
              apply not_free_bound_or_not_occur in H8'. inv H8'.
              Focus 2. exfalso. apply H12. apply bound_var_ctx_comp_ctx.
              right. constructor. rewrite inlined_fundefs_append.
              apply bound_var_rename_all_ns_fundefs in H13.
              eapply fundefs_append_bound_vars.
              reflexivity. left; auto.

              apply not_free_bound_or_not_occur in H15''. inv H15''.
              Focus 2. exfalso. apply H12. apply bound_var_ctx_comp_ctx.
              right. constructor. rewrite inlined_fundefs_append.
              apply bound_var_rename_all_ns_fundefs in H14.
              eapply fundefs_append_bound_vars.
              reflexivity. auto.
              simpl. apply num_occur_app_ctx in H8; destructAll; pi0.
              apply not_occur_rename_ctx_not_dom in H8; auto.

              apply not_occur_rename_fun_not_dom in H13; auto.
              apply not_occur_rename_fun_not_dom in H14; auto.

              eapply num_occur_ec_n. constructor. apply H8.
              rewrite inlined_fundefs_append.
              eapply fundefs_append_num_occur.
              reflexivity.
              apply H13. apply H14.
              auto.

            } 
            assert (H_rn_ctx: rename_all_ctx_ns (set_list (combine l0 (apply_r_list sig l)) sig)
                                                (inlined_ctx_f (comp_ctx_f x (Efun1_c (fundefs_append x1 x2) x0))
                                                               inl) =
                              (rename_all_ctx_ns sig
                                                 (inlined_ctx_f (comp_ctx_f x (Efun1_c (fundefs_append x1 x2) x0)) inl))).
            {
              apply eq_P_rename_all_ctx_ns. intro. intro.
              assert (Hl0 := Decidable_FromList l0).
              inv Hl0. specialize (Dec x3).
              inv Dec.
              - exfalso.                  
                apply H9.
                apply H_dead_l0; auto.
              - apply eq_P_set_list_not_in.
                auto.                                    
            }
            clear H8.
            
            assert (
                gsr_clos
                  (rename_all_ctx_ns sig (inlined_ctx_f x inl)
                  |[ Efun
                       (fundefs_append
                          (rename_all_fun_ns sig (inlined_fundefs_f x1 inl))
                          (Fcons (apply_r sig v) f l0 (rename_all_ns sig e)
                                 (rename_all_fun_ns sig (inlined_fundefs_f x2 inl))))
                       (rename_all_ctx_ns sig (inlined_ctx_f x0 inl)
                       |[ Eapp (apply_r sig v) f (apply_r_list sig l) ]|) ]|)
                  
                  (rename_all_ctx_ns (set_list (combine l0 (apply_r_list sig l)) sig)
                                     (inlined_ctx_f (comp_ctx_f x (Efun1_c (fundefs_append x1 (Fcons (apply_r sig v) f l0 e x2)) x0))
                                                    (M.set (apply_r sig v) true inl))
                  |[ rename_all_ns (set_list (combine l0 (apply_r_list sig l)) sig) e ]|)).
            {
              
              econstructor 3.
              constructor. constructor.
              apply Fun_inline_s.
              rewrite length_apply_r_list. auto.
              specialize (H2 (apply_r sig v)). rewrite garvc in H2.
              unfold ce in H2. rewrite H7 in H2.
              apply num_occur_app_ctx in H2. destructAll.
              (* x3 = 0 *)
              assert ( ~ bound_var_ctx (rename_all_ctx_ns sig (inlined_ctx_f x inl))
                         (apply_r sig v)).
              
              (** by UB *) intro.
              unfold ce in H0. rewrite H7 in H0.
              apply ub_app_ctx_f in H0. destructAll.
              inv H12. specialize (H13 (apply_r sig v)).
              apply H13. split. auto. constructor.
              eapply fundefs_append_bound_vars.
              reflexivity.
              right. constructor. constructor. auto.              
              apply not_bound_dead_or_free_ctx in H10.              
              inv H10. assert (x3 = 0). eapply num_occur_ec_det; eauto.

              subst. simpl in H9. rewrite H9; auto.
              (** cannot be free since closed so dead *)
              exfalso. eapply occurs_free_included_ctx in H11.
              unfold ce in H1. rewrite H7 in H1. apply H1 in H11.
              inv H11.
              
              rewrite <- H_inl_ctx. 
              (* should that (apply_r sig v) and l0 is not bound in x, x1, x2 and x0 s.t. cannot occur *)
              assert (H8 := H_inl_nbv). clear H_inl_nbv.
              rewrite inlined_ctx_f_staged.
              rewrite Disjoint_inlined_ctx with (im := (M.set (apply_r sig v) true (M.empty bool))).

              Focus 2.
              split. intro. intro. inv H9. inv H11.
              revert H10. apply H8.
              constructor. unfold get_b in H12.
              destruct (var_dec x3 (apply_r sig v)).
              subst; auto. rewrite M.gso in H12. rewrite M.gempty in H12. inv H12.
              auto.

              
              rewrite H_rn_ctx.

              rewrite (proj1 (set_list_rename_all_ns _ _)).
              repeat normalize_ctx.
              rewrite <- app_ctx_f_fuse. simpl.
              rewrite inlined_fundefs_append.
              rewrite rename_all_ns_fundefs_append.
              constructor 2.
              { (* l0 can be staged for sig *) 
                intro. intro.
                assert (Decidable (Range_map sig)) by apply Decidable_Range_map.
                inv H10. specialize (Dec x3).
                inv Dec.
                2: left; auto.
                
                inv H10. apply H5 in H11. inv H11.
                inv H12.
                - right.
                  repeat normalize_ctx.
                  apply num_occur_app_ctx in H11; destructAll; pi0.
                  apply num_occur_ec_comp_ctx in H11; destructAll; pi0.
                  simpl in H13. inv H13; pi0. rewrite inlined_fundefs_append in H19.
                  rewrite rename_all_ns_fundefs_append in H19.
                  apply fundefs_append_num_occur' in H19; destructAll; pi0.
                  simpl in H14. rewrite Hsvi in H14.
                  simpl in H14. inv H14; pi0.
                  auto.
                - exfalso. (* this violates unique_binding (can use H8 and fact that apply_r sig v <> x3 \in l0 *)
                  unfold ce in H0.
                  repeat normalize_ctx.                  
                  apply ub_app_ctx_f in H0. destructAll.
                  apply ub_comp_ctx_f in H0. destructAll.
                  
                  apply bound_stem_comp_ctx_mut in H11.
                  inv H11.

                  inv H15.
                  specialize (H11 x3).
                  apply H11.
                  split.
                  apply bound_stem_var. auto.
                  simpl. constructor.
                  apply bound_var_rename_all_ns_fundefs.
                  rewrite inlined_fundefs_append.
                  eapply fundefs_append_bound_vars.
                  reflexivity. right.
                  simpl. rewrite Hsvi. constructor. auto.

                  simpl in H16. inv H16.
                  apply name_in_fundefs_rename_all_ns in H19.
                  rewrite inlined_fundefs_append in H19.
                  eapply fundefs_append_name_in_fundefs in H19.
                  2: reflexivity.
                  inv H14. rewrite inlined_fundefs_append in H18.
                  rewrite rename_all_ns_fundefs_append in H18.
                  eapply fundefs_append_unique_bindings_l in H18.
                  2: reflexivity. destructAll.
                  inv H19.
                  (* not a name of x1 *)
                  inv H16. specialize (H19 x3).
                  apply H19. split. apply bound_var_rename_all_ns_fundefs.
                  apply name_in_fundefs_bound_var_fundefs. auto.
                  simpl. rewrite Hsvi. constructor. auto.

                  simpl in H14. rewrite Hsvi in H14. inv H14.

                  simpl in H18. rewrite Hsvi in H18. inv H18.

                  inv H14; auto.
                  inv H28. specialize (H18 x3).
                  apply H18. split; auto.                  
                  apply name_in_fundefs_bound_var_fundefs.
                  apply name_in_fundefs_rename_all_ns. auto.

                  inv H14.
                  inv H20. specialize (H11 x3). apply H11. split.
                  apply bound_stem_var. auto.
                  apply bound_var_rename_all_ns_fundefs. rewrite inlined_fundefs_append.
                  eapply fundefs_append_bound_vars.
                  reflexivity.
                  right. simpl. rewrite Hsvi. constructor. auto.
              }
              (* by sig_inv_dom *)
              split; intro. intro.
              inv H9.
              inv H11.
              apply H5 in H9.
              destruct H9. apply H9.
              apply bound_var_app_ctx. left.
              repeat normalize_ctx.
              apply bound_var_ctx_comp_ctx. right. simpl. constructor.
              apply bound_var_rename_all_ns_fundefs.
              rewrite inlined_fundefs_append.
              eapply fundefs_append_bound_vars.
              reflexivity.
              right. simpl. rewrite Hsvi. constructor. auto.
            }
            (* simplify the context for the hyp of the IH *)
            assert (H_inl_simpl:
                      (rename_all_ctx_ns (set_list (combine l0 (apply_r_list sig l)) sig)
                                         (inlined_ctx_f
                                            (comp_ctx_f x
                                                        (Efun1_c
                                                           (fundefs_append x1 (Fcons (apply_r sig v) f l0 e x2)) x0))
                                            (M.set (apply_r sig v) true inl))) =
                      (rename_all_ctx_ns sig
                                         (inlined_ctx_f
                                            (comp_ctx_f x
                                                        (Efun1_c
                                                           (fundefs_append x1 x2) x0))
                                            inl)
                      )).
            {
              rewrite <- H_inl_ctx.
              rewrite inlined_ctx_f_staged.
              rewrite Disjoint_inlined_ctx with (im := (M.set (apply_r sig v) true (M.empty bool))).
              rewrite H_rn_ctx. reflexivity.
              split. intro. intro. inv H9. inv H11.
              revert H10. apply H_inl_nbv.
              constructor. unfold get_b in H12.
              destruct (var_dec x3 (apply_r sig v)).
              subst; auto. rewrite M.gso in H12. rewrite M.gempty in H12. inv H12.
              auto.
            }
            
            
            remember (contract (set_list (combine l0 (apply_r_list sig l)) sig)
                               (update_count_inlined (apply_r_list sig l) l0
                                                     (M.set (apply_r sig v) 0 count)) e sub
                               (M.set (apply_r sig v) true inl)) as Hc.
            destruct Hc.
            destruct x3. destruct p.
            symmetry in HeqHc.
            rewrite <- H7 in H8.
            assert (Hinc := gsr_preserves_clos _ _ H0 H1 H8).
            destruct Hinc as (Hin_ub, Hin_cl).
            apply sig_inv_combine in H5.
            destruct H5 as (H5, H5co).
            assert (Hse := gsr_preserves_sig_dom _ _ _ H0 H1 H8 H5).            
            eapply IHn with (c :=  (comp_ctx_f x
                                               (Efun1_c
                                                  (fundefs_append x1 (Fcons (apply_r sig v) f l0 e x2)) x0))) in HeqHc; auto.
            inv H6.
            destructAll.
            assert (H_rn_ctx': rename_all_ctx_ns (set_list (combine l0 (apply_r_list sig l)) sig)
                                                 (inlined_ctx_f
                                                    (comp_ctx_f x
                                                                (Efun1_c
                                                                   (fundefs_append x1 (Fcons (apply_r sig v) f l0 e x2)) x0))
                                                    im') =
                               rename_all_ctx_ns  sig
                                                  (inlined_ctx_f
                                                     (comp_ctx_f x
                                                                 (Efun1_c
                                                                    (fundefs_append x1 (Fcons (apply_r sig v) f l0 e x2)) x0))
                                                     im')).
            {
              apply eq_P_rename_all_ctx_ns. intro. intro.
              assert (Hl0 := Decidable_FromList l0).
              inv Hl0. specialize (Dec x3).
              inv Dec.
              exfalso. apply H12.

              (* show that x3 cannot be in the Dom of sig *)
              assert (~ (Dom_map sig x3)).
              intro. inv H14. apply H5 in H15.
              apply H15. apply bound_var_app_ctx. left.
              repeat normalize_ctx.
              apply bound_var_ctx_comp_ctx.
              right. simpl. constructor.
              apply bound_var_rename_all_ns_fundefs.
              rewrite inlined_fundefs_append.
              eapply fundefs_append_bound_vars.
              reflexivity.
              right.
              simpl. rewrite Hsvi.
              constructor. right. auto.

              assert ( (inlined_ctx_f
                          (comp_ctx_f x
                                      (Efun1_c (fundefs_append x1 (Fcons (apply_r sig v) f l0 e x2))
                                               x0)) im') =
                       (inlined_ctx_f
                          (comp_ctx_f x
                                      (Efun1_c (fundefs_append x1 x2)
                                               x0)) im')).
              repeat normalize_ctx. simpl.
              rewrite inlined_fundefs_append. simpl.
              assert (get_b (apply_r sig v) im' = true).
              apply b_map_le_c in b. apply b.
              unfold get_b. rewrite M.gss. auto.
              rewrite H15.
              rewrite inlined_fundefs_append. auto.

              rewrite H15. clear H15.
              eapply dead_occur_ec_le_antimon.
              simpl in BP. apply b_map_le_c. apply BP.
              apply H_dead_l0; auto.
              
              apply eq_P_set_list_not_in. auto.
            }

            split; auto.
            econstructor 3. apply H8. unfold ce'. rewrite <- H_rn_ctx'. apply H6.
            split. unfold ce'. rewrite <- H_rn_ctx'. auto.
            split. unfold ce'. rewrite <- H_rn_ctx'. auto.
            { (* inl for returned app inlined case *)
              intro. intros.
              (* x3 in l0 is dead, not in l0 is same as H11 *)
              assert (Hl0 := Decidable_FromList l0).
              inv Hl0. specialize (Dec x3).
              inv Dec.
              - exfalso. (* impossible since bound in the original term *)
                apply H5 in H12.
                apply H12.
                repeat normalize_ctx.
                apply bound_var_app_ctx. left.
                apply bound_var_ctx_comp_ctx. right.
                apply bound_var_ctx_rename_all_ns.
                simpl. constructor. rewrite inlined_fundefs_append.
                eapply fundefs_append_bound_vars.
                reflexivity. right. simpl. rewrite Hsvi.
                constructor. auto.
              - rewrite H_rn_ctx' in H11.
                eapply H11.
                rewrite <- H12.              
                rewrite get_set_list2. reflexivity.
                auto.
            }
            unfold term_sub_inl_size in *; simpl in *.
            apply sub_remove_size with (im := inl) in garvs'.
            omega.
            { (* count for app inlined case*)
              rewrite H_inl_simpl.
              eapply count_inlining; eauto.
              apply sig_inv_combine; auto.
              specialize (H2 (apply_r sig v)). rewrite garvc in H2. auto.
            }
            { (* inl for app inlined case *)
              intro. intro.
              destruct (var_dec f0 (apply_r sig v)).
              - subst.
                split. intro.
                +  (* this would violate unique_bindings *)
                  rewrite H_inl_simpl in H10.
                  apply bound_var_app_ctx in H10.
                  inv H10.
                  * apply bound_var_ctx_rename_all_ns in H11.
                    revert H11.
                    apply H_inl_nbv. auto.
                  * (* violates unique binding *)
                    apply bound_var_rename_all_ns in H11.
                    apply ub_app_ctx_f in H0; destructAll.
                    repeat normalize_ctx.
                    apply ub_comp_ctx_f in H0; destructAll.
                    simpl in H13. inv H13. repeat normalize_ctx.
                    eapply fundefs_append_unique_bindings_l in H18.
                    2: reflexivity. destructAll.
                    simpl in H15. rewrite Hsvi in H15.
                    inv H15. apply H24.                    
                    apply bound_var_rename_all_ns; auto. 
                + intros. rewrite H10 in garvs'. inv garvs'.
                  split. intro. intro. inv H11.
                  apply bound_var_app_ctx in H12. inv H12.
                  * rewrite H_inl_simpl in H11.
                    apply bound_var_ctx_rename_all_ns in H11.
                    revert H11.
                    apply H_inl_nbv.
                    auto.
                  * (* violates unique binding *)
                    apply bound_var_rename_all_ns in H11.
                    apply ub_app_ctx_f in H0; destructAll.
                    repeat normalize_ctx.
                    apply ub_comp_ctx_f in H0; destructAll.
                    simpl in H15. inv H15. repeat normalize_ctx.
                    eapply fundefs_append_unique_bindings_l in H20.
                    2: reflexivity. destructAll.
                    simpl in H17. rewrite Hsvi in H17.
                    inv H17. inv H28.
                    specialize (H17 x3).
                    apply H17. split.
                    apply bound_var_rename_all_ns; auto. auto.
              - unfold get_b in H9.
                rewrite M.gso in H9 by auto.
                apply H4 in H9.
                destruct H9.
                split; intro; intros.
                + apply H9.
                  unfold ce.
                  apply bound_var_app_ctx. left.
                  apply bound_var_app_ctx in H11.
                  apply  bound_var_ctx_rename_all_ns.
                  inv H11.
                  * apply  bound_var_ctx_rename_all_ns in H12.
                    eapply bound_var_ctx_inlined_antimon.
                    apply b_map_le_true. apply H12.
                  *  apply bound_var_rename_all_ns in H12.
                     repeat normalize_ctx.
                     apply bound_var_ctx_comp_ctx.
                     right. simpl. constructor.
                     rewrite inlined_fundefs_append.
                     eapply fundefs_append_bound_vars.
                     reflexivity. right. simpl. rewrite Hsvi.
                     constructor 3. auto.
                + apply H10 in H11. eapply Disjoint_Included_l.
                  2: apply H11.
                  unfold ce.
                  do 2 (rewrite bound_var_app_ctx).
                  repeat normalize_bound_var.
                  do 2 (                  rewrite <- (proj1 (bound_var_ctx_rename_all_ns _))).
                  rewrite Union_Empty_set_neut_r.
                  apply Union_Included.
                  apply bound_var_ctx_inlined_antimon.
                  apply b_map_le_true.
                  rewrite <- bound_var_rename_all_ns. 
                  repeat normalize_ctx.
                  rewrite (proj1 bound_var_ctx_comp_ctx).
                  simpl. rewrite inlined_fundefs_append. simpl.
                  rewrite Hsvi.
                  normalize_bound_var_ctx.
                  intro. intro. right. left.
                  eapply fundefs_append_bound_vars.
                  reflexivity.
                  right. constructor 3.
                  auto.
            } 
            { (* sig for app inline  case *)
              rewrite H_inl_simpl.
              rewrite H_inl_simpl in Hse. 
              intro; intros.
              (* either x3 is in l0 or not *)
              assert (Decidable (FromList l0)) by apply Decidable_FromList.
              inv H10.
              specialize (Dec x3). inv Dec.
              - (* x3 is from l0 *)
                (* then dom ->  dead OK,  *)
                split.
                intro. apply bound_var_app_ctx in H11.
                inv H11. apply bound_var_ctx_rename_all_ns in H12. revert H12.
                apply H_inl_nbv. auto.
                (** by UB *)
                apply bound_var_rename_all_ns in H12.
                apply ub_app_ctx_f in H0. destructAll.
                repeat normalize_ctx.
                apply ub_comp_ctx_f in H0. destructAll.
                simpl in H14. inv H14. repeat normalize_ctx.

                eapply fundefs_append_unique_bindings_l in H19.
                2: reflexivity. destructAll.
                simpl in H16. rewrite Hsvi in H16. inv H16.
                inv H27. specialize (H16 x3). apply H16. split; auto.
                apply bound_var_rename_all_ns. auto.
                (* codom has to be bound on stem due to closed and occur before *)
                (* bound on stem due to occurs_free_app_bound_stem *)
                assert ( List.In y (apply_r_list sig l)).
                eapply FromList_set_list. apply H9.
                rewrite length_apply_r_list. auto. auto.
                assert (occurs_free (rename_all_ns sig (Eapp v f l)) y).
                simpl. constructor. auto.                
                assert (~ occurs_free ce y).
                intro. apply H1 in H13. inv H13.                               
                eapply  occurs_free_app_bound_stem in H12.
                inv H12. clear H15. specialize (H14 _ H13).
                right.
                repeat normalize_ctx.
                apply bound_stem_comp_ctx_mut in H14.
                apply bound_stem_comp_ctx_mut.
                inv H14; auto.
                simpl. simpl in H12. right. inv H12.
                constructor. rewrite inlined_fundefs_append.
                rewrite inlined_fundefs_append in H17.
                apply name_in_fundefs_rename_all_ns.
                apply name_in_fundefs_rename_all_ns in H17.
                eapply fundefs_append_name_in_fundefs. reflexivity.
                eapply fundefs_append_name_in_fundefs in H17. 2: reflexivity.
                inv H17; auto.
                simpl in H12. rewrite Hsvi in H12. inv H12.                
                (* apply_r sig l <> apply_r sig v because occ only once *)
                exfalso. inv H14.
                specialize (H2 (apply_r sig v)). rewrite garvc in H2.
                apply num_occur_app_ctx in H2. destructAll.
                inv H12.
                simpl in H14.
                destruct (cps_util.var_dec (apply_r sig v) (apply_r sig v)); auto.
                assert (num_occur_list (apply_r_list sig l) (apply_r sig v) = 0) by omega.
                apply not_occur_list in H12. auto.
                
                auto.
                auto.
              - (* x3 is not from l0 *)
                rewrite eq_P_set_list_not_in in H9 by auto.
                split.
                + apply Hse in H9. auto.
                + apply H5co in H9.
                  inv H9.
                  * left.
                    apply num_occur_app_ctx in H11; destructAll; pi0.
                    repeat normalize_ctx.
                    apply num_occur_ec_comp_ctx in H9; destructAll; pi0.
                    simpl in H12. inv H12; pi0.
                    repeat normalize_ctx.
                    apply fundefs_append_num_occur' in H18; destructAll; pi0.
                    simpl in H13. rewrite Hsvi in H13.
                    simpl in H13. inv H13; pi0.
                    simpl.
                    apply num_occur_app_ctx. exists 0, 0; auto.
                    split; auto.
                    apply num_occur_ec_comp_ctx. exists 0, 0; auto. split; auto. split; auto.
                    eapply num_occur_ec_n. constructor; eauto.
                    repeat normalize_ctx.
                    eapply fundefs_append_num_occur; eauto.
                    auto.
                    split; auto.
                    apply dead_occur_rename_all_ns_set_list. inv H11; pi0.
                    apply not_occur_list. auto. auto.                    
                  * destruct (var_dec y (apply_r sig v)).
                    (* then dead *)
                    left.
                    specialize (H2 (apply_r sig v)).
                    rewrite garvc in H2.
                    apply num_occur_app_ctx in H2. destructAll.
                    inv H9. simpl in H12.
                    destruct (cps_util.var_dec (apply_r sig v) (apply_r sig v)).
                    2: exfalso; auto.
                    assert (x4 = 0) by omega.
                    assert (num_occur_list (apply_r_list sig l) (apply_r sig v) = 0) by omega.
                    clear H12.
                    subst.
                    repeat normalize_ctx.
                    apply num_occur_ec_comp_ctx in H2; destructAll; pi0.
                    simpl in H9. inv H9; pi0.
                    repeat normalize_ctx.
                    apply fundefs_append_num_occur' in H18. destructAll; pi0.
                    simpl in H12. rewrite Hsvi in H12. inv H12; destructAll; pi0.
                    simpl.
                    eapply num_occur_n. apply num_occur_app_ctx.
                    exists 0, 0. split.
                    apply num_occur_ec_comp_ctx. exists 0, 0; auto.
                    split; auto. split.
                    eapply num_occur_ec_n. constructor; eauto.
                    repeat normalize_ctx.
                    eapply fundefs_append_num_occur. reflexivity.
                    eauto. eauto. auto. auto.
                    split.
                    apply dead_occur_rename_all_ns_set_list.
                    apply not_occur_list. auto. auto.
                    reflexivity. auto.

                    right.
                    apply bound_stem_ctx_rename_all_ns.
                    apply bound_stem_ctx_rename_all_ns in H11.
                    repeat normalize_ctx.
                    apply bound_stem_comp_ctx_mut in H11.
                    apply bound_stem_comp_ctx_mut.
                    inv H11; auto.
                    simpl. simpl in H9. right.  inv H9.
                    constructor. rewrite inlined_fundefs_append.
                    rewrite inlined_fundefs_append in H14.
                    eapply fundefs_append_name_in_fundefs.
                    reflexivity.
                    eapply fundefs_append_name_in_fundefs in H14.
                    2: reflexivity. inv H14; auto.
                    simpl in H9. rewrite Hsvi in H9.
                    simpl in H9. inv H9; auto.
                    exfalso. apply n0; inv H11; auto.
                    auto.                      
            }
            
            
            
          }
          (* not eligible to be inlined *)
          inv H6.
          unfold ce in *; unfold ce' in *.
          split; auto.
          simpl. apply rt_refl.
          apply sig_inv_combine in H5. destruct H5. simpl in H6.
          split; auto.
        * (* not a known function *)
          inv H6.
          unfold ce in *; unfold ce' in *.
          split; auto.
          simpl. apply rt_refl.
          apply sig_inv_combine in H5. destruct H5. simpl in H6.
          split; auto.
      + (* multiple occ *)
        inv H6.
        unfold ce in *; unfold ce' in *.
        split; auto.
        simpl. apply rt_refl.                    
        apply sig_inv_combine in H5. destruct H5. simpl in H6.
        split; auto.
    - (* prim *)
      destruct (get_c v count) eqn:gvc.
      { (* dead prim *)
        assert (gsr_clos ce
                         (rename_all_ctx_ns sig (inlined_ctx_f c inl)
                         |[ rename_all_ns sig  e ]| )).
        {
          unfold ce. constructor. constructor. simpl.
          apply Prim_dead_s.
          specialize (H2 v). rewrite gvc in H2.
          apply num_occur_app_ctx in H2.
          destructAll; pi0.
          inv H7; pi0. rewrite H8. simpl. auto.
        }
        assert (Hub' := gsr_preserves_clos _ _ H0 H1 H7).
        destruct Hub'.
        apply sig_inv_combine in H5. destruct H5. 
        assert (Hse := gsr_preserves_sig_dom _ _ _ H0 H1 H7 H5).          
        simpl in H6.  eapply IHn with (c := c) in H6.
        destructAll.
        split; auto.
        econstructor 3.
        apply H7. apply H6.
        unfold term_sub_inl_size in *.  simpl in *. omega.
        auto. auto.
        { (* count on dead prim pre *)
          intro.
          specialize (H2 v0).
          apply num_occur_app_ctx in H2.
          destructAll.
          unfold ce'.
          repeat normalize_ctx.
          simpl in H11. inv H11.             
          eapply num_occur_n.
          apply num_occur_app_ctx.
          exists x, n0.
          split; auto.
          unfold dec_census_list.
          rewrite <- combine_minus_census_list.
          rewrite gccombine_sub.
          rewrite update_census_list_correct.
          rewrite apply_r_list_empty.
          rewrite H12. unfold get_c. rewrite M.gempty.
          omega.             }
        auto.
        eapply inl_inv_mon.
        2: apply H4.
        unfold ce.
        do 2 (rewrite bound_var_app_ctx).
        simpl.
        rewrite bound_var_Eprim.
        eauto with Ensembles_DB.
        eapply sig_inv_full_dead_l.
        simpl in H5. rewrite inv_app_Eprim in H5.
        simpl in H10. rewrite inv_app_Eprim in H10.
        apply sig_inv_combine. split; eauto.
      }
      simpl in H6.
      assert ( rename_all_ctx_ns sig (inlined_ctx_f c inl)
              |[ rename_all_ns sig (Eprim v p l e) ]| =
                                                      rename_all_ctx_ns sig (inlined_ctx_f (comp_ctx_f c (Eprim_c v p l Hole_c)) inl) |[ rename_all_ns sig e ]|) by ctx_inl_push.
      remember (contract sig count e sub inl ).
      destruct s.        
      destruct x. destruct p0.
      symmetry in Heqs.
      eapply  IHn with (c := (comp_ctx_f c (Eprim_c v p l Hole_c))) in Heqs; try (rewrite <- H7; eauto).
      3: (apply cmap_view_prim; auto).
      assert ((rename_all_ctx_ns sig
                                 (inlined_ctx_f (comp_ctx_f c (Eprim_c v p l Hole_c)) b0) |[ e0
                                                                                           ]|) =
              (rename_all_ctx_ns sig
                                 (inlined_ctx_f c b0) |[ Eprim v p (apply_r_list sig l) e0 ]|)) by ctx_inl_push.
      inv H6.
      destruct Heqs as (H6, (H9, (H11, Hsig_r))).
      destruct (get_c v c0) eqn:gvc0.
      { (* dead prim post IH *)
        inv H10.
        assert (gsr_clos
                  (rename_all_ctx_ns sig
                                     (inlined_ctx_f (comp_ctx_f c (Eprim_c v p l Hole_c)) im') |[ e'  ]|) ce').
        { unfold ce'.
          repeat normalize_ctx.
          rewrite <- app_ctx_f_fuse.
          constructor. constructor. simpl.
          apply Prim_dead_s.
          specialize (H9 v). rewrite gvc0 in H9.
          apply num_occur_app_ctx in H9; destructAll; pi0.
          auto.
        }
        split.
        econstructor 3.
        rewrite <- H7 in H6. apply H6.
        apply H10.
        split.
        { (* count on dead post prim *)
          intro. specialize (H9 v0).
          apply num_occur_app_ctx in H9.
          destructAll.
          unfold ce'.
          repeat normalize_ctx.
          apply num_occur_ec_comp_ctx in H9.
          destructAll. simpl in H14. inv H14. inv H21.
          eapply num_occur_n.
          apply num_occur_app_ctx.
          exists x1, x0.
          split; auto.
          unfold dec_census_list.
          rewrite <- combine_minus_census_list.
          rewrite gccombine_sub.
          rewrite update_census_list_correct.
          rewrite apply_r_list_empty.
          rewrite H13. unfold get_c. rewrite M.gempty.
          omega.            
        }
        split.
        eapply inl_inv_mon.
        2: apply H11.
        unfold ce'.
        repeat normalize_ctx.
        do 2 (rewrite bound_var_app_ctx).
        simpl.
        rewrite (proj1 bound_var_ctx_comp_ctx).
        rewrite bound_var_Eprim_c.          
        eauto with Ensembles_DB.          
        intro. intros.
        destruct (var_dec y v).
        (* dead v *)
        left. subst. specialize (H9 v).
        rewrite gvc0 in H9.
        repeat normalize_ctx.
        apply num_occur_app_ctx in H9; destructAll; pi0.
        apply num_occur_ec_comp_ctx in H9; destructAll; pi0.
        apply num_occur_app_ctx.
        exists 0, 0.
        split; auto.
        apply Hsig_r in H12. inv H12.
        left.
        repeat normalize_ctx.
        apply num_occur_app_ctx in H13; destructAll; pi0.
        apply num_occur_ec_comp_ctx in H12; destructAll; pi0.          
        apply num_occur_app_ctx. exists 0, 0.
        split; auto.
        right.
        repeat normalize_ctx.
        apply bound_stem_comp_ctx_mut in H13. inv H13.
        auto.
        exfalso. inv H12.  apply n1; auto. inv H18.
      }
      inv H10.
      unfold ce; unfold ce'.
      rewrite H7.
      rewrite H8 in *.
      split; auto. split; auto. split; auto.
      intro. intros. assert (H10' := H10).

      apply Hsig_r in H10. inv H10.
      left. repeat normalize_ctx.
      apply num_occur_app_ctx in H12. destructAll; pi0.
      apply num_occur_ec_comp_ctx in H10. destructAll; pi0.
      simpl in H13. inv H13; pi0. rewrite H13.
      apply num_occur_app_ctx. exists 0, 0.
      split; auto. split. eapply num_occur_n.
      constructor; eauto. auto. auto.

      destruct (var_dec v y).
      apply H5 in H10'. inv H10'. inv H13.
      (* by no zombie *)
      left. eapply shrink_no_zombie. apply H6. rewrite <- H7. auto.
      (* impossible by unique binding *)
      exfalso. apply ub_app_ctx_f in H0. destructAll. inv H15. specialize (H16 y).
      apply H16. split. apply bound_stem_var.  auto. simpl. constructor.
      right. repeat normalize_ctx.
      apply bound_stem_comp_ctx_mut in H12. inv H12. auto.
      exfalso.
      simpl in H10. inv H10. apply n2; auto. inv H17.

      
      unfold term_sub_inl_size in *.
      simpl in H.
      simpl. omega.
      {
        simpl in H5.          
        rewrite inv_app_Eprim in H5.
        apply sig_inv_full_push in H5.
        rewrite (proj1 inlined_comp_ctx).
        rewrite (proj1 (rename_all_ctx_ns_comp_ctx _ _)).
        simpl; auto.
      }
    - (* halt *)
      inv H6.
      simpl in *.
      unfold ce.
      unfold ce'.
      split; auto.
      apply rt_refl.
      split; auto. split; auto.
      apply sig_inv_combine in H5. inv H5. auto.
  Qed.


  

  (* if I want to handle terms with disjoint bv and of instead of closed, used this with xs = fv (e) : *)
  Theorem sr_unwrap_halt:
    forall f t xs e  e',
      gen_sr_rw (Efun (Fcons f t xs e Fnil) (Ehalt f)) e' ->
      exists e'', e' = (Efun (Fcons f t xs e'' Fnil) (Ehalt f)) /\
                  gen_sr_rw e e''.
  Proof.
    intros. inv H. destruct c; inv H0.
    - (* Impossible due to shape*)
      simpl in *; subst. inv H1.
      + simpl in H3. inv H3. inv H1.
        destruct (cps_util.var_dec f f). omega. exfalso; auto.
      + exfalso. inv H3; pi0. inv H5; pi0. destruct B1; inv H.
        destruct B1; inv H7. auto.
      + destruct c; inv H0.
    - destruct c; inv H3.
      simpl in H. subst. inv H1.
    - destruct f0; inv H2.
      simpl. exists (e1 |[ e'0 ]|). split; auto.
      constructor; auto.
      + (* Impossible *)
        destruct f0; inv H6.
  Qed.

  Corollary gsr_unwrap_halt:
    forall f t xs e  e',
      gsr_clos (Efun (Fcons f t xs e Fnil) (Ehalt f)) e' ->
      exists e'', e' = (Efun (Fcons f t xs e'' Fnil) (Ehalt f)) /\
                  gsr_clos e e''.
  Proof.
    intros.  remember ((Efun (Fcons f t xs e Fnil) (Ehalt f))). revert Heqe0. revert e.
    induction H.
    - intros. subst. apply sr_unwrap_halt in H. destructAll.
      exists x. split; auto. constructor; auto.
    - intros. subst. exists e. split; auto. constructor 2.
    - intros. apply IHclos_refl_trans1 in Heqe0. destruct Heqe0.
      destruct H1. apply IHclos_refl_trans2 in H1. destructAll.
      exists x1. split; auto. econstructor 3; eauto.
  Qed.    
  
  (** Top-level theorem
      see sr_unwrap_halt to strengthen it to terms that are not closed *)
  Theorem shrink_corresp_top:
    forall e,
      unique_bindings e ->
      closed e ->
      gsr_clos e (shrink_top e).
  Proof.
    intros.
    unfold shrink_top.
    remember (contract (M.empty var) (init_census e) e (M.empty svalue)
                       (M.empty bool)). destruct s. destruct x. destruct p. symmetry in Heqs.
    eapply shrink_corresp with (c:= Hole_c) in Heqs; simpl; destructAll; try (rewrite <- (proj1 rename_all_ns_empty) in *) ;auto.
    apply init_census_correct.
    apply empty_view_hole.
    {
      intro.
      intro.
      unfold get_b in H1.
      rewrite M.gempty in H1. inv H1.
    }
    {
      intro. intros.
      rewrite M.gempty in H1.
      inv H1.
    }
  Qed.


End CONTRACT.
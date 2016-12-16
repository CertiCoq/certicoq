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
Require Import L6.cps_util L6.List_util L6.shrink_cps L6.eval L6.set_util L6.identifiers  L6.set_util.
Require Import L6.shrink_cps_correct.

Locate destructAll.



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


  Section CENSUS.

    Definition c_count: exp -> c_map -> Prop :=
      fun e count => forall v, num_occur e v (get_c v count).

    About num_occur.
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
        apply proper_remove.
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
        apply proper_remove.
        auto.
      - simpl.
        erewrite H.
        erewrite H0.
        reflexivity.
        auto.
        apply prop_remove_all.
        auto.
        apply prop_remove_all. auto.
      - simpl. rewrite (prop_apply_r _ _ _ H). apply proper_update_census_sig_list.
        auto.
      - simpl. rewrite (proper_update_census_sig_list H0).
        apply H; apply proper_remove; auto.
      - simpl. rewrite (prop_apply_r _ _ _ H). reflexivity.
      - simpl. erewrite H; auto.
        apply prop_remove_all. auto.
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


   
 Notation c_plus := (fun v c => get_c v c + 1)%nat.
 Notation c_minus := (fun v c => get_c v c - 1)%nat.
 
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

  
  Theorem init_census_f_ar:
    forall f,       (forall c c', map_getd_r _ 0 c c' -> forall n, f n c = f n c') -> 

    (forall m sig c,
                               map_getd_r _ 0 (update_census (M.empty var) (rename_all sig m) f c) (update_census sig m f c)) /\
  (forall m sig c,
    map_getd_r _ 0 (update_census_f (M.empty var) (rename_all_fun sig m) f c) (update_census_f sig m f c)).
  Proof.
    intros f Hf;
    eapply exp_def_mutual_ind; intros.
    -  simpl.
      assert (hfs := remove_empty var v).
      intro. rewrite <- H.
      assert (Hff := proper_update_census_sig).
      destruct Hff.
      erewrite H0 by eauto.
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
      assert (hfs := remove_empty var v).
      intro. rewrite <- H.
      assert (Hff := proper_update_census_sig).
      destruct Hff.
      erewrite H0 by eauto.
      apply proper_update_census_d.
      auto.
      rewrite apply_r_empty.
      apply smgd_refl.
    - simpl.
      intro.
      rewrite <- H0.
      assert (Hff := proper_update_census_sig).
      destruct Hff.
      erewrite H1.
      Focus 2.
      apply remove_all_empty.
      apply proper_update_census_d. auto.
      erewrite H2.
      Focus 2.
      apply remove_all_empty.
      apply H.
    - simpl. rewrite apply_r_empty.
      apply init_census_f_ar_l.
    - simpl.
      assert (hfs := remove_empty var v).
      intro. rewrite <- H.
      assert (Hff := proper_update_census_sig).
      destruct Hff.
      erewrite H0 by eauto.
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
      assert (Hff := proper_update_census_sig).
      destruct Hff.
      erewrite H1. reflexivity.
      apply remove_all_empty.      
    - simpl. apply smgd_refl.
  Qed.


    Theorem init_census_plus_ar:
    (forall m sig c,
       map_getd_r _ 0 (update_census (M.empty var) (rename_all sig m) c_plus c) (update_census sig m c_plus c)).
    Proof.
      apply init_census_f_ar.
      intros.
      rewrite H. reflexivity.
    Qed.

    
   Theorem init_census_plus_ar_f: 
  (forall m sig c,
    map_getd_r _ 0 (update_census_f (M.empty var) (rename_all_fun sig m) c_plus c) (update_census_f sig m c_plus c)).
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
  
  Theorem combine_plus_census_correct: (forall  m count sig,
                                          map_getd_r _ 0 (M.combine (f_opt_d 0 plus) count (init_census (rename_all sig m))) (update_census sig m c_plus count)) /\
                               (forall f count sig,   map_getd_r _ 0 (M.combine (f_opt_d 0 plus) count (update_census_f (M.empty var) (rename_all_fun sig f) c_plus (M.empty nat))) (update_census_f sig f c_plus count)).  
  Proof.
    eapply exp_def_mutual_ind; intros; simpl.
    - intro. rewrite gccombine'.
      rewrite <- H.
      rewrite gccombine'.
      unfold init_census.
      simpl.
      assert (Hff := proper_update_census_sig).
      destruct Hff.
      erewrite H0. Focus 2. apply remove_empty.
      rewrite <- combine_plus_census_list.
      rewrite gccombine'.
      assert (Hfr := init_census_f_ar).
      destruct (Hfr c_plus). intros.  simpl. rewrite H2. auto.
      rewrite H2.
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
      assert (Hff := proper_update_census_sig).
      destruct Hff.
      erewrite H0. Focus 2. apply remove_empty.
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
      assert (Hff := proper_update_census_sig).
      destruct Hff.
      erewrite H1. Focus 2. apply remove_all_empty.
      erewrite H2. Focus 2.
      apply remove_all_empty.
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
      assert (Hff := proper_update_census_sig).
      destruct Hff.
      erewrite H0. Focus 2. apply remove_empty.
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
      assert (Hff := proper_update_census_sig).
      destruct Hff.
      erewrite H1. Focus 2. apply remove_all_empty.
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
  
  SearchAbout apply_r_list.

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


  Theorem combine_minus_census_correct: (forall  m count sig,
                                          map_getd_r _ 0 (M.combine (f_opt_d 0 minus) count (init_census (rename_all sig m))) (update_census sig m c_minus count)) /\
                               (forall f count sig,   map_getd_r _ 0 (M.combine (f_opt_d 0 minus) count (update_census_f (M.empty var) (rename_all_fun sig f) c_plus (M.empty nat))) (update_census_f sig f c_minus count)).  
  Proof.
    eapply exp_def_mutual_ind; intros; simpl.
    - intro. rewrite gccombine_sub.
      rewrite <- H.
      rewrite gccombine_sub.
      unfold init_census.
      simpl.
      assert (Hff := proper_update_census_sig).
      destruct Hff.
      erewrite H0. Focus 2. apply remove_empty.
      rewrite <- combine_minus_census_list.
      rewrite gccombine_sub.
      assert (Hfr := init_census_f_ar).
      destruct (Hfr c_plus). intros.  simpl. rewrite H2. auto.
      rewrite H2.
      assert (Hcc := combine_plus_census_correct).
      destruct Hcc.
      rewrite <- H4.
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
      assert (Hff := proper_update_census_sig).
      destruct Hff.
      erewrite H0. Focus 2. apply remove_empty.
      rewrite init_census_plus_ar.
      assert (H' := combine_plus_census_correct).
      destruct H'.
      rewrite <- H2.
      rewrite gccombine'.
      rewrite apply_r_empty.
      rewrite get_c_up.
      rewrite gdempty.
      rewrite get_c_minus. omega.
    - intro.
      rewrite gccombine_sub.
      unfold init_census. simpl.
      assert (Hff := proper_update_census_sig).
      destruct Hff.
      erewrite H1. Focus 2. apply remove_all_empty.
      erewrite H2. Focus 2.
      apply remove_all_empty.
      rewrite init_census_plus_ar.
      rewrite <- H0.
      rewrite gccombine_sub.
      symmetry.
      assert (H' := combine_plus_census_correct).
      destruct H'.
      rewrite <- H3.
      rewrite gccombine'.
      rewrite <- H4.
      rewrite gccombine'.
      rewrite <- (proj2 rename_all_empty).
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
      assert (Hff := proper_update_census_sig).
      destruct Hff.
      erewrite H0. Focus 2. apply remove_empty.
      rewrite init_census_plus_ar.
      assert (H' := combine_plus_census_correct).
      destruct H'.
      rewrite <- H2.
      rewrite gccombine'.
      symmetry.
      rewrite <- combine_minus_census_list.
      rewrite gccombine_sub.      
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
      assert (Hff := proper_update_census_sig).
      destruct Hff.
      erewrite H3. Focus 2. apply remove_all_empty.
      symmetry. rewrite <- H. rewrite gccombine_sub. unfold init_census.
      omega.
    - intro.     
      rewrite gccombine_sub.
      rewrite gdempty.
      rewrite minus_n_O. reflexivity.
  Qed.

  
  
  
  
Theorem init_census_correct: (forall e, c_count e (init_census e)) /\
                        forall f, c_count_f f (init_census_f f). 
Proof.  
  eapply exp_def_mutual_ind; intros; intro vv;
  assert (Hucs := proper_update_census_sig);
  assert (Hcpc := combine_plus_census_correct).
        - specialize (H vv).
          unfold init_census. simpl. 
          eapply num_occur_constr.
          constructor. eauto.
          assert (Hrv := remove_empty var v).
          destructAll.
          erewrite H2; eauto.
          rewrite <- H0.
          rewrite gccombine'.
          rewrite update_census_list_correct.
          rewrite gdempty. rewrite apply_r_list_empty.
          rewrite <- (proj1 rename_all_empty).
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
          rewrite <- (proj1 rename_all_empty).
          omega.
        - unfold init_census; simpl.
          eapply num_occur_constr.
          constructor. apply H.
          destruct Hucs.
          erewrite H0.
          Focus 2.
          apply remove_empty.
          destruct Hcpc. rewrite <- H2.
          rewrite gccombine'.
          rewrite apply_r_empty.
          rewrite get_c_up. rewrite gdempty. rewrite <- (proj1 rename_all_empty).
          simpl. destruct (cps_util.var_dec vv v0). subst; rewrite gdss. auto.
          rewrite gdso by auto.
          rewrite gdempty. auto.
        - unfold init_census; simpl.
          eapply num_occur_constr.
          constructor; auto.
          destruct Hcpc.
          destruct Hucs.
          erewrite H3.
          Focus 2.
          apply remove_all_empty.
          rewrite <- H1. rewrite gccombine'.
          erewrite H4. Focus 2.
          apply remove_all_empty.
          rewrite <- (proj1 rename_all_empty).
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
          destruct Hucs.
          erewrite H0.
          Focus 2.
          apply remove_empty.
          destruct Hcpc.
          rewrite <- H2.
          rewrite gccombine'.
          rewrite update_census_list_correct.
          rewrite <- (proj1 rename_all_empty).
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
          destruct Hucs.          
          erewrite H3.
          Focus 2. apply remove_all_empty.
          rewrite <- (proj2 rename_all_empty).
          auto.
        - unfold init_census_f. simpl. rewrite gdempty. constructor.
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
    
  (* do not inline the first level of functions when going through a Efun2_c?*) 
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
  
(*  Theorem eq_b_map_inlined_ctx_mut:
   forall b1 b2,
   (forall c,
     eq_b_map_P (fun_names_ctx c) b1 b2 ->
      inlined_ctx_f c b1 = inlined_ctx_f c b2) /\
     (forall fds,
     eq_b_map_P (fun_names_fundefs_ctx fds) b1 b2 ->
      inlined_fundefs_ctx_f fds b1 = inlined_fundefs_ctx_f fds b2).
 Proof.
   Admitted.*)


  Print Dom_map.
  Definition Dom_map_b im: Ensemble var :=
    fun x => get_b x im = true.
  
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
  
  Theorem Disjoint_inlined_fds:
    forall fds im,
      Disjoint _ (bound_var_fundefs fds) (Dom_map_b im) ->
      inlined_fundefs_f fds im = fds.
  Proof.
    induction fds; intros.
    - rewrite bound_var_fundefs_Fcons in H.
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

    (* may need to also have count = 0 *)
    Definition inl_inv (im:b_map) (sub:ctx_map) (e:exp):Prop :=
      forall f, get_b f im = true ->
                ~ (bound_var e f) /\
                (forall t xs m, M.get f sub = Some (SVfun t xs m) ->
                             Disjoint _ (bound_var e) (FromList xs)).

    
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
        
    (* This is implied by sig_inv_dom in the case where e is also closed.
   Note 12/16/16: if sig_inv_dom has both ~ bv and ~ fv, then we should be able to prove corresp of contract for ub w/o closed top level 
  *) 
    Definition sig_inv sig e: Prop := 
      forall x y, M.get x sig = Some y ->
                  (* dom *) ~ (bound_var e x) /\
                            (* codom *)
                            (num_occur e y  0 \/ bound_var e y).


    
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

    Theorem same_name_in_fun: forall f,
      Same_set _ (name_in_fundefs f) (FromList (all_fun_name f)).
    Proof.
      intro.
      split; intro; intro; apply name_fds_same; auto.
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



    
    Definition sig_inv_dom_fundefs (sig:r_map) fds: Prop := 
      forall x y, M.get x sig = Some y ->
                  ~ (bound_var_fundefs fds x).


    Definition sig_inv_dead (sig:r_map) e :Prop :=
      forall x y, M.get x sig = Some y ->
                 num_occur e x 0.

    Definition sig_inv_dead_fundefs (sig:r_map) f :Prop :=
      forall x y, M.get x sig = Some y ->
                  num_occur_fds f x 0.

    
    Definition sig_inv_codom (sig:r_map) e: Prop := 
      forall x y, M.get x sig = Some y ->
                   ~ (occurs_free e y).


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
    
    Theorem remove_all_list_no_shadow:
      forall l sig,
      (forall x, (exists y, M.get x sig = Some y) -> ~ FromList l x) ->
        remove_all sig l =mg= sig.
    Proof.
      induction l; intros.
      - apply smg_refl.
      - simpl. eapply smg_trans.
        2: apply IHl.
        apply prop_remove_all.
        apply remove_none.
        destruct (M.get a sig) eqn:gas.
        exfalso.
        specialize (H a).
        destruct H.
        eauto.
        constructor.
        auto.
        auto.
        intros.
        destruct H0.
        intro.
        eapply H.
        eexists; eauto.
        constructor 2; auto.
    Qed.        
        
    Theorem remove_all_fun_name_no_shadow:
      forall f2 sig,
      sig_inv_dom_fundefs sig f2 -> 
      remove_all sig (all_fun_name f2) =mg= sig.
    Proof.
      induction f2.
      - intros. simpl.
        assert (sig_inv_dom_fundefs sig f2).
        eapply sig_inv_dom_fundefs_antimon; eauto.
        normalize_bound_var. right; auto.
        apply IHf2 in H0.
        eapply smg_trans.
        2: apply H0.        
        apply prop_remove_all.
        apply remove_none.
        destruct (M.get v sig) eqn:gvs.
        exfalso.
        apply H in gvs.
        apply gvs.
        apply bound_var_fundefs_Fcons.
        auto.
        auto.
      - intros. apply smg_refl.
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
      intro sig.
      apply exp_def_mutual_ind; intros; simpl.
      - assert (sig_inv_dom sig e).
        eapply sig_inv_dom_mon.
        2: apply H0.
        apply bound_var_subterm_e.
        constructor; constructor.
        apply H in H1.
        erewrite (proj1 prop_rename_all). rewrite H1.
        reflexivity.
        apply remove_none.
        destruct (M.get v sig) eqn:gvs.
        exfalso.
        apply H0 in gvs.
        apply gvs.
        auto.
        auto.
      - reflexivity.
      - rewrite H.
        assert ( sig_inv_dom sig (Ecase v l)).
        intro. intros.
        intro.
        apply H1 in H2.
        apply H2.
        inv H3.
        eapply Bound_Ecase; eauto.
        right. eauto.
        apply H0 in H2.
        simpl in H2. inv H2.
        reflexivity.
        intro. intros.
        intro.
        apply H1 in H2.
        apply H2.
        eapply Bound_Ecase.
        apply H3.
        constructor. auto.        
      - assert (sig_inv_dom sig e).
        eapply sig_inv_dom_mon.
        2: apply H0.
        apply bound_var_subterm_e.
        constructor; constructor.
        apply H in H1.
        erewrite (proj1 prop_rename_all). rewrite H1.
        reflexivity.
        apply remove_none.
        destruct (M.get v sig) eqn:gvs.
        exfalso.
        apply H0 in gvs.
        apply gvs.
        auto.
        auto.
      - assert (sig_inv_dom_fundefs sig f2).
        intro. intros.
        apply H1 in H2.
        intro; apply H2.
        apply bound_var_Efun.
        auto.        
        assert  (remove_all sig (all_fun_name f2) =mg= sig).
        apply remove_all_fun_name_no_shadow.
        auto.
        erewrite (proj1 prop_rename_all); eauto.
        rewrite H0.
        erewrite (proj2 prop_rename_all); eauto.
        rewrite H.
        reflexivity.
        auto.
        eapply sig_inv_dom_mon.
        2: apply H1.
        rewrite bound_var_Efun. right; auto.
      - reflexivity.
      - assert (sig_inv_dom sig e).
        eapply sig_inv_dom_mon.
        2: apply H0.
        apply bound_var_subterm_e.
        constructor; constructor.
        apply H in H1.
        erewrite (proj1 prop_rename_all). rewrite H1.
        reflexivity.
        apply remove_none.
        destruct (M.get v sig) eqn:gvs.
        exfalso.
        apply H0 in gvs.
        apply gvs.
        auto.
        auto.
      - reflexivity.
      - erewrite (proj1 prop_rename_all).
        rewrite H.
        rewrite H0.
        reflexivity.
        eapply sig_inv_dom_fundefs_antimon; eauto.
        rewrite bound_var_fundefs_Fcons.
        right; auto.
        intro. intros.
        apply H1 in H2.
        intro; apply H2.
        apply bound_var_fundefs_Fcons.
        auto.
        apply remove_all_list_no_shadow.
        intros.
        destruct H2.
        apply H1 in H2.
        intro; apply H2.
        apply bound_var_fundefs_Fcons.
        auto.
      - reflexivity.
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

             Theorem bound_var_rename_all_ns:
               forall sigma, 
                 (forall (e : exp),
                    bound_var e <--> bound_var (rename_all_ns sigma e)) /\
                 (forall (fds : fundefs),
                    bound_var_fundefs fds <--> bound_var_fundefs (rename_all_fun_ns sigma fds)).
             Proof.
               intro sig.
               apply exp_def_mutual_ind; intros; simpl; repeat (normalize_bound_var); split; try (rewrite H); try (rewrite H0); auto with Ensembles_DB.
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

       Print name_in_fundefs.
(* Section move_to_identifiers. *)
       Fixpoint name_in_ctx_fundefs B:=
         match B with
           | Fcons1_c f' _ _ _ B0 => Union var [set f'] (name_in_fundefs B0)
           | Fcons2_c f' _ _ _ B0 => Union var [set f'] (name_in_ctx_fundefs B0)
         end.

       Theorem name_in_ctx_fundefs_ctx:
         forall e cf, 
           Same_set _ (name_in_ctx_fundefs cf) (name_in_fundefs (cf <[ e ]>)).
       Proof.
         induction cf.
         simpl. eauto with Ensembles_DB.
         simpl. rewrite IHcf.
         eauto with Ensembles_DB.
       Qed.         
         
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
             ~ (name_in_ctx_fundefs defs y) -> 
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
                  ~ (name_in_ctx_fundefs defs x) ->
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
                         (Setminus _ (occurs_free e) (name_in_ctx_fundefs B))).
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
                                                     (name_in_ctx_fundefs B))))
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

    Ltac normalize_bound_var_ctx' :=
      match goal with
        | [ |- context[bound_var_ctx Hole_c]] =>
          rewrite bound_var_Hole_c 
        | [|- context[bound_var_ctx (Econstr_c _ _ _ _)]] =>
          rewrite bound_var_Econstr_c
        | [|- context[bound_var_ctx (Eproj_c _ _ _ _ _)]] =>
          rewrite bound_var_Eproj_c
        | [|- context[bound_var_ctx (Ecase_c _ _ _ _ _)]] =>
          rewrite bound_var_Case_c
        | [ |- context[bound_var_ctx (Efun1_c _ _)]] =>
          rewrite bound_var_Fun1_c 
        | [ |- context[bound_var_ctx (Efun2_c _ _)] ] =>
          rewrite bound_var_Fun2_c
        | [|- context[bound_var_ctx (Eprim_c _ _ _ _)]] =>
          rewrite bound_var_Eprim_c
        | [|- context[bound_var_fundefs_ctx (Fcons1_c _ _ _ _ _)]] =>
          rewrite bound_var_Fcons1_c
        | [|- context[bound_var_fundefs_ctx (Fcons2_c _ _ _ _ _)]] =>
          rewrite bound_var_Fcons2_c
      end.

Ltac normalize_bound_var_ctx_in_ctx' :=
  match goal with
    | [ H: context[bound_var_ctx Hole_c] |- _] =>
      rewrite bound_var_Hole_c in H
    | [ H : context[bound_var_ctx (Econstr_c _ _ _ _)] |- _ ] =>
      rewrite bound_var_Econstr_c in H
    | [ H : context[bound_var_ctx (Eproj_c _ _ _ _ _)]  |- _ ] =>
      rewrite bound_var_Eproj_c in H
    | [H: context[bound_var_ctx (Ecase_c _ _ _ _ _)] |- _] =>
      rewrite bound_var_Case_c in H
    | [ H : context[bound_var_ctx (Efun1_c _ _)] |- _ ] =>
      rewrite bound_var_Fun1_c in H
    | [ H : context[bound_var_ctx (Efun2_c _ _)] |- _ ] =>
      rewrite bound_var_Fun2_c in H
    | [ H : context[bound_var_ctx (Eprim_c _ _ _ _)] |- _ ] =>
      rewrite bound_var_Eprim_c in H
    | [H:context[bound_var_fundefs_ctx (Fcons1_c _ _ _ _ _)] |- _] =>
      rewrite bound_var_Fcons1_c in H
    | [H: context[bound_var_fundefs_ctx (Fcons2_c _ _ _ _ _)] |- _] =>
      rewrite bound_var_Fcons2_c in H
  end.


    Theorem bound_var_ctx_comp_ctx:      
      (forall c1 c2,
      Same_set _ (bound_var_ctx (comp_ctx_f c1 c2))
               (Union _ (bound_var_ctx c1) (bound_var_ctx c2)))/\
      (forall fc1 c2,
         Same_set _ (bound_var_fundefs_ctx (comp_f_ctx_f fc1 c2))
               (Union _ (bound_var_fundefs_ctx fc1) (bound_var_ctx c2)))
       .
       Proof.
         exp_fundefs_ctx_induction IHc1 IHfc1; simpl; split; repeat (normalize_bound_var_ctx'); try (rewrite IHc1); try (rewrite IHfc1); repeat (normalize_bound_var_ctx'); repeat (normalize_bound_var); eauto 25 with Ensembles_DB.
       Qed.

       Ltac  normalize_bound_var_ctx :=
         first [
                match goal with
                  | [|- context[bound_var_ctx (comp_ctx_f _ _)]] =>
                    rewrite (proj1 (bound_var_ctx_comp_ctx))
                  | [|- context [bound_var_fundefs_ctx (comp_f_ctx_f _ _)]] =>
                    rewrite (proj1 (bound_var_ctx_comp_ctx))
                end | normalize_bound_var_ctx'].

       Ltac  normalize_bound_var_ctx_in_ctx :=
         first [
                match goal with
                  | [H:context[bound_var_ctx (comp_ctx_f _ _)] |- _] =>
                    rewrite (proj2 (bound_var_ctx_comp_ctx)) in H
                  | [H:context [bound_var_fundefs_ctx (comp_f_ctx_f _ _)] |- _] =>
                    rewrite (proj2 (bound_var_ctx_comp_ctx)) in H
                end| normalize_bound_var_ctx_in_ctx'].

       
       Definition closed_ctx :=
          fun c => Empty_set var <--> occurs_free_ctx c.
         
       Definition closed_fundefs_ctx :=
         fun cf => Empty_set var <--> occurs_free_fundefs_ctx cf.

       Definition closed_fundefs :=
         fun f => Empty_set var <--> occurs_free_fundefs f.

       Theorem Decidable_name_in_ctx_fundefs :
         forall cf, Decidable (name_in_ctx_fundefs cf).
       Proof.
         induction cf; simpl.
         apply Decidable_Union.
         apply Decidable_singleton_var.
         apply Decidable_name_in_fundefs.
         apply Decidable_Union.
         apply Decidable_singleton_var.
         auto.
       Qed.         

       Theorem fun_names_not_free_in_fundefs_ctx :
         forall x f7,
         name_in_ctx_fundefs f7 x
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
           assert (Hf5 := Decidable_name_in_ctx_fundefs f5).
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
           assert (Hf6 := Decidable_name_in_ctx_fundefs f7).
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
         rewrite <- name_in_ctx_fundefs_ctx.
         eauto with Ensembles_DB.
         rewrite <- name_in_ctx_fundefs_ctx.
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

       About Decidable_name_in_ctx_fundefs.

       
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
       
       Theorem name_in_bound_var_fundefs_ctx: forall cf,
         Included _ (name_in_ctx_fundefs cf) (bound_var_fundefs_ctx cf).
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
  - assert (Hf5 := Decidable_name_in_ctx_fundefs f5).
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
    assert (Hf7 := Decidable_name_in_ctx_fundefs f7).
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


    (* if closed at top level, then any subterm is Disjoint OF BV *)
 (* not used 
    Theorem closed_app_fun_not_occurs:
      forall c fds y e',
      bound_var_fundefs fds y ->
      ~ name_in_fundefs fds y ->
      closed (c |[ Efun fds e' ]|) ->
      unique_bindings (c |[ Efun fds e' ]|) ->
      num_occur (c |[ e' ]|) y 0.
    Proof.
      intros.
      assert (~ bound_var_ctx c y).
      apply ub_app_ctx_f in H2.
      destructAll.
      intro.
      inv H4.
      specialize (H6 y).
      apply H6. split; auto.
      assert (num_occur_ec c y 0).
      apply closed_app_ctx in H1.
      assert (~ occurs_free_ctx c y).
      intro.
      apply H1 in H4.
      inv H4.
      apply not_free_dead_or_bound_ctx in H4.
      inv H4; auto.
      exfalso; auto.
      assert (~ bound_var e' y).
      intro.
      apply ub_app_ctx_f in H2.
      destructAll.
      inv H6.
      inv H12. specialize (H6 y); apply H6; auto.
      assert (num_occur e' y 0).
      {
        apply not_bound_dead_or_free in H5.
        inv H5; auto.
        exfalso.
        admit.
      }
      apply num_occur_app_ctx; eauto.
    Admitted.      
*)
    
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
          apply bound_var_rename_all_exp in H1.
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
          apply bound_var_rename_all in H4.
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


    (* todo: replace shrink_cps_correct's def with that *)
 Definition eq_env_P {A}:  Ensemble var -> M.t A -> M.t A -> Prop :=
    fun S rho1 rho2 =>
      forall x, S x -> M.get x rho1 = M.get x rho2.


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
        
    (* todo: move to ctx *)


      
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

    Print comp_f_ctx_f.
    
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
               assert (Hcc := bound_var_rename_all_ns).
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
       
       

       

    Theorem precontractfun_corresp:
      forall fds_c fds e c im sub count sig,
      let ce := (app_ctx_f (rename_all_ctx_ns sig (inlined_ctx_f c im)) (rename_all_ns sig (Efun (fundefs_append fds fds_c) e))) in
      unique_bindings ce ->
      closed ce ->
      c_count ce count ->
      cmap_view_ctx sub c ->
      inl_inv im sub ce ->
      sig_inv_dom sig ce ->
      forall fds_c' count' sub',
      precontractfun sig count sub fds_c = (fds_c', count', sub') ->
      let ce' := (app_ctx_f (rename_all_ctx_ns sig (inlined_ctx_f c im)) (rename_all_ns sig (Efun (fundefs_append fds fds_c') e))) in
      gsr_clos ce ce' /\ c_count ce' count' /\ inl_inv im sub' ce' /\
      cmap_view_ctx sub' (comp_ctx_f c (Efun1_c fds_c' Hole_c)).
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
           assert (Hse := gsr_preserves_sig_dom _ _ _ H H0 H6 H4).           
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
             simpl in H9. inv H9.
             rewrite rename_all_ns_fundefs_append in H16.
             apply fundefs_append_num_occur' in H16.
             destructAll.
             simpl in H11.
             inv H11.
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
             specialize (H11 e count sig). rewrite <- H11.
             rewrite gccombine_sub.
             rewrite H10.
             assert (c_count (rename_all sig e) (init_census (rename_all sig e))).
             apply init_census_correct.
             rewrite (proj1 (rename_all_no_shadow _)) in H14 at 1.
             specialize (H14 v0).
             assert (n0 =  get_c v0 (init_census (rename_all sig e))).
             eapply (proj1 (num_occur_det v0)); eauto.             
             omega.
             intro.
             intros.
             apply H4 in H15.
             unfold ce in H15.
             intro; apply H15.
             apply bound_var_app_ctx.
             right.
             apply bound_var_rename_all_ns.
             normalize_bound_var.
             left.
             rewrite fundefs_append_bound_vars.
             2: reflexivity.
             normalize_bound_var.
             auto.
           }
           {
             intro.
             intros.
             apply H3 in H9.
             destruct H9.
             split; [| split].
             - intro.
               apply H9.
               unfold ce.
               apply bound_var_app_ctx in H11.
               apply bound_var_app_ctx.
               inv H11; auto.
               right.
               apply bound_var_rename_all_ns.
               apply bound_var_rename_all_ns in H12.
               normalize_bound_var.
               rewrite bound_var_Efun in H12.
               inv H12; auto.
               left.
               rewrite fundefs_append_bound_vars.
               2: reflexivity.
               rewrite fundefs_append_bound_vars in H11.
               2: reflexivity.
               rewrite bound_var_fundefs_Fcons.
               inv H11; auto.
             - apply H10 in H11.
               unfold ce in H11.
               intro. intro.
               inv H11.
               specialize (H13 x).
               apply H13.
               inv H12. split; auto.
               rewrite bound_var_app_ctx in H11.
               rewrite bound_var_app_ctx.
               inv H11; auto.
               right.
               apply bound_var_rename_all_ns.
               apply bound_var_rename_all_ns in H12.
               normalize_bound_var.
               rewrite bound_var_Efun in H12.
               inv H12; auto.
               left.
               rewrite fundefs_append_bound_vars.
               2: reflexivity.
               rewrite fundefs_append_bound_vars in H11.
               2: reflexivity.
               rewrite bound_var_fundefs_Fcons.
               inv H11; auto.               
           }
          
        +           assert (rename_all_ctx_ns sig (inlined_ctx_f c im)
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
                      rewrite <- (proj1 (bound_var_rename_all_ns _)).
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
                    * rewrite M.gso in H12.
                      apply H11 in H12.
                      auto. auto.
                    * apply cmap_view_efun1_cons. apply H10.
                      
                      (* due to unique binding *)

                      apply (gsr_preserves_clos _ _ H H0) in H7.
                      destruct H7.
                      destruct (M.get v c0) eqn:gvc0.
                      2: auto.

                      assert (bound_var_ctx (comp_ctx_f c (Efun1_c f0 Hole_c)) v).
                      eapply cmap_view_bound_in_ctx; eauto.                      

                      apply bound_var_ctx_comp_ctx in H12.
                      apply ub_app_ctx_f in H7.
                      destructAll.
                      exfalso.
                      inv H12.
                      {
                        inv H14.
                        specialize (H12 v).
                        apply H12.
                        split.
                        apply bound_var_ctx_rename_all_ns.
                        {
                          destruct s.
                          - apply H10 in gvc0. destructAll.
                            apply comp_ctx_split in H14.
                            destruct H14.
                            + destructAll.
                              destruct x1; inv H14.
                              rewrite (proj1 inlined_comp_ctx).
                              simpl.                            
                              apply bound_var_ctx_comp_ctx.
                              right; auto.
                            + destructAll. destruct x2; inv H17. destruct x2; inv H18.
                          - assert (gvc0' := gvc0).
                            apply H10 in gvc0. destructAll.
                            apply comp_ctx_split in H14.
                            destruct H14.
                            + destructAll.
                              destruct x3; inv H14.
                              * simpl in H13.
                                inv H13.
                                repeat rewrite rename_all_ns_fundefs_append in H18.
                                eapply fundefs_append_unique_bindings_l in H18.
                                2: reflexivity.
                                destructAll.
                                inv H16.
                                exfalso. specialize (H18 v).
                                apply H18.                                
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
                                apply H14.
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
                              destruct x4; inv H17.
                              * exfalso.
                                simpl in H13.
                                inv H13.
                                repeat rewrite rename_all_ns_fundefs_append in H18.
                                eapply fundefs_append_unique_bindings_l in H18.
                                2: reflexivity.
                                destructAll.
                                inv H16.
                                exfalso. specialize (H18 v).
                                apply H18.                                
                                split.
                                eapply fundefs_append_bound_vars.
                                reflexivity. right.
                                simpl. auto.
                                eapply fundefs_append_bound_vars.
                                reflexivity. right.
                                simpl. auto.                              
                              * destruct x4; inv H18.
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
                        simpl in H13. inv H13.
                        rewrite rename_all_ns_fundefs_append in H18.
                        rewrite rename_all_ns_fundefs_append in H18.
                        eapply fundefs_append_unique_bindings_l in H18.
                        2: reflexivity.
                        destructAll.
                        inv H16. specialize (H18 v).
                        apply H18.
                        split.
                        eapply fundefs_append_bound_vars.
                        reflexivity.
                        right. simpl. auto.
                        apply bound_var_rename_all_ns.
                        inv H15. 
                        auto.
                        inv H22.
                      }
      - simpl in H5. inv H5.
        split.
        apply rt_refl.
        split; auto.
        split; auto.
        apply cmap_view_efun1_nil. auto.
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

   
                   (* will need to prove at the same time postcontractfun and contractcase *)
    Theorem shrink_corresp:
      forall e sub im sig c count,
      let ce := (app_ctx_f (rename_all_ctx_ns sig (inlined_ctx_f c im)) (rename_all_ns sig e)) in
      unique_bindings ce ->
      closed ce ->
      c_count ce count ->
      cmap_view_ctx sub c ->
      inl_inv im sub ce ->
      sig_inv_dom sig ce ->
      forall e' count' im' BP,
        contract sig count e sub im = existT _ (e', count', im') BP ->
        let ce' := (app_ctx_f (rename_all_ctx_ns sig (inlined_ctx_f c im')) e') in
      gsr_clos ce ce' /\ c_count ce' count' /\ inl_inv im' sub ce'.
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
            destruct Heqs. destruct H10.
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
              + split; intros.
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
            - (* live post *)
              inv H6.
              unfold ce'; rewrite H12.
              split; auto.
              split; auto.
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
      - (* case *)
        simpl in H6. 
        destruct ( M.get (apply_r sig v) sub ) eqn:garvs; [destruct s|].
        +  destruct (findtag l c0) eqn:ftlc0.
           * (* folded case *)
             
             admit.
           * (* case not found, same as fun *)
             admit.
        + (* fun *)
          admit.
        + (* None *)
          admit.
      - (* proj *)
        simpl in H6.
        destruct (M.get (apply_r sig v0) sub) eqn:garv0s; [destruct s|].
        + (* constr *)
          destruct (nthN l n0) eqn:n0thl.
          * (* constant folding *)
            assert (Hgvs : M.get v sig = None).
            { destruct (M.get v sig) eqn:gvs.
              apply H5 in gvs. exfalso.
              apply gvs.
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
                assert (
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
                    intro. inv H8. rewrite gvs in H9; inv H9.
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
                rewrite H7.
                admit.
                
                (* 1) rename v (rename_all e) = rename_all+v e by  *)
                
                

                
            }                
            assert (Hub' := gsr_preserves_clos _ _ H0 H1 H7).
            destructAll.
            assert (Hse := gsr_preserves_sig_dom _ _ _ H0 H1 H7 H5).
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
                admit.
                SearchAbout b_map_le bound_var.
              - rewrite M.gso by auto; auto.
            }
            rewrite H10 in *.
            destructAll.
            split; auto.
            eapply rt_trans.
            2: apply H6.
            apply H7.
            {             (* size *)
              unfold term_sub_inl_size in *.
              simpl in *; omega.
            }
            {             (* c_count *)
              admit.
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
                do 2 (rewrite <- (proj1 (bound_var_rename_all_ns _ ))).
                normalize_bound_var.
                auto with Ensembles_DB.
            }
            {            (* sig_inv *)
              intro. intros.
              destruct (var_dec x1 v).
              - subst. rewrite M.gss in H10.
                inv H10.
                intro.
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
              - rewrite M.gso in H10 by auto.
                apply Hse in H10.
                auto.
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
            inv H6.
            assert ( (rename_all_ctx_ns sig
            (inlined_ctx_f (comp_ctx_f c (Eproj_c v c0 n0 v0 Hole_c)) im')
                     |[ e0 ]|) = rename_all_ctx_ns sig (inlined_ctx_f c im')
                    |[ Eproj v c0 n0 (apply_r sig v0) e0 ]|) by  ctx_inl_push. 
            unfold ce';  rewrite <- H6.
            split; auto.
            unfold term_sub_inl_size in *. simpl. simpl in H. omega.
            apply cmap_view_proj; auto.
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
            inv H6.
            assert ( (rename_all_ctx_ns sig
            (inlined_ctx_f (comp_ctx_f c (Eproj_c v c0 n0 v0 Hole_c)) im')
                     |[ e1 ]|) = rename_all_ctx_ns sig (inlined_ctx_f c im')
                    |[ Eproj v c0 n0 (apply_r sig v0) e1 ]|) by  ctx_inl_push. 
            unfold ce';  rewrite <- H6.
            split; auto.
            unfold term_sub_inl_size in *. simpl. simpl in H. omega.
            apply cmap_view_proj; auto. 
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
            inv H6.
            assert ( (rename_all_ctx_ns sig
            (inlined_ctx_f (comp_ctx_f c (Eproj_c v c0 n0 v0 Hole_c)) im')
                     |[ e0 ]|) = rename_all_ctx_ns sig (inlined_ctx_f c im')
                    |[ Eproj v c0 n0 (apply_r sig v0) e0 ]|) by  ctx_inl_push. 
            unfold ce';  rewrite <- H6.
            split; auto.
            unfold term_sub_inl_size in *. simpl. simpl in H. omega.
            apply cmap_view_proj; auto. 
      - (* fun *)
        remember (precontractfun sig count sub f).
        destruct p.
        destruct p.
        symmetry in Heqp.
        assert (Heqp' := Heqp).
        eapply precontractfun_corresp with (fds := Fnil) in Heqp; eauto.
        destructAll.
        assert (Hub' := gsr_preserves_clos _ _ H0 H1 H7).
        destruct Hub'.
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
          apply bound_var_rename_all_ns.
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
        (* show that e0 = rename_all_ns sig e0 *)
        (* replace f0 by fundefs_append Fnil f0 *)
        (* use postcontractfun_corresp *)
        admit.
        {
          assert ((forall im, sub_inl_size c0 im <= funs_size f + sub_inl_size sub im /\ funs_size f0 <= funs_size f))%nat. eapply precontractfun_size. eauto.  unfold term_sub_inl_size. simpl. unfold term_sub_inl_size in H; simpl in H. specialize (H14 inl). omega.
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
          * (* function inlining *)
            assert (garvs' := garvs).
            apply H3 in garvs.
            destructAll.
            simpl in ce.
            assert (rename_all_ctx_ns sig
                                      (inlined_ctx_f
                                         (comp_ctx_f x
                                                     (Efun1_c
                                                        (fundefs_append x1 (Fcons (apply_r sig v) f0 l0 e x2)) x0))
                                         inl) |[ Eapp (apply_r sig v) f (apply_r_list sig l) ]| =
                                                                                                (rename_all_ctx_ns sig (inlined_ctx_f x inl)) |[ 
                      Efun (fundefs_append (rename_all_fun_ns sig (inlined_fundefs_f x1 inl)) (Fcons (apply_r sig v) f0 l0 (rename_all_ns sig e) (rename_all_fun_ns sig (inlined_fundefs_f x2 inl)))) (rename_all_ctx_ns sig (inlined_ctx_f x0 inl) |[ Eapp (apply_r sig v) f (apply_r_list sig l)  ]|)
                    ]|).
            {
              ctx_inl_push.
              rewrite inlined_fundefs_append.
              rewrite rename_all_ns_fundefs_append.
              simpl.
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
              - simpl. reflexivity.
            }
            admit.
          * (* not a known function *)
            inv H6.
            unfold ce in *; unfold ce' in *.
            split; auto.
            simpl. apply rt_refl.                    
        + (* multiple occ *)
          inv H6.
          unfold ce in *; unfold ce' in *.
          split; auto.
          simpl. apply rt_refl.                    
      - (* prim -- TODO: modify contract to check for dead prim post *)
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
        destructAll.        
        unfold ce; unfold ce'.
        rewrite H7.
        rewrite H8 in *.
        auto.
        unfold term_sub_inl_size in *.
        simpl in H.
        simpl. omega.        
      - (* halt *)
        inv H6.
        simpl in *.
        unfold ce.
        unfold ce'.
        split; auto.
        apply rt_refl.                
    Admitted.


  
    Theorem contractcases_corresp:
      forall cl2 cl1 sig c im x count sub,
      let ce := (app_ctx_f (rename_all_ctx_ns sig (inlined_ctx_f c im)) (Ecase x (cl1 ++ (rename_all_case sig cl2)))) in
      unique_bindings ce ->
      closed ce ->
      c_count ce count ->
      cmap_view_ctx sub c ->
      inl_inv im sub ce ->
      sig_inv_dom sig ce ->
      forall cl2' count' im' oes pfe pfsub bp,
       contractcases oes (fun rm cm es H => contract rm cm (fst (fst es)) (snd (fst es)) (snd es)) sig count im sub cl2 pfe pfsub = existT _ (cl2', count', im') bp ->
      let ce' := (app_ctx_f (rename_all_ctx_ns sig (inlined_ctx_f c im')) (Ecase x (cl1 ++ cl2'))) in
      gsr_clos ce ce' /\ c_count ce' count' /\ inl_inv im' sub ce'.
    Proof.
      induction cl2; intros; simpl in H5.
      - inv H5; unfold ce in *; unfold ce' in *; split; auto.
        apply rt_refl.                        
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
              2: apply H4.
              unfold ce.
              rewrite bound_var_app_ctx.
              rewrite bound_var_Ecase_app.
              auto with Ensembles_DB.
        }        
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
        eapply shrink_corresp with
        (c :=  (comp_ctx_f c (Ecase_c x cl1 v Hole_c cl2)))
          in Heqcon_e; try (rewrite <- H6; auto).
        Focus 2.
        apply cmap_view_case. auto.

        (* push Disjoint, Unique and Sub_inv through e0 *)
        destructAll.
        rewrite <- H6 in H7.
        assert (Hub' := gsr_preserves_clos _ _ H H0 H7).
        destructAll.
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
                (@snd (prod exp ctx_map) b_map es)) sig c0 b0 sub cl2
             (@subcl_e_cons_l v e cl2
                (@fst exp ctx_map (@fst (prod exp ctx_map) b_map oes))
                (@eq_ind_r (list (prod var exp))
                   (@cons (prod var exp) (@pair var exp v e) cl2)
                   (fun x : list (prod var exp) =>
                    subcl_e x
                      (@fst exp ctx_map (@fst (prod exp ctx_map) b_map oes)))
                   pfe (@cons (prod var exp) (@pair var exp v e) cl2)
                   (@eq_refl (list (prod var exp))
                      (@cons (prod var exp) (@pair var exp v e) cl2))))
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

 Print name_in_fundefs.

 Fixpoint name_in_fundefs_ctx (B : fundefs_ctx) : Ensemble var :=
  match B with
    | Fcons1_c f' _ _ _ B0 => Union var [set f'] (name_in_fundefs B0)
    | Fcons2_c f' _ _ _ B0 => Union var [set f'] (name_in_fundefs_ctx B0)
  end.
 

 
 Theorem bound_var_fundefs_ctx_append_f:
   forall im fdc,
   Included _ (name_in_fundefs_ctx fdc)
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
   Same_set _ (name_in_fundefs_ctx (fundefs_ctx_append fds fdc)) (Union _ (name_in_fundefs fds) (name_in_fundefs_ctx fdc)).
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


    Theorem postcontractfun_corresp:
      forall fds_c fds e c im sub count sig,
      let ce := (app_ctx_f (rename_all_ctx_ns sig (inlined_ctx_f (comp_ctx_f c (Efun1_c (fundefs_append fds fds_c) Hole_c)) im)) (rename_all_ns sig e)) in
      unique_bindings ce ->
      closed ce -> 
      c_count ce count ->
      cmap_view_ctx sub c ->
      inl_inv im sub ce ->
      sig_inv_dom sig ce ->
      forall oes fds_c' count' im' pfe pfsub bp,
       postcontractfun oes (fun rm cm es H => contract rm cm (fst (fst es)) (snd (fst es)) (snd es)) sig count im sub fds_c pfe pfsub = existT _ (fds_c', count', im')  bp ->
       let ce' := (app_ctx_f (rename_all_ctx_ns sig (inlined_ctx_f (comp_ctx_f c (Efun1_c (fundefs_append fds fds_c') Hole_c)) im')) (rename_all_ns sig e)) in
      gsr_clos ce ce' /\ c_count ce' count' /\ inl_inv im' sub ce'.
    Proof.
      induction fds_c; intros.
      Focus 2.
      simpl in H5. inv H5.
      unfold ce in *; unfold ce'.
      split; auto.
      apply rt_refl.      
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
          assert (Hsig_dead := gsr_preserves_sig_dom _ _ _ H H0 Hgsr_dead H4).

          (* I.H. *)
          eapply IHfds_c in H5; eauto.
          * destructAll.
            unfold ce'; split; auto.
            eapply rt_trans; eauto.
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
            assert (get_c v0 (init_census (rename_all sig e)) = n0).
            eapply (proj1 (num_occur_det _)).
            apply init_census_correct.
            rewrite (proj1 (rename_all_no_shadow _)).
            auto.
            intro. intros.
            apply H4 in H9.
            intro. apply H9.
            unfold ce.
            repeat (normalize_ctx; simpl).
            rewrite gbvim.
            apply bound_var_app_ctx.
            left.
            repeat normalize_bound_var_ctx.
            right.
            left.            
            rewrite fundefs_append_bound_vars.
            2: reflexivity.
            right.
            simpl.
            normalize_bound_var.
            rewrite <- (proj1 (bound_var_rename_all_ns _)).
            auto.
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
          

          eapply shrink_corresp in Heqs; eauto.
          (* can add shallow Efun2_c *)
          2: (apply cmap_view_efun2; auto).
          
          
          (* I H *)
          destruct Heqs.
          destruct H8.
          assert (Ht := gsr_preserves_clos _ _ H H0 H7).
          destruct Ht as (Hub_post, Hdj_post).
          assert (Hsig_post := gsr_preserves_sig_dom _ _ _ H H0 H7 H4).
          
          

          assert (He1 : e1 = rename_all_ns sig e1).
          {
            rewrite <- (proj1 (rename_all_no_shadow _)).
            symmetry.
            apply rename_sig_dead.
            intro.             intros.
            apply Hsig_post in H10.
            destructAll.
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
            - apply H9 in gvb0.
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
                  SearchAbout bound_var_ctx comp_ctx_f.
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
                  apply name_in_fundefs_not_inlined; auto.

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
                  apply name_in_fundefs_not_inlined; auto.

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
          destructAll.
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
          auto.
    Qed.

    (* 
    Theorem shrink_corresp_top:
      forall e,
      unique_bindings e ->
      closed e ->
      gsr_clos e (shrink_top e).
    Proof.
      intros.
      unfold shrink_top.
      eapply shrink_corresp with (c := Hole_c); auto.
      rewrite <- (proj1 rename_all_empty).
      rewrite Disjoint_inlined_ctx.
      simpl. reflexivity.
      rewrite bound_var_Hole_c.
      apply Disjoint_Empty_set_l.
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

*)

    End CONTRACT.
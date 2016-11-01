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

Require Import L6.cps.
Require Import L6.ctx L6.logical_relations.
Require Import L6.cps_util L6.List_util L6.shrink_cps L6.eval L6.set_util L6.identifiers.


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


  (* rewrite rules that 
    (1) produces a smaller exp
    (2) preserves the unique binding invariant 

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
| Fun_split: forall lf rf lrf e,
               split_fds lf rf lrf ->    
               Forall (fun v => num_occur_fds rf v 0) (all_fun_name lf) ->
               rw (Efun lrf e) (Efun lf (Efun rf e))

(* Rules about inlining/constant-folding *)
| Constr_case: forall x c' c'e cl co e c'e' ys,
      app_ctx c' (Ecase x cl) c'e ->
      findtag cl co = Some e ->
      ~bound_var_ctx c' x ->
      app_ctx c' e c'e' ->      
      rw (Econstr x co ys c'e) (Econstr x co ys c'e') 
| Constr_proj: forall v  t t' n x e k ys c' c'e c'e', 

                 app_ctx c' (Eproj v t' n x e) c'e ->
                 (* nothing shadows constructor x in c' *)
                 ~ bound_var_ctx c' x ->
                 (* nothing rebinds the projection k in the rest of the term c' *) 
                 ~ bound_var e k ->                
                 nthN ys n = Some k -> 
                 app_ctx c' (rename k v e) c'e' -> 
                 rw (Econstr x t ys c'e) (Econstr x t ys c'e')
| Fun_inline: forall c'  vs c'e f  t xs fb c'e' fds,
                app_ctx c' (Eapp f t vs) c'e ->
                ~ bound_var_ctx c' f -> 
                (*  nothing rebinds vs's in c'e *)
                Forall (fun v => ~bound_var c'e v) vs -> 
                get_fun f fds = Some (t, xs, fb) ->
                app_ctx c' (rename_all (set_list (combine xs vs) (M.empty var)) fb) c'e' ->
                rw (Efun fds c'e) (Efun fds c'e').                     




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
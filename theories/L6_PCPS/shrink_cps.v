Require Import Coq.Relations.Relations.
Require Import Coq.Relations.Relations.
Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.Morphisms.
Import RelationClasses.

Require compcert.lib.Maps.


Require Import ExtLib.Data.Bool.


Require Coq.funind.Recdef.
Import Nnat.
Require Import Coq.Arith.Arith Coq.NArith.BinNat ExtLib.Data.String ExtLib.Data.List Coq.omega.Omega Coq.Program.Program Coq.micromega.Psatz Coq.Sets.Ensembles.
Require Import Coq.Sorting.Permutation.
Require Import Libraries.maps_util.
Require Import L6.cps.
Require Import L6.ctx.
Require Import L6.cps_util L6.List_util L6.identifiers.


(* Shallow val for constr and function *)
Inductive svalue : Type :=
| SVconstr: ctor_tag -> list var -> svalue (* instead of list val *)
| SVfun :  fun_tag -> list var -> exp -> svalue. (* instead of env and full fds *)

(* substitution maps f |-> v where v can stand for a function or a datatype (for projections) *)
Definition ctx_map := M.t svalue.

(* renamer maps x |-> a *)
Definition r_map := M.t var.


(* census maps x |-> total # of occurences *)
Definition c_map :=  M.t nat.

Definition b_map := M.t bool.


Definition getd {A:Type} (d:A) :=
  fun v sub => match M.get v sub with
               | None => d
               | Some e => e
               end.

Definition seto {A:Type} (x:var)(oa:option A) (map:M.t A):=
  match oa with
  | Some a => M.set x a map
  | None => map
  end.

Notation get_c := (getd 0%nat).
Notation get_b := (getd false).


Section MEASURECONTRACT.

  Create HintDb mtss.

  (* compute the number of constructors of an expression *)
  Fixpoint term_size (e: exp) : nat :=
    match e with
    | Econstr _ _ _ e => 1 + term_size e
    | Ecase _ cl => 1 + (List.fold_right (fun (p:(ctor_tag * exp)) =>
                                            fun  (n:nat) => let (k, e) := p in
                                                            (n + (term_size e))%nat) 0%nat cl)
    | Eproj _ _ _ _ e => 1 + term_size e
    | Eletapp _ _ _ _ e => 1 + term_size e
    | Eapp _ _ _ => 1
    | Eprim _ _ _ e => 1 + term_size e
    | Efun fds e => 1 + funs_size fds + term_size e
    | Ehalt _ => 1
    end
  with funs_size fds : nat :=
         match fds with
         | Fcons _ _ _ e fds' => 1 + funs_size fds' + term_size e
         | Fnil => 1
         end.

  Definition svalue_size (v: svalue) : nat :=
    match v with
    | SVconstr t lv => 0
    | SVfun t lv e => term_size e
    end.

  Definition svalue_inl_size (f:(positive*svalue)) (inl:b_map): nat :=
    (if (get_b (fst f) inl) then 0 else svalue_size (snd f)).

  Theorem svalue_inl_le:
    forall i v im,
      svalue_inl_size (i,v) im <= svalue_size v.
  Proof.
    intros.
    unfold svalue_inl_size.
    simpl.
    destruct (get_b i im).
    apply Peano.le_0_n.
    auto.
  Defined.

  Lemma term_size_inline_letapp e x C y e' :
    inline_letapp e x = Some (C, y) ->
    term_size (C |[ e' ]|) <= term_size e + term_size e'.
  Proof.
    generalize C.
    induction e; intros C' Heq;
      simpl in *;
      try ((destruct (inline_letapp e x) as [ [C'' z'] | ] eqn:Heq''; try congruence); inv Heq; simpl; eauto using Peano.le_n_S).
    congruence.
    eapply Peano.le_n_S. specialize (IHe C'' (eq_refl _)). omega.
    inv Heq. simpl. reflexivity.
    inv Heq. simpl. eauto.
  Defined.
  
  (** Computes the sum of the sizes of every unlined function in sub *)
  Definition list_inl_size (sub:list (positive*svalue)) (inl:b_map):=
    fold_right plus 0 (map (fun v => svalue_inl_size v inl) sub).


  Theorem list_inl_size_app: forall l l' inl,
      list_inl_size (l++l') inl = list_inl_size l inl + list_inl_size l' inl .
  Proof.
    induction l; intros.
    reflexivity.
    unfold list_inl_size. simpl.
    unfold list_inl_size in IHl.
    rewrite IHl.
    rewrite <- Nat.add_assoc.
    reflexivity.
  Qed.

  Definition sub_inl_size (sub:ctx_map) (inl:b_map):=
    fold_left plus (map (fun v => svalue_inl_size v inl) (M.elements sub)) 0.

  Theorem sub_inl_proof:
    forall sub inl,
      sub_inl_size sub inl =
      list_inl_size (M.elements sub) inl.
  Proof.
    unfold sub_inl_size, list_inl_size. intros. apply fold_symmetric; intros; omega.
  Qed.


  Theorem min_term_size:
    forall e, 1 <= term_size e.
  Proof. intro.
         destruct e; simpl; apply lt_le_S; apply Nat.lt_0_succ.
  Defined.

  Theorem min_funs_size:
    forall f, 1 <= funs_size f.
  Proof.
    destruct f; simpl; apply lt_le_S; apply Nat.lt_0_succ.
  Defined.


  Theorem funs_size_append: forall f2 f1,
      funs_size (fundefs_append f1 f2) = funs_size f1 + funs_size f2 - 1.
  Proof.
    induction f1; simpl; intros.
    rewrite IHf1.
    assert (Hf2 := min_funs_size f2).
    assert (Hf1 := min_funs_size f1).
    omega.
    omega.
  Defined.

  Definition term_sub_inl_size (esi: (exp * ctx_map * b_map)): nat :=
    term_size (fst (fst esi)) + sub_inl_size (snd (fst esi)) (snd esi).


  (* TODO:move maybe to List_util? *)
  Theorem NoDup_list_norepet:
    forall {A} (l:list A), NoDup l <-> Coqlib.list_norepet l.
  Proof.
    intros.
    induction l; split; intro; auto.
    constructor. constructor.
    inv H; constructor; eauto.
    apply  IHl. auto.
    inv H; constructor; auto.
    apply IHl. auto.
  Qed.


  Theorem fold_right_plus_init:
    forall l n,
      fold_right plus n l = fold_right plus 0 l + n.
  Proof.
    induction l; intros.
    reflexivity.
    simpl. rewrite IHl. omega.
  Qed.

  Theorem svalue_inl_not: forall a x im,
      fst a <> x ->
      svalue_inl_size a (M.set x true im) = svalue_inl_size a im.
  Proof.
    intros. destruct a.
    unfold svalue_inl_size. simpl in *.
    unfold get_b. rewrite M.gso; auto.
  Qed.

  Theorem list_inl_size_not_in: forall x im x0,
      ~ List.In x (map fst x0) ->
      list_inl_size x0 (M.set x true im) = list_inl_size x0 im.
  Proof.
    induction x0; unfold list_inl_size in *; intros.
    auto.
    simpl. rewrite IHx0.
    rewrite svalue_inl_not. auto.
    intro; apply H. simpl. auto.
    intro. apply H.
    destruct a. simpl. auto.
  Qed.

  Theorem sub_inl_fun_size: forall x t xs e im sub,
      M.get x sub = Some (SVfun t xs e) ->
      get_b x im = false ->
      (sub_inl_size sub im  = sub_inl_size sub (M.set x true im) + term_size e )%nat.
  Proof.
    intros.
    apply M.elements_remove in H.
    destructAll.
    do 2 (rewrite sub_inl_proof).
    assert (NoDup (List.map fst (M.elements sub))).
    apply NoDup_list_norepet. apply M.elements_keys_norepet.
    rewrite H in H2.
    rewrite Coqlib.list_append_map in H2.
    simpl in H2.
    apply NoDup_remove_2 in H2.
    rewrite H.
    do 2 (rewrite list_inl_size_app).
    rewrite list_inl_size_not_in.
    unfold list_inl_size. simpl.
    assert (~List.In x (map fst x1)).
    intro. apply H2.
    apply Coqlib.in_app. auto.
    eapply list_inl_size_not_in in H3.
    unfold list_inl_size in H3. rewrite H3.
    unfold svalue_inl_size.
    simpl. rewrite H0.
    unfold get_b. rewrite M.gss. omega.
    intro. apply H2.
    apply Coqlib.in_app. auto.
  Qed.


  Hint Resolve sub_inl_fun_size: mtss.


  Theorem sub_remove_size':
    forall x sub inl,
      (sub_inl_size (M.remove x sub) inl <= sub_inl_size sub inl)%nat.
  Proof.
    intros.
    destruct (M.get x sub) eqn:gxs.
    - do 2 (rewrite sub_inl_proof).
      apply M.elements_remove in gxs.
      destructAll.
      rewrite H. rewrite H0.
      unfold list_inl_size.
      do 2 (rewrite Coqlib.list_append_map).
      simpl.
      do 2 (rewrite fold_right_app). simpl.
      rewrite fold_right_plus_init.
      rewrite fold_right_plus_init with
          (n := (svalue_inl_size (x, s) inl + fold_right Init.Nat.add 0 (map (fun v : positive * svalue => svalue_inl_size v inl) x1))).
      omega.
    - unfold sub_inl_size.
      erewrite M.elements_extensional.
      apply Nat.eq_le_incl.
      reflexivity.
      apply remove_none. auto.
  Qed.



  Theorem set_none_size:
    forall x sub im v,
      M.get x sub = None ->
      (sub_inl_size (M.set x v sub) im =  svalue_inl_size (x,v) im + sub_inl_size sub im)%nat.
  Proof.
    intros x sub im v gxs.
    do 2 (rewrite sub_inl_proof).
    apply elements_set_none with (v := v) in gxs. destructAll.
    rewrite H, H0.
    clear H0. clear H. unfold list_inl_size.
    do 2 (rewrite Coqlib.list_append_map).
    simpl.
    do 2 (rewrite fold_right_app).
    simpl.
    rewrite fold_right_plus_init.
    rewrite fold_right_plus_init with (n := (fold_right Init.Nat.add 0 (map (fun v0 : positive * svalue => svalue_inl_size v0 im) x1))).
    assert (svalue_inl_size (x, v) im <= svalue_size v) by apply svalue_inl_le.
    omega.
  Qed.

  Theorem set_some_size:
    forall x sub im v v',
      M.get x sub = Some v' ->
      (sub_inl_size (M.set x v sub) im + svalue_inl_size (x, v') im = sub_inl_size sub im + svalue_inl_size (x,v) im)%nat.
  Proof.
    intros x sub im v v' gxs.
    do 2 (rewrite sub_inl_proof).
    apply elements_set_some with (v := v) in gxs.
    destructAll. rewrite H, H0.
    clear H; clear H0.
    unfold list_inl_size.
    do 2 (rewrite Coqlib.list_append_map).
    simpl.
    do 2 (rewrite fold_right_app).
    simpl.
    rewrite fold_right_plus_init.
    rewrite fold_right_plus_init
      with (n := (svalue_inl_size (x, v') im + fold_right Init.Nat.add 0 (map (fun v0 : positive * svalue => svalue_inl_size v0 im) x1))).
    omega.
  Qed.


  Theorem sub_set_size:
    forall v x sub im, (sub_inl_size (M.set x v sub) im  <= svalue_size v + sub_inl_size sub im)%nat.
  Proof.
    intros.
    assert (svalue_inl_size (x, v) im <= svalue_size v) by apply svalue_inl_le.
    destruct (M.get x sub) eqn:gxs.
    - apply set_some_size with (v := v) (im := im) in gxs.
      omega.
    - apply set_none_size with (v := v) (im := im) in gxs.
      omega.
  Qed.

  Theorem constr_sub_size:
    forall e v t lv sub im,
      (term_sub_inl_size (e, M.set v (SVconstr t lv) sub, im) < term_sub_inl_size (Econstr v t lv e, sub, im))%nat.
  Proof.
    intros. unfold term_sub_inl_size. simpl.
    assert ((sub_inl_size (M.set v (SVconstr t lv) sub) im <= svalue_size (SVconstr t lv)  + sub_inl_size sub im))%nat.
    apply sub_set_size. simpl in H. omega.
  Defined.

  Theorem subfds_fds_size: forall fds' fds, subfds_fds fds fds' -> (funs_size fds < funs_size fds')%nat.
  Proof.
    induction fds'; intros.
    - inversion H; subst. apply IHfds' in H2. simpl. omega. simpl. omega.
    - inversion H.
  Defined.

  Theorem case_size:
    forall g v k cl,
      List.In (g, k) cl ->
      (term_size k < term_size (Ecase v cl))%nat.
  Proof.
    induction cl; intro; simpl in H.
    - inversion H.
    - destruct a.
      inv H.
      + inv H0.
        simpl. omega.
      + apply IHcl in H0.
        simpl. simpl in H0.
        omega.
  Defined.

  Theorem dsubterm_fds_size:
    forall e fds,
      dsubterm_fds_e e fds -> (term_size e < funs_size fds)%nat.
  Proof.
    induction fds; intros.
    inv H. simpl. omega.
    apply IHfds in H2. simpl; omega.
    inv H.
  Defined.

  Theorem dsubterm_size:
    forall e e',
      dsubterm_e e' e -> term_size e' < term_size e.
  Proof.
    intros. inv H; auto.
    -  eapply case_size; eauto.
    - apply dsubterm_fds_size in H0. simpl. omega.
    - simpl. omega.
  Defined.


  Theorem subterm_size :
    forall e e',
      subterm_e e' e -> (term_size e' < term_size e)%nat.
  Proof.
    intros. induction H.
    - apply dsubterm_size; auto.
    - eapply transitivity; eauto.
  Defined.

  Theorem subterm_fds_size:
    forall e fds,
      subterm_fds_e e fds -> (term_size e < funs_size fds)%nat.
  Proof.
    intros. induction H.
    - apply subterm_size in H.  simpl. omega.
    - simpl. omega.
  Defined.

  
  Theorem subterm_or_eq_size:
    forall e e', subterm_or_eq e e' -> (term_size e <= term_size e')%nat.
  Proof.
    intros. induction H.
    apply dsubterm_size in H; omega.
    reflexivity.
    etransitivity; eauto.
  Defined.


  Theorem subfds_or_eq_size:
    forall fds fds', subfds_or_eq fds fds' -> (funs_size fds <= funs_size fds')%nat.
  Proof.
    destruct fds; intros; inversion H; try (subst; reflexivity).
    - apply subfds_fds_size in H0. omega.
    - inversion H0; subst. simpl; omega.  simpl; omega.
  Defined.

  Corollary subfds_e_size:
    forall fds e, subfds_e fds e -> (funs_size fds < term_size e)%nat.
  Proof.
    intros. inversion H. destructAll. apply subfds_or_eq_size in H1. apply subterm_or_eq_size in H0. simpl in H0. omega.
  Defined.


  Definition b_map_le: b_map -> b_map -> Prop :=
    fun inl inl_r => forall v, get_b v inl = true -> get_b v inl_r = true.
  
  Theorem b_map_le_refl: forall i,
      b_map_le i i.
  Proof.
    intros; intro; intros. assumption.
  Defined.

  Theorem b_map_le_trans: forall i i' i'',
      b_map_le i i' -> b_map_le i' i'' -> b_map_le i i''.
  Proof.
    intros; intro; intros. apply H in H1. apply H0 in H1. assumption.
  Defined.

  Theorem b_map_le_true : forall v i,
      b_map_le   i  (M.set v true i).
  Proof.
    intros. intro. intros.
    destruct (var_dec v0 v); subst.
    -  apply gdss.
    - rewrite gdso by auto. apply H.
  Defined.

  Theorem svalue_inl_b_map_le : forall inl inl',
      b_map_le inl inl' ->
      forall v,
        svalue_inl_size v inl' <= svalue_inl_size v inl.
  Proof.
    intros. unfold svalue_inl_size. destruct v; simpl.
    destruct (get_b p inl) eqn:gbp.
    apply  H in gbp. rewrite gbp; auto.
    destruct (get_b p inl'); omega.
  Qed.


  Theorem sub_size_le : forall sub inl inl',
      b_map_le inl inl' ->
      sub_inl_size sub inl' <= sub_inl_size sub inl.
  Proof.
    intros.
    do 2 (rewrite sub_inl_proof). remember (M.elements sub) as l.
    clear Heql. induction l.
    reflexivity.
    unfold list_inl_size in *. simpl.
    assert ( svalue_inl_size a inl' <=  svalue_inl_size a inl) by (apply svalue_inl_b_map_le; auto).
    omega.
  Qed.

  Inductive b_map_le_i : b_map -> b_map -> Prop :=
  | ble_refl: forall b, b_map_le_i b b
  | ble_add : forall b b' v, b_map_le_i b b' ->
                             b_map_le_i b (M.set v true b').

  Theorem b_map_le_c :
    forall b b',
      b_map_le_i b b' -> b_map_le b b'.
  Proof.
    intros.
    induction H.
    apply b_map_le_refl.
    subst.
    eapply b_map_le_trans. apply IHb_map_le_i.
    apply b_map_le_true.
  Defined.

  Theorem b_map_le_i_trans:
    forall b b',
      b_map_le_i b b' ->
      forall b'',
        b_map_le_i b' b'' ->
        b_map_le_i b b''.
  Proof.
    intros b b' H b'' H'. induction H'; intros.
    assumption.
    apply ble_add. apply IHH'. assumption.
  Defined.

  Theorem b_map_i_true:
    forall b b' v,
      (b_map_le_i (M.set v true b) b' ->
       b_map_le_i b b').
  Proof.
    intros b b' v H.
    remember (M.set v true b) as tb.
    induction H.
    rewrite Heqtb. constructor 2; constructor.
    constructor 2. apply IHb_map_le_i in Heqtb. assumption.
  Defined.


End MEASURECONTRACT.



(* option_map on pairs of option *)
Fixpoint f_opt {A} f on om : option A :=
  match on with
  | Some n =>
    (match om with
     | Some m => Some (f n m)
     | None => Some n
     end)
  | None => om
  end.

Definition f_pair {A B C D} (f: A -> A -> B) (g: C -> C -> D)
  : (A * C) -> (A * C) -> (B * D) :=
  fun e1 e2 => match (e1, e2) with
               | ( (a1, c1), (a2, c2)) => ( f a1 a2 , g c1 c2)
               end.


Definition apply_r sigma y :=
  match (@M.get M.elt y sigma) with
  | Some v => v
  | None => y
  end.

Definition apply_r_list sigma ys :=
  map (apply_r sigma) ys.

Definition tag := positive.

Theorem prop_apply_r: (forall v, forall sub sub', map_get_r _ sub sub' -> apply_r sub v = apply_r sub' v).
Proof.
  intros.
  unfold apply_r.
  destruct (M.get v sub) eqn:gvs.
  rewrite H in gvs. rewrite gvs. auto.
  rewrite H in gvs. rewrite gvs; auto.
Defined.

Theorem prop_apply_r_list: (forall l, forall sub sub', map_get_r _ sub sub' -> apply_r_list sub l = apply_r_list sub' l).
Proof.
  induction l; intros.
  reflexivity.
  simpl. erewrite IHl; eauto.
  erewrite prop_apply_r; eauto.
Defined.


Theorem apply_r_empty: forall v, apply_r (M.empty var) v = v.
Proof.
  intro. unfold apply_r.
  rewrite M.gempty. auto.
Defined.

Theorem apply_r_list_empty: forall l, apply_r_list (M.empty var) l = l.
Proof.
  induction l; auto.
  simpl. rewrite IHl. rewrite apply_r_empty. reflexivity.
Defined.

Fixpoint all_fun_name (fds:fundefs) : list var :=
  match fds with
  | Fcons f t ys e fds' => f::(all_fun_name fds')
  | Fnil => []
  end.

Fixpoint remove_all (sigma:r_map) (vs:list var) :=
  match vs with
  | v::vs' => M.remove v (remove_all sigma vs')
  | [] => sigma
  end.

Fixpoint update_census_list (sig:r_map) (ys:list var) (fun_delta:var -> c_map -> nat) (count:c_map) :=
  match ys with
  | [] => count
  | y::ys' =>
    let y' := apply_r sig y in
    update_census_list sig ys' fun_delta (M.set y' (fun_delta y' count) count)
  end.



(* assumes Disjoint (Dom sig) (BV e) *)
Fixpoint update_census (sig:r_map) (e:exp) (fun_delta:var -> c_map -> nat) (count:c_map) : c_map :=
  match e with
  | Econstr x t ys e =>
    let count' := update_census_list sig ys fun_delta count in
    update_census sig e fun_delta count'
  | Eprim x f ys e =>
    let count' := update_census_list sig ys fun_delta count in
    update_census sig e fun_delta count'
  | Ecase v cl =>
    let count' := update_census_list sig [v] fun_delta count in
    fold_right (fun (p:(var*exp)) c =>
                  let (k, e) := p in
                  update_census sig e fun_delta c) count' cl

  | Eproj v t n y e =>
    let count' := update_census_list sig [y] fun_delta count in
    update_census sig e fun_delta count'
  | Eletapp v f ft ys e =>
    let count' := update_census_list sig (f :: ys) fun_delta count in
    update_census sig e fun_delta count'
  | Efun fl e =>
    let fname := all_fun_name fl in
    let count' := update_census_f sig fl fun_delta count in
    update_census sig e fun_delta count'
  | Eapp f t ys => update_census_list sig (f::ys) fun_delta count
  | Ehalt v => update_census_list sig [v] fun_delta count
  end
with update_census_f (sig:r_map) (fds:fundefs) (fun_delta: var -> c_map -> nat) (count:c_map): c_map :=
       match fds with
       | Fcons v t ys e fds' => let count' := update_census sig e fun_delta count in
                                update_census_f sig fds' fun_delta count'
       | Fnil => count
       end
.

Definition init_census (e:exp) := update_census (M.empty var) e (fun v c => get_c v c + 1)%nat (M.empty nat).
Definition dec_census (sig:r_map) (e:exp) (count:c_map) := update_census sig e (fun v c => get_c v c - 1)%nat  count.
Definition dec_census_list (sig:r_map) (ys:list var) (count:c_map) := update_census_list sig ys (fun v c => get_c v c - 1)%nat count.

(* Decrease the count by each clause *)
Fixpoint dec_census_all_case (sig:r_map) (cl:list (var*exp))  (count:c_map) :=
  match cl with
  | [] => count
  | (k, e)::cl' =>
    let count' := dec_census_all_case sig cl' count in
    dec_census sig e count'
  end.

(* Decrease the count by each cl except the first one that matches y *)
Fixpoint dec_census_case (sig:r_map) (cl:list (var*exp)) (y:var) (count:c_map) :=
  match cl with
  | [] => count
  | (k, e)::cl' =>
    if (var_dec k y) then
      dec_census_all_case sig cl' count
    else
      let count' := dec_census_case sig cl' y count in
      dec_census sig e count'
  end.

(* assume NoDup(xs) *)
Fixpoint update_count_inlined (ys:list var) (xs:list var) (count:c_map) :=
  match ys, xs with
  | y::ys', x::xs' =>
    let cy := get_c y count in
    let cx := get_c x count in
    update_count_inlined ys' xs'  (M.set y (cy + cx - 1) (M.set x 0 count))%nat
  | _, _ => count
  end.


Section RENAME.


  Fixpoint rename_all (sigma:r_map) (e:exp) : exp :=
    match e with
    | Econstr x t ys e' => Econstr x t (apply_r_list sigma ys) (rename_all (M.remove x sigma) e')
    | Eprim x f ys e' => Eprim x f (apply_r_list sigma ys) (rename_all (M.remove x sigma) e')
    | Eletapp x f ft ys e' => Eletapp x (apply_r sigma f) ft (apply_r_list sigma ys)
                                      (rename_all (M.remove x sigma) e')
    | Eproj v t n y e' => Eproj v t n (apply_r sigma y) (rename_all (M.remove v sigma) e')
    | Ecase v cl =>
      Ecase (apply_r sigma v) (List.map (fun (p:var*exp) => let (k, e) := p in
                                                            (k, rename_all sigma e)) cl)
    | Efun fl e' =>
      let fs := all_fun_name fl in
      let fl' := rename_all_fun (remove_all sigma fs) fl in

      Efun fl' (rename_all (remove_all sigma fs) e')
    | Eapp f t ys =>
      Eapp (apply_r sigma f) t (apply_r_list sigma ys)
    | Ehalt v => Ehalt (apply_r sigma v)
    end
  with rename_all_fun (sigma:r_map) (fds:fundefs): fundefs :=
         match fds with
         | Fnil => Fnil
         | Fcons v' t ys e fds' => Fcons v' t ys (rename_all (remove_all sigma ys) e) (rename_all_fun sigma fds')
         end.

  Theorem rename_all_fun_name: forall rho fds,
      Same_set _ (name_in_fundefs (rename_all_fun rho fds)) (name_in_fundefs fds).
  Proof.
    induction fds.
    - simpl. eauto with Ensembles_DB.
    - reflexivity.
  Defined.


  Theorem prop_remove_all: 
    forall l sub sub', map_get_r _ sub sub' -> map_get_r _ (remove_all sub l) (remove_all sub' l).
  Proof.
    induction l; intros.  
    - auto.
    - simpl. apply proper_remove. apply IHl; eauto. 
  Defined.


  Theorem prop_rename_all: (forall e, forall sub sub', map_get_r _ sub sub' -> rename_all sub e = rename_all sub' e) /\
                           (forall fds, forall sub sub', map_get_r _ sub sub' -> rename_all_fun sub fds = rename_all_fun sub' fds) .
  Proof.
    apply exp_def_mutual_ind; intros; simpl.
    - erewrite prop_apply_r_list; eauto. erewrite H; eauto. apply proper_remove; auto.
    - erewrite prop_apply_r; eauto.
    - erewrite H; eauto.
      erewrite prop_apply_r; eauto.
      apply H0 in H1. simpl in H1. inversion H1; subst. reflexivity.
    - erewrite prop_apply_r; eauto. erewrite H; eauto. apply proper_remove; auto.
    - erewrite prop_apply_r; eauto. erewrite prop_apply_r_list; eauto. erewrite H; eauto. apply proper_remove; auto.
    - erewrite H0; eauto. erewrite H; eauto.
      apply prop_remove_all; auto.
      apply prop_remove_all; auto.
    - erewrite prop_apply_r; eauto. erewrite prop_apply_r_list; eauto.
    - erewrite prop_apply_r_list; eauto. erewrite H; eauto. apply proper_remove; auto.
    - erewrite prop_apply_r; eauto.
    - erewrite H; eauto. erewrite H0; eauto. apply prop_remove_all; auto.
    - reflexivity.
  Defined.




  Theorem remove_all_empty: forall l, map_get_r _ (remove_all (M.empty var) l)  (M.empty var).
  Proof.
    induction l; intros; simpl; auto.
    - apply smg_refl. 
    - eapply smg_trans. eapply proper_remove. eassumption.
      apply remove_empty.
  Defined.

  Theorem remove_all_not_in: 
    forall x z l rho,
      ~ (List.In x l) ->
      map_get_r _ (remove_all (M.set x z rho) l) (M.set x z (remove_all rho l)).
  Proof.
    induction l; intros; simpl.
    - apply smg_refl.
    - eapply smg_trans. eapply proper_remove.
      eapply IHl. intros Hc. eapply H; now right.
      apply remove_set_2. intros Hc; subst; eapply H; now left.
  Defined.


  Theorem remove_all_in: 
    forall x z l rho,
      List.In x l ->
      map_get_r _ (remove_all (M.set x z rho) l) (remove_all rho l).
  Proof.
    induction l; intros; simpl; auto.
    - inversion H.
    - simpl in H. 
      destruct (var_dec x a); subst.
      + edestruct (ListDec.In_decidable) with (l := l) (x := a) as [Hd | ]. 
        { intros x y. destruct (DecidableTypeEx.Positive_as_DT.eq_dec x y); subst; eauto.
          left; eauto. right; eauto. }
        * eapply proper_remove. eapply IHl. eauto.
        * eapply smg_trans. eapply proper_remove. 
          eapply remove_all_not_in. eassumption.    
          apply remove_set_1.
      + inv H. exfalso; eauto. eapply proper_remove. eapply IHl. eauto.
  Qed.


  Theorem rename_all_empty: (forall e,
                                e = rename_all (M.empty var) e) /\
                            (forall fds, fds = rename_all_fun (M.empty var) fds).
  Proof.
    apply exp_def_mutual_ind; intros; simpl.
    - rewrite apply_r_list_empty.
      replace (rename_all (M.remove v (M.empty var)) e) with e. reflexivity.
      rewrite H at 1.
      apply prop_rename_all.
      apply smg_sym.
      apply remove_empty.
    - rewrite apply_r_empty.  reflexivity.
    - rewrite apply_r_empty. rewrite <- H. simpl in H0. inversion H0.
      rewrite <- H3. rewrite <- H3. reflexivity.
    - rewrite apply_r_empty.
      replace (rename_all (M.remove v (M.empty var)) e) with e. reflexivity.
      rewrite H at 1.
      apply prop_rename_all.
      apply smg_sym.
      apply remove_empty.
    - rewrite apply_r_empty, apply_r_list_empty.
      replace (rename_all (M.remove x (M.empty var)) e) with e. reflexivity.
      rewrite H at 1.
      apply prop_rename_all.
      apply smg_sym.
      apply remove_empty.
    - replace (rename_all (remove_all (M.empty var) (all_fun_name f2)) e) with e.
      replace (rename_all_fun (remove_all (M.empty var) (all_fun_name f2)) f2) with f2; auto.
      rewrite H at 1.
      eapply prop_rename_all.
      apply smg_sym.
      apply remove_all_empty.
      rewrite H0 at 1.
      eapply prop_rename_all.
      apply smg_sym.
      apply remove_all_empty.
    - rewrite apply_r_empty.
      rewrite apply_r_list_empty. auto.
    - rewrite apply_r_list_empty.
      replace (rename_all (M.remove v (M.empty var)) e) with e. reflexivity.
      rewrite H at 1.
      apply prop_rename_all.
      apply smg_sym.
      apply remove_empty.
    -     rewrite apply_r_empty. auto.
    - rewrite <- H0.
      replace (rename_all (remove_all (M.empty var) l) e) with e.
      reflexivity.
      rewrite H at 1.
      eapply prop_rename_all.
      apply smg_sym.
      apply remove_all_empty.
    - auto.
  Defined.


  Fixpoint all_fun_name_ctx (cfds:fundefs_ctx) : list var :=
    match cfds with
    | Fcons1_c f t ys c fds' => f::(all_fun_name fds')
    | Fcons2_c f t ys e cfds' => f::(all_fun_name_ctx cfds')
    end.

  Theorem all_fun_name_ctx_same:
    forall e f,
      all_fun_name_ctx f = all_fun_name (f <[ e ]>).
  Proof.
    induction f; auto.
    simpl.
    rewrite IHf. auto.
  Defined.


  Fixpoint rename_all_ctx (sigma:r_map) (c:exp_ctx): exp_ctx :=
    match c with
    | Hole_c => Hole_c
    | Econstr_c x t ys c' =>
      Econstr_c x t (apply_r_list sigma ys) (rename_all_ctx (M.remove x sigma) c')
    | Eprim_c x f ys c' =>
      Eprim_c x f (apply_r_list sigma ys) (rename_all_ctx (M.remove x sigma) c')
    | Eproj_c v t n y c' => Eproj_c v t n (apply_r sigma y) (rename_all_ctx (M.remove v sigma) c')
    | Eletapp_c v f ft ys c' => Eletapp_c v (apply_r sigma f) ft (apply_r_list sigma ys)
                                          (rename_all_ctx (M.remove v sigma) c')
    | Ecase_c v l t c' l' =>
      let f cl := (List.map (fun (p:var*exp) => let (k, e) := p in
                                                (k, rename_all sigma e)) cl) in
      Ecase_c (apply_r sigma v) (f l) t (rename_all_ctx sigma c') (f l')
    | Efun1_c fl c' =>
      let fs := all_fun_name fl in
      let fl' := rename_all_fun (remove_all sigma fs) fl in
      Efun1_c fl' (rename_all_ctx (remove_all sigma fs) c')
    | Efun2_c cf e =>
      let fs := all_fun_name_ctx cf in
      let cf' := rename_all_fun_ctx (remove_all sigma fs) cf in
      Efun2_c cf' (rename_all (remove_all sigma fs) e)
    end
  with rename_all_fun_ctx (sigma:r_map) (fc: fundefs_ctx): fundefs_ctx :=
         match fc with
         | Fcons1_c f t ys c fds' =>  Fcons1_c f t ys (rename_all_ctx (remove_all sigma ys) c) (rename_all_fun sigma fds')
         | Fcons2_c f t ys e cfds' =>  Fcons2_c f t ys (rename_all (remove_all sigma ys) e) (rename_all_fun_ctx sigma cfds')
         end.


  (* no-shadow version of rename_all. *)
  Fixpoint rename_all_ns (sigma:r_map) (e:exp) : exp :=
    match e with
    | Econstr x t ys e' => Econstr x t (apply_r_list sigma ys) (rename_all_ns sigma e')
    | Eprim x f ys e' => Eprim x f (apply_r_list sigma ys) (rename_all_ns sigma e')
    | Eproj v t n y e' => Eproj v t n (apply_r sigma y) (rename_all_ns sigma e')
    | Eletapp v f t ys e' => Eletapp v (apply_r sigma f) t (apply_r_list sigma ys) (rename_all_ns sigma e')
    | Ecase v cl =>
      Ecase (apply_r sigma v) (List.map (fun (p:var*exp) => let (k, e) := p in
                                                            (k, rename_all_ns sigma e)) cl)
    | Efun fl e' =>
      let fl' := rename_all_fun_ns sigma fl in
      Efun fl' (rename_all_ns sigma e')
    | Eapp f t ys =>
      Eapp (apply_r sigma f) t (apply_r_list sigma ys)
    | Ehalt v => Ehalt (apply_r sigma v)
    end
  with rename_all_fun_ns (sigma:r_map) (fds:fundefs): fundefs :=
         match fds with
         | Fnil => Fnil
         | Fcons v' t ys e fds' => Fcons v' t ys (rename_all_ns sigma e) (rename_all_fun_ns sigma fds')
         end.


  Fixpoint rename_all_ctx_ns (sigma:r_map) (c:exp_ctx): exp_ctx :=
    match c with
    | Hole_c => Hole_c
    | Econstr_c x t ys c' =>
      Econstr_c x t (apply_r_list sigma ys) (rename_all_ctx_ns sigma c')
    | Eprim_c x f ys c' =>
      Eprim_c x f (apply_r_list sigma ys) (rename_all_ctx_ns sigma c')
    | Eproj_c v t n y c' => Eproj_c v t n (apply_r sigma y) (rename_all_ctx_ns sigma c')
    | Eletapp_c v f ft ys c' => Eletapp_c v (apply_r sigma f) ft (apply_r_list sigma ys)
                                          (rename_all_ctx_ns sigma c')
    | Ecase_c v l t c' l' =>
      let f cl := (List.map (fun (p:var*exp) => let (k, e) := p in
                                                (k, rename_all_ns sigma e)) cl) in
      Ecase_c (apply_r sigma v) (f l) t (rename_all_ctx_ns sigma c') (f l')
    | Efun1_c fl c' =>
      let fl' := rename_all_fun_ns sigma fl in
      Efun1_c fl' (rename_all_ctx_ns sigma c')
    | Efun2_c cf e =>
      let cf' := rename_all_fun_ctx_ns sigma cf in
      Efun2_c cf' (rename_all_ns sigma e)
    end
  with rename_all_fun_ctx_ns (sigma:r_map) (fc: fundefs_ctx): fundefs_ctx :=
         match fc with
         | Fcons1_c f t ys c fds' =>  Fcons1_c f t ys (rename_all_ctx_ns sigma c) (rename_all_fun_ns sigma fds')
         | Fcons2_c f t ys e cfds' =>  Fcons2_c f t ys (rename_all_ns sigma e) (rename_all_fun_ctx_ns sigma cfds')
         end.

  Definition rename y x e :=
    rename_all (M.set x y (M.empty var)) e.
  
  Transparent rename.
End RENAME.

Section CONTRACT.

  (* Type of shrink program *)
  Definition shrinkT A (im : b_map) : Type := {esir:(A * nat * c_map * b_map) & (b_map_le_i im (snd esir))}.
  
  
  Fixpoint precontractfun (sig:r_map) (count:c_map) (sub:ctx_map) (fds:fundefs) (steps : nat): (fundefs * nat * c_map * ctx_map) :=
    match fds with
    | Fcons f t ys e fds' =>
      match (get_c f count) with
      | 0%nat =>
        let count' := dec_census sig e count in
        precontractfun sig count' sub fds' (steps + 1)
      | _ =>
        let '(fds'', steps', count', sub') := precontractfun sig count sub fds' steps in
        (Fcons f t ys e fds'', steps', count', (M.set f (SVfun t ys e) sub'))
      end
    | Fnil => (Fnil, steps, count, sub)
    end.


  Theorem precontractfun_size:
    forall fds steps sig count sub fds' steps' count' sub',
      ((fds', steps', count', sub') =  precontractfun sig count sub fds steps ->
       (forall im, sub_inl_size sub' im <= funs_size (fds) + sub_inl_size sub im /\ funs_size fds' <= funs_size fds))%nat.
  Proof.
    induction fds; intros; simpl in H.
    - destruct (get_c v count) eqn: gcvc.
      + specialize (IHfds _ _ _ _ _ _ _ _ H im). simpl. destruct IHfds. split.
        rewrite <- Nat.add_assoc.
        rewrite Nat.add_comm. rewrite <- Nat.add_assoc. rewrite <- Nat.add_succ_l.
        rewrite <- Nat.add_0_r with (n :=sub_inl_size sub' im ).
        rewrite Nat.add_comm.
        apply Nat.add_le_mono.  apply le_0_n.
        rewrite Nat.add_comm. apply H0.
        rewrite <- Nat.add_succ_r.
        rewrite <- Nat.add_0_r with (n := funs_size fds').
        apply Nat.add_le_mono. assumption. apply le_0_n.
      + assert (exists fds' count' sub' steps', (fds', steps', count', sub') = precontractfun sig count sub fds steps).
        destruct (precontractfun sig count sub fds). destruct p. destruct p.
        eauto. destructAll. assert (H0' := H0).
         specialize (IHfds _ _ _ _ _ _ _ _ H0 im).  rewrite <- H0' in H. inversion H; subst. simpl. split.
         eapply Nat.le_trans. apply sub_set_size.  simpl.  destruct IHfds.
         constructor. rewrite Nat.add_comm with (n := funs_size fds). rewrite <- Nat.add_assoc.
         apply Nat.add_le_mono. reflexivity. assumption.
         apply le_n_S. apply Nat.add_le_mono. destruct IHfds; assumption. reflexivity.
    -  inversion H; subst. simpl.
       split. constructor; reflexivity. reflexivity.
  Defined.

  Definition sublist {A:Type} (l:list A) (l':list A): Prop :=
    forall x, List.In x l -> List.In x l'.

  Definition subcl_e: list (var*exp) -> exp -> Prop :=
    fun cl' e =>
      exists y cl, e = Ecase y cl /\ sublist cl' cl.

  Theorem subcl_refl:
    forall {v} cl,
      subcl_e cl (Ecase v cl).
  Proof.
    intros.
    exists v. exists cl.
    split. reflexivity.
    intro; intros; assumption.
  Defined.

  (* termination conditions for contractcases *)
  Theorem subcl_size {y e cl' e0 sub inl c b}:
    subcl_e ((y, e) :: cl') e0 ->
    sub_inl_size sub inl <= sub_inl_size c b ->
    term_sub_inl_size (e, sub, inl) < term_sub_inl_size (e0, c, b).
  Proof.
    intros pfe pfsub.
    inversion pfe.
    destructAll.
    unfold term_sub_inl_size; simpl.
    assert (term_size e < term_size (Ecase x x0)).
    eapply case_size.
    inv pfe. destruct H. destruct H. inv H. apply H1. constructor. reflexivity.
    simpl in H.
    rewrite <- Nat.add_succ_l.
    apply Nat.add_lt_le_mono.
    apply H.
    assumption.
  Defined.

  Theorem  subcl_e_cons_l {y e cl e0}:
    subcl_e ((y, e) :: cl) e0 ->
    subcl_e cl e0.
  Proof.
    intros.
    inv H.
    destructAll.
    exists x, x0.
    split. reflexivity.
    intro. intros.
    apply H0.
    constructor 2. assumption.
  Defined.

  Theorem sub_inl_size_compat {sub inl inl' c b}:
    sub_inl_size sub inl <= sub_inl_size c b ->
    b_map_le_i inl inl' -> sub_inl_size sub inl' <= sub_inl_size c b.
  Proof.
    etransitivity.
    eapply b_map_le_c in H0.
    eapply sub_size_le.
    apply H0.
    assumption.
  Defined.
  

  Function contractcases (oes: exp * ctx_map * b_map)
           (fcon: r_map -> c_map ->  forall esi:(exp*ctx_map*b_map), (term_sub_inl_size esi < term_sub_inl_size oes)%nat -> shrinkT exp (snd esi))
           (sig:r_map) (count:c_map) (inl:b_map) (sub:ctx_map) (cl:list (var*exp))
           (pfe:subcl_e cl (fst (fst oes)))
           (pfsub: (sub_inl_size sub inl <= sub_inl_size (snd (fst oes)) (snd oes))%nat)
    : shrinkT (list (var * exp)) inl :=
    (match cl as x return x = cl -> _ with
     | [] => fun _ => existT  _ ([], 0, count, inl) (ble_refl inl)
     | (y,e)::cl' =>
       fun Heq_cl =>
         match fcon sig count (e, sub, inl) (subcl_size (eq_ind_r (fun x => subcl_e x _) pfe Heq_cl) pfsub) with
         | existT (e', steps', count', inl') bp =>
           (match contractcases oes fcon sig count' inl' sub cl' (subcl_e_cons_l (eq_ind_r (fun x => subcl_e x _) pfe Heq_cl))
                                (sub_inl_size_compat pfsub bp) with
              existT (cl'', steps'', count'', inl'') bp' =>
              existT _ ((y,e')::cl'', (steps' + steps''), count'', inl'') (b_map_le_i_trans _ _ bp _ bp')
            end)
         end
     end) (eq_refl cl).
  
  (* oe is original expression of form (Efun fds e'), every e on which contract is called is a subterm of oe ( by subterm_fds ) *)  
  Theorem subfds_Fcons {f t ys e fds' e0}:
    subfds_e (Fcons f t ys e fds') e0 ->
    subfds_e fds' e0.
  Proof.
    intro.
    inv H. destructAll. exists x, x0.
    split. assumption.
    eapply subfds_or_eq_left.
    2: apply H0.
    apply subfds_cons.
  Defined.


  Theorem tsis_sub_pcf {sub inl c b e0 f t ys fds' e}:
    sub_inl_size sub inl <= sub_inl_size c b ->
    subfds_e (Fcons f t ys e fds') e0 ->
    term_sub_inl_size (e, sub, inl) < term_sub_inl_size (e0, c, b).
  Proof.
    intros pfsub pfe.
    (program_simpl; simpl in pfsub; simpl in pfe; unfold term_sub_inl_size; simpl; apply subfds_e_size in pfe; simpl in pfe).
    unfold lt. rewrite <- Nat.add_succ_l.
    apply Nat.add_le_mono.
    rewrite <- Nat.add_succ_r in pfe.
    unfold lt in pfe. rewrite <- Nat.add_succ_l in pfe. eapply Nat.le_trans. 2: apply pfe.
    rewrite <- Nat.add_0_r with (n := S (term_size e)) at 1. rewrite Nat.add_comm.
    apply Nat.add_le_mono. apply le_0_n. reflexivity.
    assumption.
  Defined.

  Theorem tsis_sub_pcf' {sub inl c b inl'}:
    sub_inl_size sub inl <= sub_inl_size c b ->
    b_map_le_i inl inl' ->
    sub_inl_size sub inl' <= sub_inl_size c b.
  Proof.
    intros.
    etransitivity.
    eapply sub_size_le. eapply b_map_le_c.
    apply H0.
    assumption.
  Defined.



  Function postcontractfun (oes: exp * ctx_map * b_map)
           (fcon: r_map -> c_map -> forall esi:(exp*ctx_map*b_map), (term_sub_inl_size esi < term_sub_inl_size oes)%nat -> shrinkT exp (snd esi))
           (sig:r_map) (count:c_map) (inl:b_map) (sub:ctx_map) (fds: fundefs)
           (pfe:subfds_e fds (fst (fst oes)))
           (steps : nat)
           (pfsub: (sub_inl_size sub inl <= sub_inl_size (snd (fst oes)) (snd oes))%nat)
    : shrinkT fundefs inl :=
    (match fds  as x return x = fds -> _  with
     | Fnil => fun _ => existT _ (Fnil, steps, count, inl) (ble_refl inl)
     | Fcons f t ys e fds' =>
       fun Heq_fds =>
         (match (get_b f inl) with
          | true =>
            (* DEBUG: might want to verify here that the variable is actually dead *)
            postcontractfun oes fcon sig count inl sub fds' (subfds_Fcons (eq_ind_r (fun x => subfds_e x _) pfe Heq_fds)) (steps + 1) pfsub
          | false =>
            (match (get_c f count) with
             | 0%nat => (* deadF *)
               let count' := dec_census sig e count in
               postcontractfun oes fcon sig count' inl sub fds' (subfds_Fcons (eq_ind_r (fun x => subfds_e x _) pfe Heq_fds)) (steps + 1) pfsub
             | _ =>
               match (fcon sig count (e,sub,inl) (tsis_sub_pcf pfsub (eq_ind_r (fun x => subfds_e x _) pfe Heq_fds))) with
               | existT (e', steps', count', inl') bp =>
                 match postcontractfun oes fcon sig count' inl' sub fds' (subfds_Fcons (eq_ind_r (fun x => subfds_e x _) pfe Heq_fds)) steps
                                       (tsis_sub_pcf' pfsub bp) with
                 | existT (fds'', steps'', count'', inl'') bp' =>
                   existT _ (Fcons f t ys e' fds'', steps' + steps'', count'', inl'') (b_map_le_i_trans _ _ bp _ bp')
                 end
               end
             end)
          end)
     end) (eq_refl fds).



  Theorem subfds_refl:
    forall {e} fds,
      subfds_e fds (Efun fds e).
  Proof.
    intros.
    exists fds, e.
    split.
    apply rt_refl.
    right. reflexivity.
  Defined.

  (* The return type of contractT *)
  Definition contractT im := shrinkT exp im.


  (* TODO move *)
  Fixpoint straight_code (e : exp) : bool :=
    match e with
    | Econstr _ _ _ e 
    | Eproj _ _ _ _ e
    | Eletapp _ _ _ _ e
    | Eprim _ _ _ e
    | Efun _ e => straight_code e
    | Eapp _ _ _
    | Ehalt _ => true
    | Ecase _ _ => false
    end.

  Definition incr_steps {im} (res : contractT im) : contractT im :=
    match res as k return (k = res -> contractT im) with
    | existT (e_body, steps, count, im') bp =>
      fun Heq => existT _ (e_body, steps + 1, count, im') bp
    end (eq_refl _).
  
  Program Fixpoint contract (sig:r_map) (count:c_map) (e:exp) (sub:ctx_map) (im:b_map) {measure (term_sub_inl_size (e,sub,im))}
    : contractT im :=
    match e with
    |  Ehalt v =>
       existT _ (Ehalt (apply_r sig v), 0, count, im) (ble_refl _)
    | Econstr x t ys e' =>
      match (get_c x count) return _ with
      | 0%nat =>
        let count' := dec_census_list sig ys count in
        incr_steps (contract sig count' e' sub im)
      | _ =>
        match contract sig count e' (M.set x (SVconstr t ys) sub) im return _  with
        | existT  (e'', steps', count', im') bp =>
          (match (get_c x count') return _ with
           | 0%nat =>
             let count'' := dec_census_list sig ys count'  in
             existT _ (e'', steps' + 1, count'', im') bp
           | _ =>
             let ys' := apply_r_list sig ys in
             existT _ (Econstr x t ys' e'', steps', count', im') bp
           end)
        end
      end
    | Eproj v t n y e =>
      match (get_c v count) return _ with
      | 0%nat =>
        let count' := dec_census_list sig [y] count in
        incr_steps (contract sig count' e sub im)
      | _ =>
        let y' := apply_r sig y in
        (match (M.get y' sub) return _ with
         | Some (SVconstr t' ys) =>
           (match (nthN ys n) return _ with
            | Some yn =>
              let yn' := apply_r sig yn in
              let count' := M.set y' ((get_c y' count) - 1)%nat count in
              let count'' := M.set v 0%nat (M.set yn' (get_c v count + get_c yn' count)%nat count') in
              incr_steps (contract (M.set v yn' sig) count'' e  sub im)
            | None =>
              match contract sig count e sub im return _  with
              | existT  (e', steps', count', im') bp =>
                (match (get_c v count') return _ with
                 | 0%nat =>
                   let count'' := dec_census_list sig [y] count'  in
                   existT _ (e', steps' + 1, count'', im') bp
                 | _ =>
                   existT _ (Eproj v t n y' e', steps', count', im') bp
                 end)
              end
            end)
         | _ =>
           (match (contract sig count e sub im) return _ with
            | existT  (e', steps', count', im') bp =>
              (match (get_c v count') return _ with
               | 0%nat =>
                 let count'' := dec_census_list sig [y] count'  in
                 existT _ (e', steps' + 1, count'', im') bp
               | _ =>
                 existT _ (Eproj v t n y' e', steps', count', im') bp
               end)
            end)
         end)
      end
    | Eletapp x f t ys e =>
      (* Zoe: I couldn't get the equality proof of the two defs to go through without expanding all the return types
         in this definition which makes this code hard to read *)
      (* Zoe: I couldn't get the equality proof of the two defs to go through without expanding all the return types
         in this definition which makes this code hard to read *)
      match get_c x count as k return (k = get_c x count -> contractT im) with
      | 0%nat =>
        (*  Delete the finding if its not used *)
        fun Heq0_1 =>
          let count' := dec_census_list sig (f::ys) count in
          contract sig count' e sub im
      | _ =>
        fun Heq0_2 => 
          (* If the binding is used then *)
          (* check how many times the function is used *)
          let f' := apply_r sig f in
          let ys' := apply_r_list sig ys in
          let f_no := get_c f' count in
          let f_info := M.get f' sub in          
          (match (f_no, f_info) as k return (k = (f_no, f_info) -> contractT im)  with
           | (1%nat, Some (SVfun t' xs e_body)) =>
             (fun Heq1 =>
                (* need t = t' and |xs| = |ys| (also that f' is not already inlined which is needed for the termination proof) *)
                match ((Pos.eqb t' t) && (Init.Nat.eqb (length ys) (length xs)) && (negb (get_b f' im)) && (straight_code e_body))%bool as k
                      return (k = ((t' =? t)%positive && (length ys =? length xs) && negb (get_b f' im) && (straight_code e_body))%bool -> contractT im)
                with
                | true =>
                  fun Heq2 =>                         
                    let im' := M.set f' true im in
                    (* update counts of ys' and xs after setting f' to 0 *)
                    let count' := update_count_inlined ys' xs (M.set f' 0 count) in
                    let sig' := set_list (combine xs ys') sig in                                      
                    (* first shrink the body *)
                    (match contract sig' count' e_body sub im'
                           as k return (k = contract sig' count' e_body sub im' -> contractT im) with
                     | existT (e_body', steps1, count'', im'') bp =>
                       fun Heqb =>
                         let inl := inline_letapp e_body' x in
                         (match inl as inl' return (inl' = inl -> contractT im) with
                          (* body can be inlined *)
                          | Some (C_inl, x') =>
                            fun Heq3 =>
                              let sig' := M.set x (apply_r sig' x') sig in
                              (match contract sig' count'' e sub im''
                                     as k return (k = contract sig' count'' e sub im'' -> contractT im) with
                               | existT  (e', steps2, count'', im''') bp' =>
                                 fun Heq4 => existT _ (e', steps1 + steps2 + 1, count'', im''')
                                                    (b_map_le_i_trans im (M.set (apply_r sig f) true im) (ble_add im im (apply_r sig f) (ble_refl im))
                                                                      _ (b_map_le_i_trans _ _ bp _ bp'))
                               end (eq_refl _))
                          | None =>
                            (fun Heq5 =>
                               match (contract sig count e sub im) as k return (k = contract sig count e sub im -> contractT im) with
                               | existT  (e', steps, count', im') bp =>
                                 (fun Heq =>
                                    match (get_c x count') as k return (k = get_c x count' -> contractT im) with
                                    | 0%nat =>
                                      fun Heq6 => let count'' := dec_census_list sig (f::ys) count'  in
                                                  existT _ (e', steps + 1, count'', im') bp
                                    | _ =>
                                      fun Heq7 => existT _ (Eletapp x f' t ys' e', steps, count', im') bp
                                    end (eq_refl _))
                               end (eq_refl _))
                          end (eq_refl _))
                     end (eq_refl _))
                | false =>
                  (fun Heq5 =>
                     match (contract sig count e sub im) as k return (k = contract sig count e sub im -> contractT im) with
                     | existT  (e', steps, count', im') bp =>
                       (fun Heq =>
                          match (get_c x count') as k return (k = get_c x count' -> contractT im) with
                          | 0%nat =>
                            fun Heq6 => let count'' := dec_census_list sig (f::ys) count'  in
                                        existT _ (e', steps + 1, count'', im') bp
                          | _ =>
                            fun Heq7 => existT _ (Eletapp x f' t ys' e', steps, count', im') bp
                          end (eq_refl _))
                     end (eq_refl _))                    
                end (eq_refl _))
           | _ =>
             (fun Heq7 =>
                match (contract sig count e sub im) as k return (k = contract sig count e sub im -> contractT im) with
                | existT  (e', steps, count', im') bp =>
                  (fun Heq =>
                     match (get_c x count') as k return (k = get_c x count' -> contractT im) with
                     | 0%nat =>
                       fun Heq6 => let count'' := dec_census_list sig (f::ys) count'  in
                                   existT _ (e', steps + 1, count'', im') bp
                     | _ =>
                       fun Heq7 => existT _ (Eletapp x f' t ys' e', steps, count', im') bp
                     end (eq_refl _))
                end (eq_refl _))
           end (eq_refl _))
      end (eq_refl _)
    | Eprim x f ys e =>
      match (get_c x count) return _ with
      | 0%nat =>
        let count' := dec_census_list sig ys count in
        incr_steps (contract sig count' e sub im)
      | _ =>
        (match contract sig count e sub im return _ with
         | existT   (e', steps', count', im') bp  =>
           (match (get_c x count') return _ with
            | 0%nat =>
              let count'' := dec_census_list sig ys count'  in
              existT _ (e', steps' + 1, count'', im') bp
            | _ =>
              let ys' := apply_r_list sig ys in
              existT _ (Eprim x f ys' e', steps', count', im') bp
            end)
         end)
      end
    | Ecase v cl =>
      let v' := apply_r sig v in
      (match (M.get v' sub) return _ with
       | Some (SVconstr t lv) =>
         (match findtag cl t with
          | Some k =>
            (* decrease count of each (sig e') other than k *)
            incr_steps (contract sig (dec_census_case sig cl t (dec_census_list sig [v] count)) k  sub im)
          | None =>
            (* fold over case body *)
            (match contractcases (Ecase v cl, sub, im)
                                 (fun rm cm es H => contract rm cm (fst (fst es)) (snd (fst es)) (snd es)) sig count im sub cl (subcl_refl cl) (le_n _)  with
             | existT  (cl', steps', count', im') bp =>
               existT _ (Ecase v' cl', steps', count', im') bp
             end)
          end)
       | _ =>
         (match contractcases (Ecase v cl, sub, im)
                              (fun rm cm es H => contract rm cm (fst (fst es)) (snd (fst es)) (snd es)) sig count im sub cl (subcl_refl cl) (le_n _) with
          | existT (cl', steps', count', im') bp  =>

            existT _ (Ecase v' cl', steps', count', im') bp
          end)
       end )
    | Efun fl e =>
      (match  precontractfun sig count sub fl 0 with
       | (fl', steps', count', sub') =>
         (match contract sig count' e sub' im return _ with
            existT (e', steps'', count'', im') bp =>
            match postcontractfun (Efun fl' e, sub, im')
                                  (fun rm cm es H => contract rm cm (fst (fst es)) (snd (fst es)) (snd es)) sig count''
                                  im' sub fl' (subfds_refl fl') 0 (le_n _) return _ with
            | existT (fl'', steps''', count''', im'') bp' =>
              (match fl'' return _ with (* eliminate empty function defns. *)
               | Fnil => existT _ ( e', steps' + steps'' + steps''' + 1, count''', im'') (b_map_le_i_trans _ _ bp _ bp')
               |  _  =>  existT _ (Efun fl'' e', steps' + steps'' + steps''', count''', im'') (b_map_le_i_trans _ _ bp _ bp')
               end)
            end
          end)
       end)

    | Eapp f t ys =>
      let f' := apply_r sig f in
      let ys' := apply_r_list sig ys in
      (match get_c f' count with
       | 1%nat => (match (M.get f' sub) with
                   | Some (SVfun t' xs m)  =>
                     (* need t = t' and |xs| = |ys| (also that f' is not already inlined which is needed for the termination proof) *)
                     (match (andb (Pos.eqb t' t) (andb (Init.Nat.eqb (length ys) (length xs)) (negb (get_b f' im))))
                      with
                      | true =>
                        let im' := M.set f' true im in
                        (* update counts of ys' and xs after setting f' to 0 *)
                        let count' := update_count_inlined ys' xs (M.set f' 0 count) in
                        (match contract (set_list (combine xs ys') sig) count' m  sub im' return _ with
                         | existT (e, steps', c, i) bp => existT _ (e, steps' + 1, c, i) (b_map_i_true _ _ _ bp)
                         end)
                      | false =>
                        existT _ (Eapp f' t ys', 0, count, im) (ble_refl im)
                      end)
                   | _ => existT _ (Eapp f' t ys', 0, count, im) (ble_refl im)
                   end)
       | _ => existT _ (Eapp f' t ys', 0, count, im) (ble_refl im)
       end)
    end. 
  Solve Obligations with (program_simpl; unfold term_sub_inl_size; simpl;  rewrite <- Nat.add_succ_r;  rewrite <- Nat.add_lt_mono_l;  eapply Nat.le_lt_trans; [apply sub_set_size | (simpl; unfold lt; reflexivity)]).
  Next Obligation.
    unfold term_sub_inl_size in *; simpl in *. 
    assert (term_size k < term_size (Ecase v cl))%nat.
    symmetry in Heq_anonymous.
    apply findtag_In_patterns in Heq_anonymous.
    eapply case_size; eauto.
    simpl in H.
    rewrite <- Nat.add_succ_l.
    apply Nat.add_lt_mono_r. assumption.
  Defined.
  Next Obligation.
    assert ((forall im, sub_inl_size sub' im <= funs_size (fl) + sub_inl_size sub im /\ funs_size fl' <= funs_size fl))%nat. eapply precontractfun_size. eauto.  unfold term_sub_inl_size. simpl. specialize (H im). apply le_lt_n_Sm. destruct H.
    rewrite Nat.add_comm with (n := funs_size fl).
    rewrite <- Nat.add_assoc.
    apply Nat.add_le_mono. reflexivity. apply H.
  Defined.
  Next Obligation.
    unfold term_sub_inl_size; simpl.
    unfold term_sub_inl_size in H. simpl in H.
    assert (Heq0 := Heq_anonymous).
    eapply precontractfun_size with ( im := b) in Heq0.
    assert (sub_inl_size sub im' <= sub_inl_size sub im).
    apply sub_size_le.
    apply b_map_le_c; auto.
    eapply Nat.lt_le_trans. apply H.
    destruct Heq0.
    apply le_n_S.
    rewrite <- Nat.add_assoc.
    rewrite <- Nat.add_assoc.
    rewrite Nat.add_comm.
    rewrite Nat.add_comm with (n := funs_size fl).
    do 2 (rewrite <- Nat.add_assoc).
    apply Nat.add_le_mono. reflexivity.
    apply Nat.add_le_mono; assumption.
  Defined.
  Next Obligation.
    unfold term_sub_inl_size; simpl.
    symmetry in Heq_anonymous1.
    apply sub_inl_fun_size with (im :=  im) in Heq_anonymous1.
    rewrite Nat.add_comm.
    rewrite <- Heq_anonymous1. auto.
    symmetry in Heq_anonymous.
    apply Bool.andb_true_iff in Heq_anonymous.
    destructAll.
    apply Bool.andb_true_iff in H0.
    destructAll.
    apply Bool.negb_true_iff. auto.
  Defined. 
  Next Obligation.
    unfold term_sub_inl_size; simpl in *.
    rewrite plus_comm. erewrite <- sub_inl_fun_size; eauto. omega.   
    symmetry in Heq2.
    apply Bool.andb_true_iff in Heq2.
    destructAll.
    apply Bool.andb_true_iff in H0.
    destructAll.
    apply Bool.negb_true_iff. auto.
  Defined.
  Next Obligation.
    simpl in *. destruct Heqb.
    unfold term_sub_inl_size; simpl.
    eapply le_trans. eapply le_n_S.
    eapply plus_le_compat_l. eapply sub_inl_size_compat; [| eapply bp  ].
    reflexivity. eapply le_n_S.
    eapply plus_le_compat_l. inv Heq1.
    erewrite sub_inl_fun_size with (im := im); eauto. omega.   
    symmetry in Heq2. apply Bool.andb_true_iff in Heq2.
    destructAll.
    apply Bool.andb_true_iff in H4.
    destructAll.
    apply Bool.negb_true_iff. auto.
  Defined.
 
  

  Definition contract_def (sig:r_map) (count:c_map) (e:exp) (sub:ctx_map) (im:b_map): contractT im  :=
    match e with
    |  Ehalt v =>
       existT _ (Ehalt (apply_r sig v), 0, count, im) ( ble_refl _)
    | Econstr x t ys e' =>
      match (get_c x count) with
      | 0%nat =>
        let count' := dec_census_list sig ys count in
        incr_steps (contract sig count' e' sub im)
      | _ =>
        match contract sig count e' (M.set x (SVconstr t ys) sub) im  with
        | existT  (e'', steps, count', im') bp =>
          (match (get_c x count') with
           | 0%nat =>
             let count'' := dec_census_list sig ys count'  in
             existT _ (e'', steps + 1, count'', im') bp
           | _ =>
             let ys' := apply_r_list sig ys in
             existT _ (Econstr x t ys' e'', steps, count', im') bp
           end)
        end
      end
    | Eproj v t n y e =>
      match (get_c v count) with
      | 0%nat =>
        let count' := dec_census_list sig [y] count in
        incr_steps (contract sig count' e sub im)
      | _ =>
        let y' := apply_r sig y in
        (match (M.get y' sub) with
         | Some (SVconstr t' ys) =>
           (match (nthN ys n) with
            | Some yn =>
              let yn' := apply_r sig yn in
              let count' := M.set y' ((get_c y' count) - 1)%nat count in
              let count'' := M.set v 0%nat (M.set yn' (get_c v count + get_c yn' count)%nat count') in
              incr_steps (contract (M.set v yn' sig) count'' e  sub im)
            | None =>
              match contract sig count e sub im  with
              | existT  (e', steps, count', im') bp =>
                (match (get_c v count') with
                 | 0%nat =>
                   let count'' := dec_census_list sig [y] count'  in
                   existT _ (e', steps + 1, count'', im') bp
                 | _ =>
                   existT _ (Eproj v t n y' e', steps, count', im') bp
                 end)
              end
            end)
         | _ =>
           (match (contract sig count e sub im) with
            | existT  (e', steps, count', im') bp =>
              (match (get_c v count') with
               | 0%nat =>
                 let count'' := dec_census_list sig [y] count'  in
                 existT _ (e', steps + 1, count'', im') bp
               | _ =>
                 existT _ (Eproj v t n y' e', steps, count', im') bp
               end)
            end)
         end)
      end
    | Eletapp x f t ys e =>
      (* Zoe: I couldn't get the equality proof of the two defs to go through without expanding all the return types
         in this definition which makes this code hard to read *)
      match get_c x count as k return (k = get_c x count -> contractT im) with
      | 0%nat =>
        (*  Delete the finding if its not used *)
        fun Heq0_1 =>
          let count' := dec_census_list sig (f::ys) count in
          contract sig count' e sub im
      | _ =>
        fun Heq0_2 => 
          (* If the binding is used then *)
          (* check how many times the function is used *)
          let f' := apply_r sig f in
          let ys' := apply_r_list sig ys in
          let f_no := get_c f' count in
          let f_info := M.get f' sub in          
          (match (f_no, f_info) as k return (k = (f_no, f_info) -> contractT im)  with
           | (1%nat, Some (SVfun t' xs e_body)) =>
             (fun Heq1 =>
                (* need t = t' and |xs| = |ys| (also that f' is not already inlined which is needed for the termination proof) *)
                match ((Pos.eqb t' t) && (Init.Nat.eqb (length ys) (length xs)) && (negb (get_b f' im)) && (straight_code e_body))%bool as k
                      return (k = ((t' =? t)%positive && (length ys =? length xs) && negb (get_b f' im) && (straight_code e_body))%bool -> contractT im)
                with
                | true =>
                  fun Heq2 =>                         
                    let im' := M.set f' true im in
                    (* update counts of ys' and xs after setting f' to 0 *)
                    let count' := update_count_inlined ys' xs (M.set f' 0 count) in
                    let sig' := set_list (combine xs ys') sig in                                      
                    (* first shrink the body *)
                    (match contract sig' count' e_body sub im'
                           as k return (k = contract sig' count' e_body sub im' -> contractT im) with
                     | existT (e_body', steps1, count'', im'') bp =>
                       fun Heqb =>
                         let inl := inline_letapp e_body' x in
                         (match inl as inl' return (inl' = inl -> contractT im) with
                          (* body can be inlined *)
                          | Some (C_inl, x') =>
                            fun Heq3 =>
                              let sig' := M.set x (apply_r sig' x') sig in
                              (match contract sig' count'' e sub im''
                                     as k return (k = contract sig' count'' e sub im'' -> contractT im) with
                               | existT  (e', steps2, count'', im''') bp' =>
                                 fun Heq4 => existT _ (e', steps1 + steps2 + 1, count'', im''')
                                                    (b_map_le_i_trans im (M.set (apply_r sig f) true im) (ble_add im im (apply_r sig f) (ble_refl im))
                                                                      _ (b_map_le_i_trans _ _ bp _ bp'))
                               end (eq_refl _))
                          | None =>
                            (fun Heq5 =>
                               match (contract sig count e sub im) as k return (k = contract sig count e sub im -> contractT im) with
                               | existT  (e', steps, count', im') bp =>
                                 (fun Heq =>
                                    match (get_c x count') as k return (k = get_c x count' -> contractT im) with
                                    | 0%nat =>
                                      fun Heq6 => let count'' := dec_census_list sig (f::ys) count'  in
                                                  existT _ (e', steps + 1, count'', im') bp
                                    | _ =>
                                      fun Heq7 => existT _ (Eletapp x f' t ys' e', steps, count', im') bp
                                    end (eq_refl _))
                               end (eq_refl _))
                          end (eq_refl _))
                     end (eq_refl _))
                | false =>
                  (fun Heq5 =>
                     match (contract sig count e sub im) as k return (k = contract sig count e sub im -> contractT im) with
                     | existT  (e', steps, count', im') bp =>
                       (fun Heq =>
                          match (get_c x count') as k return (k = get_c x count' -> contractT im) with
                          | 0%nat =>
                            fun Heq6 => let count'' := dec_census_list sig (f::ys) count'  in
                                        existT _ (e', steps + 1, count'', im') bp
                          | _ =>
                            fun Heq7 => existT _ (Eletapp x f' t ys' e', steps, count', im') bp
                          end (eq_refl _))
                     end (eq_refl _))                    
                end (eq_refl _))
           | _ =>
             (fun Heq7 =>
                match (contract sig count e sub im) as k return (k = contract sig count e sub im -> contractT im) with
                | existT  (e', steps, count', im') bp =>
                  (fun Heq =>
                     match (get_c x count') as k return (k = get_c x count' -> contractT im) with
                     | 0%nat =>
                       fun Heq6 => let count'' := dec_census_list sig (f::ys) count'  in
                                   existT _ (e', steps + 1, count'', im') bp
                     | _ =>
                       fun Heq7 => existT _ (Eletapp x f' t ys' e', steps, count', im') bp
                     end (eq_refl _))
                end (eq_refl _))
           end (eq_refl _))
      end (eq_refl _)
    | Eprim x f ys e=>
      match (get_c x count) with
      | 0%nat =>
        let count' := dec_census_list sig ys count in
        incr_steps (contract sig count' e sub im)
      | _ =>
        (match contract sig count e sub im with
         | existT   (e', steps, count', im') bp  =>
           (match (get_c x count') with
            | 0%nat =>
              let count'' := dec_census_list sig ys count'  in
              existT _ (e', steps + 1, count'', im') bp
            | _ =>
              let ys' := apply_r_list sig ys in
              existT _ (Eprim x f ys' e', steps, count', im') bp
            end)
         end)
      end
    | Ecase v cl =>
      let v' := apply_r sig v in
      (match (M.get v' sub) with
       | Some (SVconstr t lv) =>
         (match findtag cl t  as anonymous'
                return (anonymous' = findtag cl t -> contractT im) with
          | Some k =>
            fun Heq_ft =>
              (* decrease count of each (sig e') other than k *)
              incr_steps (contract sig (dec_census_case sig cl t (dec_census_list sig [v] count)) k  sub im)
          | None =>
            fun _ =>
              (* fold over case body *)
              (match contractcases (Ecase v cl, sub, im)
                                   (fun rm cm es H => contract rm cm (fst (fst es)) (snd (fst es)) (snd es)) sig count im sub cl (subcl_refl cl) (le_n _)
                     as anonymous'
                     return
                     (anonymous' = contractcases (Ecase v cl, sub, im)
                                                 (fun rm cm es H => contract rm cm (fst (fst es)) (snd (fst es)) (snd es)) sig count im sub cl (subcl_refl cl) (le_n _) -> contractT im)
               with
               | existT  (cl', steps, count', im') bp =>
                 fun Heqc => existT _ (Ecase v' cl', steps, count', im') bp
               end) (eq_refl _)
          end) (eq_refl _)
       | _ =>
         (match contractcases (Ecase v cl, sub, im)
                              (fun rm cm es H => contract rm cm (fst (fst es)) (snd (fst es)) (snd es)) sig count im sub cl (subcl_refl cl) (le_n _) as anonymous'
                return
                (anonymous' = contractcases (Ecase v cl, sub, im)
                                            (fun rm cm es H => contract rm cm (fst (fst es)) (snd (fst es)) (snd es)) sig count im sub cl (subcl_refl cl) (le_n _) -> contractT im)
          with
          | existT (cl', steps, count', im') bp  =>
            fun Heqc =>
              existT _ (Ecase v' cl', steps, count', im') bp
          end) (eq_refl _)
       end )
    | Efun fl e =>
      (match  precontractfun sig count sub fl 0 as anonymous'
              return
              (anonymous' = precontractfun sig count sub fl 0 -> contractT im) with
       | (fl', steps1, count', sub') =>
         fun Heq =>
           (match contract sig count' e sub' im with
              existT (e', steps2, count'', im') bp =>
              match postcontractfun (Efun fl' e, sub, im')
                                    (fun rm cm es H => contract rm cm (fst (fst es)) (snd (fst es)) (snd es)) sig count''
                                    im' sub fl' (subfds_refl fl') 0 (le_n _) with
              | existT (fl'', steps3, count''', im'') bp' =>
                (match fl'' return contractT im with (* eliminate empty function defns. *)
                 | Fnil => existT _ (e', steps1 + steps2 + steps3 + 1, count''', im'') (b_map_le_i_trans _ _ bp _ bp')
                 |  _  =>  existT _ (Efun fl'' e', steps1 + steps2 + steps3, count''', im'') (b_map_le_i_trans _ _ bp _ bp')
                 end)
              end
            end)
       end) (eq_refl _)

    | Eapp f t ys =>
      let f' := apply_r sig f in
      let ys' := apply_r_list sig ys in
      (match get_c f' count as anonymous' return
             (anonymous' = get_c f' count -> contractT im) with
       | 1%nat =>
         fun Heq_f' =>
           (match (M.get f' sub) as anonymous'
                  return
                  (anonymous' = M.get f' sub -> contractT im)
            with
            | Some (SVfun t' xs m)  =>
              fun Heqs =>
                (* need t = t' and |xs| = |ys| (also that f' is not already inlined which is needed for the termination proof) *)
                (match (andb (Pos.eqb t' t) (andb (Init.Nat.eqb (length ys) (length xs)) (negb (get_b f' im)))) as
                       anonymous'
                       return
                       (anonymous' =
                        ((t' =? t)%positive &&
                         ((length ys =? length xs) && negb (get_b f' im)))%bool -> contractT im)
                 with
                 | true =>
                   fun Heqm =>
                     let im' := M.set f' true im in
                     (* update counts of ys' and xs after setting f' to 0 *)
                     let count' := update_count_inlined ys' xs (M.set f' 0 count) in
                     (match contract (set_list (combine xs ys') sig) count' m  sub im' with
                      | existT (e, steps, c, i) bp => existT _ (e, steps + 1, c, i) (b_map_i_true _ _ _ bp)
                      end)
                 | false =>
                   fun Heqm =>
                     existT _ (Eapp f' t ys', 0, count, im) (ble_refl im)
                 end) (eq_refl _)
            | _ => fun Heqs => existT _ (Eapp f' t ys', 0, count, im) (ble_refl im)
            end) (eq_refl _)
       | _ => fun _ => existT _ (Eapp f' t ys', 0, count, im) (ble_refl im)
       end) (eq_refl _)
    end.


  Arguments contract:simpl never.
  Obligation Tactic := program_simplify ; auto with *.
  
  Definition hide_body {A} {a : A} := a.
  

  Theorem contract_eq:
    forall e sub im sig count,
      contract sig count e sub im  =
      contract_def sig count e sub im.
  Proof.
    intros.
    unfold contract. unfold contract_func.
    match goal with
      |- context C [@Fix_sub ?A ?R ?wf ?P ?f ?a] =>
      set (body := hide_body (a:=f)) in |-;
                                          let newg := context C [ @Fix_sub A R wf P body a ] in convert_concl_no_check newg
    end.
    WfExtensionality.unfold_sub contract (contract sig count e sub im).
    destruct e; lazy [projT1 projT2 fst snd];
      try (unfold contract_def; unfold contract; unfold contract_func;
           lazy [projT1 projT2 fst snd]; reflexivity).
  Qed.


End CONTRACT.

(* Perform 1 pass of contract of e *)
Definition shrink_top (e:exp) : exp :=
  let count := init_census e in
  match (contract (M.empty var) count e (M.empty svalue) (M.empty bool)) with
  | existT (e', _, _, _) _ => e'
  end.

(* Perform n passes of contract of e starting with count map c *)
Fixpoint shrink_n_times' (e:exp) (c:c_map) (n:nat): (exp * c_map) :=
  match n with
  | 0 => (e, c)
  | (S n') =>
    match (contract (M.empty var) c e (M.empty svalue) (M.empty bool)) with
    | existT (e', _, c', _) _ => shrink_n_times' e' c' n'
    end
  end.

(* Perform n passes of contract of e *)
Definition shrink_n_times (e:exp) (n:nat): exp :=
  let count := init_census e in
  let (e, _) := shrink_n_times' e count n in
  e.

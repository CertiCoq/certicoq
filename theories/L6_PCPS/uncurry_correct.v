Require Import L6.cps L6.size_cps L6.cps_util L6.eval L6.logical_relations L6.set_util L6.identifiers L6.ctx
        L6.hoare L6.Ensembles_util L6.List_util L6.alpha_conv L6.functions L6.uncurry
        L6.shrink_cps_correct.
Require Import FunInd.
Require Import closure_conversion_corresp. (* for [fresh] *)
Require Import Coq.ZArith.Znumtheory Coq.Relations.Relations Coq.Arith.Wf_nat.
Require Import Coq.Lists.List Coq.MSets.MSets Coq.MSets.MSetRBT Coq.Numbers.BinNums
        Coq.NArith.BinNat Coq.PArith.BinPos Coq.Sets.Ensembles Omega.
Require Import ExtLib.Structures.Monads ExtLib.Data.Monads.StateMonad.

Import ListNotations MonadNotation.

Section list_lemmas.
  Lemma setlist_length : forall {A} (l : list M.elt) (l1 : list A) (rho rho1 : M.t A),
    Some rho1 = setlist l l1 rho -> length l = length l1.
  Proof.
    induction l; intros.
    - (* [] *) destruct l1; [easy|now simpl in H].
    - (* :: *) destruct l1; [now simpl in H|].
      simpl. apply f_equal.
      remember (setlist l l1 rho).
      destruct o.
      + eapply IHl. simpl in H. eapply Heqo.
      + simpl in H. now rewrite <- Heqo in H.
  Qed.

  Lemma exists_setlist_iff_length : forall {A} (l : list M.elt) (l1 : list A) (rho : M.t A),
    (exists rho1, Some rho1 = setlist l l1 rho) <-> length l = length l1.
  Proof.
    induction l; split; intros.
    - (* [] -> *) destruct H. destruct l1; [easy|now simpl in H].
    - (* [] <- *) destruct l1; [now exists rho|easy].
    - (* :: -> *) destruct H. destruct l1; [now simpl in H|].
      simpl. apply f_equal.
      simpl in H. remember (setlist l l1 rho).
      destruct o; [|congruence].
      rewrite <- IHl with (rho := rho). now exists t. 
    - (* :: <- *) destruct l1; [easy|]. simpl in H. apply Nat.succ_inj in H.
      rewrite <- IHl with (rho := rho) in H. destruct H.
      simpl. rewrite <- H. now exists (M.set a a0 x).
  Qed.

  Corollary exists_setlist_length : forall {A} (l : list M.elt) (l1 : list A) (rho : M.t A),
    (exists rho1, Some rho1 = setlist l l1 rho) -> length l = length l1.
  Proof. intros; now rewrite <- exists_setlist_iff_length with (rho0 := rho). Qed.

  Corollary length_exists_setlist : forall {A} (l : list M.elt) (l1 : list A) (rho : M.t A),
     length l = length l1 -> (exists rho1, Some rho1 = setlist l l1 rho).
  Proof. intros; now rewrite exists_setlist_iff_length with (rho0 := rho). Qed.

  (* nesting setlists (TODO: move to cps.v?) *)
  Lemma setlist_setlist : forall {A} (l l1 : list M.elt) (v v1 : list A) (rho rho1 rho2 : M.t A),
    Some rho1 = setlist l v rho ->
    Some rho2 = setlist l1 v1 rho1 ->
    Some rho2 = setlist (l1 ++ l) (v1 ++ v) rho.
  Proof.
    induction l1.
    - (* [] *)
      intros. assert (v1 = []) by (apply setlist_length in H0; now destruct v1). subst.
      inversion H0. now subst.
    - (* :: *)
      intros. destruct v1; [apply setlist_length in H0; inversion H0|].
      simpl in *. remember (setlist l1 v1 rho1). destruct o; [|congruence].
      now rewrite <- (IHl1 _ _ _ _ _ H Heqo).
  Qed.

  (* expose an M.set from a successful setlist *)
  Lemma set_setlist : forall {A} h h1 (t : list M.elt) (t1 : list A) (rho rho2 : M.t A),
    Some rho2 = setlist (h :: t) (h1 :: t1) rho -> exists rho1,
    rho2 = M.set h h1 rho1 /\ Some rho1 = setlist t t1 rho.
  Proof.
    simpl. intros. remember (setlist t t1 rho). destruct o; [|congruence].
    inversion H. inversion H. subst. eauto.
  Qed.

  Lemma setlist_set : forall {A} a b (l : list M.elt) (v : list A) (rho : M.t A),
    setlist l v (M.set a b rho) = setlist (l ++ [a]) (v ++ [b]) rho.
  Proof.
    induction l; intros.
    - (* [] *) destruct v; [easy|destruct v; easy].
    - (* :: *) destruct v. simpl.
      assert (setlist (l ++ [a]) [] rho = None) by (now destruct l). now rewrite H.
      simpl in *.
      remember (setlist l v (M.set a b rho)).
      remember (setlist (l ++ [a]) (v ++ [b]) rho).
      destruct o, o0; [| | |auto].
      + rewrite <- IHl in Heqo0. rewrite <- Heqo in Heqo0. inversion Heqo0; now subst.
      + apply setlist_length in Heqo.
        assert (length (l ++ [a]) = length (v ++ [b]))
          by (repeat rewrite app_length; now rewrite Heqo).
        apply length_exists_setlist with (rho0 := rho) in H. destruct H. congruence.
      + assert (length l = length v). {
          apply setlist_length in Heqo0. 
          repeat rewrite app_length in Heqo0. simpl in Heqo0. omega.
        }
        apply length_exists_setlist with (rho0 := (M.set a b rho)) in H. destruct H. congruence.
  Qed.

  Lemma list_length_cons : forall {A} {B} h (l : list A) (t : list B),
    length l = length (h :: t) -> exists h1 t1, l = h1 :: t1.
  Proof. intros. destruct l; [easy|now exists a, l]. Qed.

  Lemma list_length_snoc : forall {A} {B} (l : list A) (a : list B) b,
    length l = length (a ++ [b]) -> exists a1 b1, l = a1 ++ [b1].
  Proof.
    induction l; intros.
    - rewrite app_length in H. inversion H. rewrite plus_comm in H1. inversion H1.
    - destruct a0.
      + assert (l = []) by (destruct l; [easy|inversion H]). subst.
        now exists [], a.
      + inversion H. destruct (IHl _ _ H1) as [a1 [b1 Hab1]].
        exists (a :: a1), b1. simpl. now apply f_equal.
  Qed.

  Lemma setlist_fresh : forall {A} v1 v v2 w1 w w2 (rho rho1 : M.t A),
    length v1 = length w1 ->
    ~ List.In v v1 ->
    Some rho1 = setlist (v1 ++ [v] ++ v2) (w1 ++ [w] ++ w2) rho ->
    M.get v rho1 = Some w.
  Proof.
    induction v1.
    - intros. assert (w1 = []) by (destruct w1; easy; inversion H). subst.
      simpl in H1. remember (setlist v2 w2 rho).
      destruct o; [|congruence]. inversion H1. now rewrite M.gss.
    - intros. symmetry in H.
      destruct (list_length_cons _ _ _ H) as [w1h [w1t Hw1]]. subst.
      inversion H.
      simpl in H1. remember (setlist (v1 ++ v :: v2) (w1t ++ w :: w2) rho).
      destruct o; [|congruence]. inversion H1; subst.
      rewrite not_in_cons in H0. destruct H0.
      rewrite M.gso; [|assumption].
      eapply IHv1; [symmetry; eassumption|assumption|simpl; eassumption].
  Qed.

  Lemma getlist_setlist_app : forall {A} v v1 w w1 (rho rho1 : M.t A),
    length v = length w ->
    NoDup v ->
    Some rho1 = setlist (v ++ v1) (w ++ w1) rho ->
    getlist v rho1 = Some w.
  Proof.
    induction v; intros.
    - assert (w = []) by (destruct w; easy; inversion H). now subst.
    - inversion H0; subst. destruct w; [inversion H|].
      simpl in H1. remember (setlist (v ++ v1) (w ++ w1) rho).
      destruct o; [|congruence]. inversion H1; subst.
      simpl. rewrite getlist_set_neq; [|assumption].
      erewrite IHv; [now rewrite M.gss|now inversion H|assumption|eassumption].
  Qed.

  Lemma Disjoint_FromList_cons_right : forall {A} (a : list A) h t,
    Disjoint _ (FromList a) (FromList (h :: t)) ->
    Disjoint _ (FromList a) (FromList t).
  Proof.
    intros. constructor. intros x contra.
    inv contra. inv H.
    contradiction (H2 x).
    constructor; [|right]; assumption.
  Qed.

  Lemma getlist_setlist_disjoint_app : forall {A} u v w v1 w1 (rho rho1 : M.t A),
    Disjoint _ (FromList u) (FromList v) ->
    length v = length w ->
    Some rho1 = setlist (v ++ v1) (w ++ w1) rho ->
    exists rho2, Some rho2 = setlist v1 w1 rho /\ getlist u rho1 = getlist u rho2.
  Proof.
    induction v; intros.
    - assert (w = []) by (destruct w; easy; inversion H). subst. now exists rho1.
    - destruct w; inversion H0.
      simpl in H1. remember (setlist (v ++ v1) (w ++ w1) rho).
      destruct o; [inversion H1; subst|congruence].
      replace (getlist u (M.set a a0 t)) with (getlist u t).
      eapply IHv; [|eassumption|assumption].
      eapply Disjoint_FromList_cons_right. eassumption.
      symmetry. apply getlist_set_neq.
      intros contra. inversion H. contradiction (H2 a).
      split; [assumption|now left].
  Qed.

  Lemma list_in_iff_Included : forall {A} a (l : list A),
    List.In a l <-> In _ (FromList l) a.
  Proof. split; intros; auto. Qed.

  Lemma not_list_in_app : forall {A} a (l r : list A),
    ~ List.In a (l ++ r) <-> ~ List.In a l /\ ~ List.In a r.
  Proof.
    split; intros.
    - induction l. split; [auto|]. assumption.
      apply not_in_cons in H. destruct H.
      destruct (IHl H0) as [H1 H2].
      split; [|assumption].
      intros [HL|HR]; congruence.
    - destruct H. induction l. simpl. assumption.
      apply not_in_cons in H. destruct H.
      simpl. intros [HL|HR]; [congruence|now apply IHl in H1].
  Qed.
End list_lemmas.

Section uncurry_correct.
  Lemma Fcons_eq_v_eq : forall {f t v e fds f1 t1 v1 e1 fds1},
    Fcons f t v e fds = Fcons f1 t1 v1 e1 fds1 -> v = v1.
  Proof. now inversion 1. Qed.
  Lemma Fcons_eq_e_eq : forall {f t v e fds f1 t1 v1 e1 fds1},
    Fcons f t v e fds = Fcons f1 t1 v1 e1 fds1 -> e = e1.
  Proof. now inversion 1. Qed.
  Lemma Fcons_eq_fds_eq : forall {f t v e fds f1 t1 v1 e1 fds1},
    Fcons f t v e fds = Fcons f1 t1 v1 e1 fds1 -> fds = fds1.
  Proof. now inversion 1. Qed.
  Lemma Efun_eq_fds_eq : forall {fds e fds1 e1}, Efun fds e = Efun fds1 e1 -> fds = fds1.
  Proof. now inversion 1. Qed.
  Lemma Efun_eq_e_eq : forall {fds e fds1 e1}, Efun fds e = Efun fds1 e1 -> e = e1.
  Proof. now inversion 1. Qed.
  Lemma Eapp_eq_xs_eq : forall {x f xs x1 f1 xs1}, Eapp x f xs = Eapp x1 f1 xs1 -> xs = xs1.
  Proof. now inversion 1. Qed.
  Lemma Fcons_neq_Fnil : forall {f t v e fds}, Fcons f t v e fds <> Fnil.
  Proof. now inversion 1. Qed.
  Lemma Econstr_neq_Efun : forall {x c vs e e1 fds1}, Econstr x c vs e <> Efun fds1 e1.
  Proof. now inversion 1. Qed.
  Lemma Ecase_neq_Efun : forall {v l e1 fds1}, Ecase v l <> Efun fds1 e1.
  Proof. now inversion 1. Qed.
  Lemma Eproj_neq_Efun : forall {x c n y e e1 fds1}, Eproj x c n y e <> Efun fds1 e1.
  Proof. now inversion 1. Qed.
  Lemma Eapp_neq_Efun : forall {x f xs e1 fds1}, Eapp x f xs <> Efun fds1 e1.
  Proof. now inversion 1. Qed.
  Lemma Eprim_neq_Efun : forall {x p xs e e1 fds1}, Eprim x p xs e <> Efun fds1 e1.
  Proof. now inversion 1. Qed.
  Lemma Ehalt_neq_Efun : forall {x e1 fds1}, Ehalt x <> Efun fds1 e1.
  Proof. now inversion 1. Qed.
  Lemma Econstr_neq_Eapp : forall {x c vs e x1 f1 xs1}, Econstr x c vs e <> Eapp x1 f1 xs1.
  Proof. now inversion 1. Qed.
  Lemma Ecase_neq_Eapp : forall {v l x1 f1 xs1}, Ecase v l <> Eapp x1 f1 xs1.
  Proof. now inversion 1. Qed.
  Lemma Eproj_neq_Eapp : forall {x c n y e x1 f1 xs1}, Eproj x c n y e <> Eapp x1 f1 xs1.
  Proof. now inversion 1. Qed.
  Lemma Eprim_neq_Eapp : forall {x p xs e x1 f1 xs1}, Eprim x p xs e <> Eapp x1 f1 xs1.
  Proof. now inversion 1. Qed.
  Lemma Efun_neq_Eapp : forall {fds e x1 f1 xs1}, Efun fds e <> Eapp x1 f1 xs1.
  Proof. now inversion 1. Qed.
  Lemma Ehalt_neq_Eapp : forall {x x1 f1 xs1}, Ehalt x <> Eapp x1 f1 xs1.
  Proof. now inversion 1. Qed.
  Lemma cons_cons_neq_cons : forall {A : Type} {a b c : A} {t}, a :: b :: t <> [c].
  Proof. now inversion 1. Qed.

  (* need a stronger definition of size to prove that the functional
     induction scheme is well-founded *)
  Fixpoint sizeof_exp e : nat :=
    match e with
      (Econstr x _ ys e) => 1 + length ys + sizeof_exp e
    | (Ecase x l) =>
      1 + (fix sizeof_l l :=
              match l with
                [] => 0
              | (t, e) :: l => 1 + sizeof_exp e + sizeof_l l
              end) l
    | (Eproj x _ _ y e) => 1 + sizeof_exp e
    | (Efun fds e) => 1 + sizeof_fundefs fds + sizeof_exp e
    | (Eapp x _ ys) => 1 + length ys
    | (Eprim x _ ys e) => 1 + length ys + sizeof_exp e
    | (Ehalt x) => 1
    end
  with sizeof_fundefs f : nat := 
    match f with
    | Fcons f t v e fds => 1 + sizeof_exp e + sizeof_fundefs fds
    | Fnil => 0
    end.

  Definition sizeof (a : exp + fundefs) : nat :=
    match a with inl e => sizeof_exp e | inr f => sizeof_fundefs f end.

  Definition reflect_eq_var (a b : var) : (a = b) + (a <> b) :=
    match Pos.eqb_spec a b with
      ReflectT yes => inl yes
    | ReflectF no => inr no
    end.

  (* functional induction scheme for uncurry_exp, uncurry_fundefs *)
  Function uncurry_wf_ind
    (a : exp + fundefs)
    (P : _ -> _ ->  Prop) (Q : _ -> _ -> Prop)
    (Hconstr : forall x c vs e,
        P e (uncurry_exp e) ->
        P (Econstr x c vs e) (uncurry_exp (Econstr x c vs e)))
    (Hnil : forall x, P (Ecase x []) (uncurry_exp (Ecase x [])))
    (Hcons : forall x c e t,
        P e (uncurry_exp e) ->
        P (Ecase x t) (uncurry_exp (Ecase x t)) ->
        P (Ecase x ((c, e) :: t)) (uncurry_exp (Ecase x ((c, e) :: t))))
    (Hproj : forall x c n y e,
        P e (uncurry_exp e) ->
        P (Eproj x c n y e) (uncurry_exp (Eproj x c n y e)))
    (Happ : forall x f xs,
        P (Eapp x f xs) (uncurry_exp (Eapp x f xs)))
    (Hprim : forall x p xs e,
        P e (uncurry_exp e) ->
        P (Eprim x p xs e) (uncurry_exp (Eprim x p xs e)))
    (Hfun : forall e fds,
        P e (uncurry_exp e) ->
        Q fds (uncurry_fundefs fds) ->
        P (Efun fds e) (uncurry_exp (Efun fds e)))
    (Hhalt : forall x,
        P (Ehalt x) (uncurry_exp (Ehalt x)))
    (HFnil : Q Fnil (uncurry_fundefs Fnil))
    (HFcons : forall f ft k fv g gt gv ge kt fds,
        Q fds (uncurry_fundefs fds) ->
        P ge (uncurry_exp ge) ->
        Q (Fcons f ft (k :: fv) (Efun (Fcons g gt gv ge Fnil) (Eapp k kt [g])) fds)
          (uncurry_fundefs
             (Fcons f ft (k :: fv) (Efun (Fcons g gt gv ge Fnil) (Eapp k kt [g])) fds)))
    (HFcons1 : forall f ft k k' fv g g' gt gv ge kt fds,
        Q fds (uncurry_fundefs fds) ->
        P ge (uncurry_exp ge) ->
        k <> k' \/ g <> g' ->
        Q (Fcons f ft (k :: fv) (Efun (Fcons g gt gv ge Fnil) (Eapp k' kt [g'])) fds)
          (uncurry_fundefs
             (Fcons f ft (k :: fv) (Efun (Fcons g gt gv ge Fnil) (Eapp k' kt [g'])) fds)))
    (HFcons2 : forall f ft v e fds,
        Q fds (uncurry_fundefs fds) ->
        P e (uncurry_exp e) ->
        (~ exists k k' fv g g' gt gv ge kt, 
          Fcons f ft v e fds =
          Fcons f ft (k :: fv) (Efun (Fcons g gt gv ge Fnil) (Eapp k' kt [g'])) fds) ->
        Q (Fcons f ft v e fds) (uncurry_fundefs (Fcons f ft v e fds)))
    {measure sizeof a} :
    match a with
      inl e => P e (uncurry_exp e)
    | inr f => Q f (uncurry_fundefs f)
    end :=
    let go b := uncurry_wf_ind b
                               P Q Hconstr Hnil Hcons Hproj Happ Hprim Hfun Hhalt
                               HFnil HFcons HFcons1 HFcons2 in
    match a with
      inl (Econstr x c vs e) => Hconstr x c vs e (go (inl e))
    | inl (Ecase x []) => Hnil x
    | inl (Ecase x ((c, e) :: t)) => Hcons x c e t (go (inl e)) (go (inl (Ecase x t)))
    | inl (Eproj x c n y e) => Hproj x c n y e (go (inl e))
    | inl (Eapp x f xs) => Happ x f xs
    | inl (Eprim x p xs e) => Hprim x p xs e (go (inl e))
    | inl (Efun fds e) => Hfun e fds (go (inl e)) (go (inr fds))
    | inl (Ehalt x) => Hhalt x
    | inr Fnil => HFnil
    | inr (Fcons f ft fl fe fds) => 
      match fl with
        k :: fv => 
        match fe with
          Efun fds1 e =>
          match fds1 with
            Fnil =>
              HFcons2 f ft (k :: fv) (Efun Fnil e) fds
              (go (inr fds)) (go (inl (Efun Fnil e)))
              (fun '(ex_intro k (ex_intro k' (ex_intro fv (ex_intro g (ex_intro g' (ex_intro gt
                (ex_intro gv (ex_intro ge (ex_intro kt Heq))))))))) =>
                (Fcons_neq_Fnil (eq_sym (Efun_eq_fds_eq (Fcons_eq_e_eq Heq)))))
          | Fcons g gt gv ge Fnil =>
            match e with
              Eapp k' kt l =>
              match l with
                [] =>
                  HFcons2 f ft (k :: fv) (Efun (Fcons g gt gv ge Fnil) (Eapp k' kt [])) fds
                  (go (inr fds)) (go (inl (Efun (Fcons g gt gv ge Fnil) (Eapp k' kt []))))
                  (fun '(ex_intro k (ex_intro k' (ex_intro fv (ex_intro g (ex_intro g' (ex_intro gt
                    (ex_intro gv (ex_intro ge (ex_intro kt Heq))))))))) =>
                    (nil_cons (Eapp_eq_xs_eq (Efun_eq_e_eq (Fcons_eq_e_eq Heq)))))
              | [g'] =>
                match reflect_eq_var k k' with
                  inl yes =>
                  match yes, reflect_eq_var g g' with
                    eq_refl, inl yes => match yes with eq_refl =>
                      HFcons f ft k fv g gt gv ge kt fds (go (inr fds)) (go (inl ge))
                    end
                  | eq_refl, inr no =>
                      HFcons1 f ft k k fv g g' gt gv ge kt fds (go (inr fds)) (go (inl ge))
                      (or_intror no)
                  end
                | inr no =>
                    HFcons1 f ft k k' fv g g' gt gv ge kt fds (go (inr fds)) (go (inl ge))
                    (or_introl no)
                end
                (* doesn't work with coq 8.7.1. assertion failure @ plugins/funind/recdef.ml, line 523
                match Pos.eqb_spec k k' with
                  ReflectT yes =>
                  match yes, Pos.eqb_spec g g' with
                    eq_refl, ReflectT yes => match yes with eq_refl =>
                      HFcons f ft k fv g gt gv ge kt fds (go (inr fds)) (go (inl ge))
                    end
                  | eq_refl, ReflectF no =>
                      HFcons1 f ft k k fv g g' gt gv ge kt fds (go (inr fds)) (go (inl ge))
                      (or_intror no)
                  end
                | ReflectF no =>
                    HFcons1 f ft k k' fv g g' gt gv ge kt fds (go (inr fds)) (go (inl ge))
                    (or_introl no)
                end *)
              | g' :: g1 :: l1 =>
                  HFcons2 f ft (k :: fv)
                  (Efun (Fcons g gt gv ge Fnil) (Eapp k' kt (g' :: g1 :: l1))) fds
                  (go (inr fds))
                  (go (inl (Efun (Fcons g gt gv ge Fnil) (Eapp k' kt (g' :: g1 :: l1)))))
                  (fun '(ex_intro k (ex_intro k' (ex_intro fv (ex_intro g (ex_intro g' (ex_intro gt
                    (ex_intro gv (ex_intro ge (ex_intro kt Heq))))))))) =>
                    (cons_cons_neq_cons (Eapp_eq_xs_eq (Efun_eq_e_eq (Fcons_eq_e_eq Heq)))))
              end (* match l *)
            | Econstr x1 c1 vs1 e1 =>
                HFcons2 f ft (k :: fv) (Efun (Fcons g gt gv ge Fnil) (Econstr x1 c1 vs1 e1)) fds
                (go (inr fds)) (go (inl (Efun (Fcons g gt gv ge Fnil) (Econstr x1 c1 vs1 e1))))
                (fun '(ex_intro k (ex_intro k' (ex_intro fv (ex_intro g (ex_intro g' (ex_intro gt
                  (ex_intro gv (ex_intro ge (ex_intro kt Heq))))))))) =>
                  (Econstr_neq_Eapp (Efun_eq_e_eq (Fcons_eq_e_eq Heq))))
            | Ecase v1 l1 =>
                HFcons2 f ft (k :: fv) (Efun (Fcons g gt gv ge Fnil) (Ecase v1 l1)) fds
                (go (inr fds)) (go (inl (Efun (Fcons g gt gv ge Fnil) (Ecase v1 l1))))
                (fun '(ex_intro k (ex_intro k' (ex_intro fv (ex_intro g (ex_intro g' (ex_intro gt
                  (ex_intro gv (ex_intro ge (ex_intro kt Heq))))))))) =>
                  (Ecase_neq_Eapp (Efun_eq_e_eq (Fcons_eq_e_eq Heq))))
            | Eproj x1 c1 n1 y1 e1 =>
                HFcons2 f ft (k :: fv) (Efun (Fcons g gt gv ge Fnil) (Eproj x1 c1 n1 y1 e1)) fds
                (go (inr fds)) (go (inl (Efun (Fcons g gt gv ge Fnil) (Eproj x1 c1 n1 y1 e1))))
                (fun '(ex_intro k (ex_intro k' (ex_intro fv (ex_intro g (ex_intro g' (ex_intro gt
                  (ex_intro gv (ex_intro ge (ex_intro kt Heq))))))))) =>
                  (Eproj_neq_Eapp (Efun_eq_e_eq (Fcons_eq_e_eq Heq))))
            | Efun fds2 e1 =>
                HFcons2 f ft (k :: fv) (Efun (Fcons g gt gv ge Fnil) (Efun fds2 e1)) fds
                (go (inr fds)) (go (inl (Efun (Fcons g gt gv ge Fnil) (Efun fds2 e1))))
                (fun '(ex_intro k (ex_intro k' (ex_intro fv (ex_intro g (ex_intro g' (ex_intro gt
                  (ex_intro gv (ex_intro ge (ex_intro kt Heq))))))))) =>
                  (Efun_neq_Eapp (Efun_eq_e_eq (Fcons_eq_e_eq Heq))))
            | Eprim x1 p1 xs1 e1 =>
                HFcons2 f ft (k :: fv) (Efun (Fcons g gt gv ge Fnil) (Eprim x1 p1 xs1 e1)) fds
                (go (inr fds)) (go (inl (Efun (Fcons g gt gv ge Fnil) (Eprim x1 p1 xs1 e1))))
                (fun '(ex_intro k (ex_intro k' (ex_intro fv (ex_intro g (ex_intro g' (ex_intro gt
                  (ex_intro gv (ex_intro ge (ex_intro kt Heq))))))))) =>
                  (Eprim_neq_Eapp (Efun_eq_e_eq (Fcons_eq_e_eq Heq))))
            | Ehalt x1 =>
                HFcons2 f ft (k :: fv) (Efun (Fcons g gt gv ge Fnil) (Ehalt x1)) fds
                (go (inr fds)) (go (inl (Efun (Fcons g gt gv ge Fnil) (Ehalt x1))))
                (fun '(ex_intro k (ex_intro k' (ex_intro fv (ex_intro g (ex_intro g' (ex_intro gt
                  (ex_intro gv (ex_intro ge (ex_intro kt Heq))))))))) =>
                  (Ehalt_neq_Eapp (Efun_eq_e_eq (Fcons_eq_e_eq Heq))))
            end (* match e *)
          | Fcons g gt gv ge (Fcons f1 t1 v1 e1 fds2) =>
              HFcons2 f ft (k :: fv) (Efun (Fcons g gt gv ge (Fcons f1 t1 v1 e1 fds2)) e) fds
              (go (inr fds)) (go (inl (Efun (Fcons g gt gv ge (Fcons f1 t1 v1 e1 fds2)) e)))
              (fun '(ex_intro k (ex_intro k' (ex_intro fv (ex_intro g (ex_intro g' (ex_intro gt
                (ex_intro gv (ex_intro ge (ex_intro kt Heq))))))))) =>
                (Fcons_neq_Fnil (Fcons_eq_fds_eq (Efun_eq_fds_eq (Fcons_eq_e_eq Heq)))))
          end (* match fds1 *)
        | Econstr x c vs e => HFcons2 f ft (k :: fv) (Econstr x c vs e) fds
            (go (inr fds)) (go (inl (Econstr x c vs e)))
            (fun '(ex_intro k (ex_intro k' (ex_intro fv (ex_intro g (ex_intro g' (ex_intro gt
              (ex_intro gv (ex_intro ge (ex_intro kt Heq))))))))) =>
              (Econstr_neq_Efun (Fcons_eq_e_eq Heq)))
        | Ecase x l => HFcons2 f ft (k :: fv) (Ecase x l) fds
            (go (inr fds)) (go (inl (Ecase x l))) 
            (fun '(ex_intro k (ex_intro k' (ex_intro fv (ex_intro g (ex_intro g' (ex_intro gt
              (ex_intro gv (ex_intro ge (ex_intro kt Heq))))))))) =>
              (Ecase_neq_Efun (Fcons_eq_e_eq Heq)))
        | Eproj x c n y e => HFcons2 f ft (k :: fv) (Eproj x c n y e) fds
            (go (inr fds)) (go (inl (Eproj x c n y e)))
            (fun '(ex_intro k (ex_intro k' (ex_intro fv (ex_intro g (ex_intro g' (ex_intro gt
              (ex_intro gv (ex_intro ge (ex_intro kt Heq))))))))) =>
              (Eproj_neq_Efun (Fcons_eq_e_eq Heq)))
        | Eapp x f1 xs => HFcons2 f ft (k :: fv) (Eapp x f1 xs) fds
            (go (inr fds)) (go (inl (Eapp x f1 xs)))
            (fun '(ex_intro k (ex_intro k' (ex_intro fv (ex_intro g (ex_intro g' (ex_intro gt
              (ex_intro gv (ex_intro ge (ex_intro kt Heq))))))))) =>
              (Eapp_neq_Efun (Fcons_eq_e_eq Heq)))
        | Eprim x p xs e => HFcons2 f ft (k :: fv) (Eprim x p xs e) fds
            (go (inr fds)) (go (inl (Eprim x p xs e)))
            (fun '(ex_intro k (ex_intro k' (ex_intro fv (ex_intro g (ex_intro g' (ex_intro gt
              (ex_intro gv (ex_intro ge (ex_intro kt Heq))))))))) =>
              (Eprim_neq_Efun (Fcons_eq_e_eq Heq)))
        | Ehalt x => HFcons2 f ft (k :: fv) (Ehalt x) fds
            (go (inr fds)) (go (inl (Ehalt x)))
            (fun '(ex_intro k (ex_intro k' (ex_intro fv (ex_intro g (ex_intro g' (ex_intro gt
              (ex_intro gv (ex_intro ge (ex_intro kt Heq))))))))) =>
              (Ehalt_neq_Efun (Fcons_eq_e_eq Heq)))
        end (* match fe *)
      | [] => HFcons2 f ft [] fe fds (go (inr fds)) (go (inl fe))
        (fun '(ex_intro k (ex_intro k' (ex_intro fv (ex_intro g (ex_intro g' (ex_intro gt
           (ex_intro gv (ex_intro ge (ex_intro kt Heq))))))))) =>
           nil_cons (Fcons_eq_v_eq Heq))
      end (* match fl *)
    end (* match a *).
  Proof.
    all: intros; simpl; omega.
  Qed.

  Corollary uncurry_mut : forall (P : _ -> _ -> Prop) (Q : _ -> _ -> Prop),
    (forall x c vs e,
        P e (uncurry_exp e) ->
        P (Econstr x c vs e) (uncurry_exp (Econstr x c vs e))) ->
    (forall x, P (Ecase x []) (uncurry_exp (Ecase x []))) ->
    (forall x c e t,
        P e (uncurry_exp e) ->
        P (Ecase x t) (uncurry_exp (Ecase x t)) ->
        P (Ecase x ((c, e) :: t)) (uncurry_exp (Ecase x ((c, e) :: t)))) ->
    (forall x c n y e,
        P e (uncurry_exp e) ->
        P (Eproj x c n y e) (uncurry_exp (Eproj x c n y e))) ->
    (forall x f xs,
        P (Eapp x f xs) (uncurry_exp (Eapp x f xs))) ->
    (forall x p xs e,
        P e (uncurry_exp e) ->
        P (Eprim x p xs e) (uncurry_exp (Eprim x p xs e))) ->
    (forall e fds,
        P e (uncurry_exp e) ->
        Q fds (uncurry_fundefs fds) ->
        P (Efun fds e) (uncurry_exp (Efun fds e))) ->
    (forall x,
        P (Ehalt x) (uncurry_exp (Ehalt x))) ->
    (Q Fnil (uncurry_fundefs Fnil)) ->
    (forall f ft k fv g gt gv ge kt fds,
        Q fds (uncurry_fundefs fds) ->
        P ge (uncurry_exp ge) ->
        Q (Fcons f ft (k :: fv) (Efun (Fcons g gt gv ge Fnil) (Eapp k kt [g])) fds)
          (uncurry_fundefs
             (Fcons f ft (k :: fv) (Efun (Fcons g gt gv ge Fnil) (Eapp k kt [g])) fds))) ->
    (forall f ft k k' fv g g' gt gv ge kt fds,
        Q fds (uncurry_fundefs fds) ->
        P ge (uncurry_exp ge) ->
        k <> k' \/ g <> g' ->
        Q (Fcons f ft (k :: fv) (Efun (Fcons g gt gv ge Fnil) (Eapp k' kt [g'])) fds)
          (uncurry_fundefs
             (Fcons f ft (k :: fv) (Efun (Fcons g gt gv ge Fnil) (Eapp k' kt [g'])) fds))) ->
    (forall f ft v e fds,
        Q fds (uncurry_fundefs fds) ->
        P e (uncurry_exp e) ->
        (~ exists k k' fv g g' gt gv ge kt, 
          Fcons f ft v e fds =
          Fcons f ft (k :: fv) (Efun (Fcons g gt gv ge Fnil) (Eapp k' kt [g'])) fds) ->
        Q (Fcons f ft v e fds) (uncurry_fundefs (Fcons f ft v e fds))) ->
    (forall e, P e (uncurry_exp e)) /\ (forall f, Q f (uncurry_fundefs f)).
  Proof.
    split; intros.
    - eapply (uncurry_wf_ind (inl e)); eauto.
    - eapply (uncurry_wf_ind (inr f)); eauto.
  Qed.

  Ltac uncurry_induction_mut P Q IHe IHf IHeq :=
    apply uncurry_mut with (P := P) (Q := Q);
    [ intros ? ? ? ? IHe
    | intros ?
    | intros ? ? ? ? IHe IHf
    | intros ? ? ? ? ? IHe
    | intros ? ? ?
    | intros ? ? ? ? IHe
    | intros ? ? IHe IHf
    | intros ?
    | intros
    | intros ? ? ? ? ? ? ? ? ? ? IHf IHe
    | intros ? ? ? ? ? ? ? ? ? ? ? ? IHf IHe IHeq
    | intros ? ? ? ? ? IHf IHe IHeq
    ].

  (* all variables in a list are distinct and disjoint from some set of used vars *)
  Definition fresh_copies (s : Ensemble var) (l : list var) : Prop
    := Disjoint _ s (FromList l) /\ NoDup l.

  (* all the used variables in an expression *)
  Definition used_vars (e : exp) : Ensemble var := bound_var e :|: occurs_free e.
  Definition used_vars_fundefs (fds : fundefs) : Ensemble var
    := bound_var_fundefs fds :|: occurs_free_fundefs fds.
  Definition used_vars_ctx (c : exp_ctx) : Ensemble var
    := bound_var_ctx c :|: occurs_free_ctx c.
  Definition used_vars_fundefs_ctx (f : fundefs_ctx) : Ensemble var
    := bound_var_fundefs_ctx f :|: occurs_free_fundefs_ctx f.

  Lemma used_vars_dec: forall e, Decidable (used_vars e).
  Proof.
    intros e.
    apply Decidable_Union.
    apply bound_var_dec.
    apply Decidable_occurs_free.
  Qed.

  Lemma used_vars_fundefs_dec: forall fds, Decidable (used_vars_fundefs fds).
  Proof.
    intros fds.
    apply Decidable_Union.
    apply bound_var_fundefs_dec.
    apply Decidable_occurs_free_fundefs.
  Qed.

  Lemma used_vars_ctx_dec: forall e, Decidable (used_vars_ctx e).
  Proof.
    intros e.
    apply Decidable_Union.
    apply bound_var_ctx_dec.
    apply Decidable_occurs_free_ctx.
  Qed.

  Lemma used_vars_fundefs_ctx_dec: forall fds, Decidable (used_vars_fundefs_ctx fds).
  Proof.
    intros fds.
    apply Decidable_Union.
    apply bound_var_fundefs_ctx_dec.
    apply Decidable_occurs_free_fundefs_ctx.
  Qed.

  Lemma Decidable_not_not : forall {A} (S : Ensemble A),
    Decidable S -> forall a,
    ~ ~ In _ S a <-> In _ S a.
  Proof.
    intros A S HS a;
    destruct HS as [HS];
    specialize HS with (x := a);
    destruct HS as [HS|HS];
    split; easy.
  Qed.

  Ltac split_var_eq a b :=
    destruct (PS.Raw.MX.eq_dec a b).

  Ltac split_var_in_list a l :=
    destruct (in_dec PS.Raw.MX.eq_dec a l).

  Ltac split_var_in_fundefs a fds Hfds :=
    destruct (Decidable_name_in_fundefs fds) as [Hfds]; destruct (Hfds a).

  Local Ltac solve_bound_cases a v l := 
    split_var_eq a v; split_var_in_list a l;
    [ right; now constructor
    | left; subst a; constructor
    | right; now constructor
    | right].

  Lemma used_vars_subset_mut :
    (forall c, (fun c => forall e, used_vars e \subset used_vars (c |[ e ]|)) c) /\
    (forall f, (fun f => forall e, used_vars e \subset used_vars_fundefs (f <[ e ]>)) f).
  Proof with eauto with Ensembles_DB.
    exp_fundefs_ctx_induction IHe IHf; simpl; try rename e into c.
    - (* Hole_c *) easy...
    - (* Econstr_c *)
      intros e; eapply Included_trans; [apply IHe|]; intros a Ha.
      destruct Ha; [left; now constructor|].
      solve_bound_cases x v l.
      apply Free_Econstr2; auto.
    - (* Eproj_c *)
      intros e; eapply Included_trans; [apply IHe|]; intros a Ha.
      destruct Ha; [left; now constructor|].
      split_var_eq x v; [left|right].
      subst x; constructor.
      constructor; auto.
    - (* Eprim_c *)
      intros e; eapply Included_trans; [apply IHe|]; intros a Ha.
      destruct Ha; [left; now constructor|].
      solve_bound_cases x v l.
      apply Free_Eprim2; auto.
    - (* Efun1_c *)
      intros l0 e; eapply Included_trans; [apply IHe|]; intros a Ha.
      unfold used_vars.
      rewrite bound_var_Ecase_app.
      rewrite occurs_free_Ecase_app.
      destruct Ha; [|auto..].
      repeat rewrite <- Union_assoc.
      rewrite Union_commut.
      repeat rewrite <- Union_assoc.
      apply Union_introl.
      econstructor; [eassumption|now constructor].
    - (* Efun2_c *)
      intros e; eapply Included_trans; [apply IHe|]; intros a Ha.
      destruct Ha; [left; now apply Bound_Efun2|].
      split_var_in_fundefs x f4 Hf4; [left|right].
      constructor; now apply name_in_fundefs_bound_var_fundefs.
      now constructor.
    - (* Fcons1_c *)
      intros e; eapply Included_trans; [apply IHf|]; intros a Ha. 
      destruct Ha; [left; now constructor|].
      split_var_in_fundefs x (f5 <[ e ]>) Hf5; [left|right].
      constructor; now apply name_in_fundefs_bound_var_fundefs.
      now constructor.
    - (* Fcons2_c*)
      intros e; eapply Included_trans; [apply IHe|]; intros a Ha. 
      destruct Ha; [left; now constructor|].
      split_var_eq x v; split_var_in_list x l.
      left... left; subst x... left...
      split_var_in_fundefs x f6 Hf6.
      left; apply Bound_Fcons2; now apply name_in_fundefs_bound_var_fundefs.
      right; constructor; assumption.
    - (* Fcons3_c *)
      intros e; eapply Included_trans; [apply IHf|]; intros a Ha. 
      destruct Ha; [left; now constructor|].
      split_var_eq x v; split_var_in_list x l.
      left... left; subst x... left...
      split_var_in_fundefs x (f7 <[ e ]>) Hf7.
      left; apply Bound_Fcons2; now apply name_in_fundefs_bound_var_fundefs.
      right; constructor; assumption.
  Qed.

  Corollary used_vars_subset : forall c e, 
    used_vars e \subset used_vars (c |[ e ]|).
  Proof. apply used_vars_subset_mut. Qed.

  Corollary used_vars_subset_fundefs_ctx : forall f e, 
    used_vars e \subset used_vars_fundefs (f <[ e ]>).
  Proof. apply used_vars_subset_mut. Qed.

  Lemma occurs_in_vars_correct : forall a l, occurs_in_vars a l = true <-> List.In a l.
  Proof.
    induction l; [firstorder|].
    destruct (Pos.eqb_spec a a0); subst.
    simpl; rewrite Pos.eqb_refl; simpl; split; intros; [now left|easy].
    simpl; rewrite <- Pos.eqb_neq in n; unfold eq_var; rewrite n; simpl.
    rewrite IHl.
    split; [intros H; now right|intros [contra|H]]; [|assumption].
    rewrite Pos.eqb_neq in n; congruence.
  Qed.

  Corollary occurs_in_vars_correct_neq : forall a l, occurs_in_vars a l = false <-> ~ List.In a l.
  Proof.
    assert (forall a, a = false <-> ~ (a = true)). {
      split; intros Ha.
      - intros Hcontra; congruence.
      - destruct a; [congruence|reflexivity].
    } 
    intros; rewrite H.
    apply not_iff_compat.
    apply occurs_in_vars_correct.
  Qed.

  Lemma Union_demorgan : forall {A} (l r : Ensemble A) a,
    ~ In _ (l :|: r) a <-> ~ In _ l a /\ ~ In _ r a.
  Proof.
    split; intros.
    - split; intros contra; contradiction H.
      now left. now right.
    - destruct H. intros contra. inv contra; congruence.
  Qed.

  Lemma negb_not : forall a b, a = negb b <-> a <> b.
  Proof. destruct a; destruct b; firstorder. Qed.

  Lemma Disjoint_Singleton_In : forall A S a,
    Decidable S -> Disjoint A S [set a] <-> ~ In _ S a.
  Proof.
    split; intros H.
    - inv H; specialize H0 with (x := a).
      destruct X; destruct (Dec a); [|easy].
      contradiction H0; constructor; easy.
    - constructor.
      intros x contra; inv contra.
      now inv H1.
  Qed.

  Lemma not_Disjoint_Singleton_In : forall A S a,
    Decidable S -> ~ Disjoint A S [set a] <-> In _ S a.
  Proof.
    split; [intros H|inversion 2; eapply H0; eauto].
    destruct X; destruct (Dec a); [easy|].
    contradiction H; constructor; intros.
    intros contra; destruct contra.
    inv H1.
    contradiction.
  Qed.

  Lemma find_def_is_Some_occurs_free_fundefs : forall f fds t xs e a,
    find_def f fds = Some (t, xs, e) ->
    occurs_free e a ->
    ~ List.In a xs ->
    ~ name_in_fundefs fds a ->
    occurs_free_fundefs fds a.
  Proof.
    induction fds; simpl; intros; [|now contradiction H2].
    destruct (M.elt_eq f v); [subst; inv H|].
    - constructor; auto; intros contra; subst; contradiction H2; [now left|now right].
    - apply Free_Fcons2; [|intros contra; subst; contradiction H2; now left].
      eapply IHfds; eauto.
      intros contra; subst; contradiction H2; now right.
  Qed.

  Hint Resolve Union_demorgan.
  Hint Resolve negb_not.
  Hint Resolve Disjoint_Singleton_In.
  Hint Resolve not_Disjoint_Singleton_In.
  Hint Resolve used_vars_dec.
  Hint Resolve used_vars_fundefs_dec.
  Hint Resolve bound_var_dec.
  Hint Resolve bound_var_fundefs_dec.
  Hint Resolve Decidable_occurs_free.
  Hint Resolve Decidable_occurs_free_fundefs.
  Hint Resolve Decidable_Union.
  Hint Resolve Decidable_Intersection.
  Hint Resolve Decidable_Setminus.
  Hint Resolve Decidable_singleton_var.
  Hint Resolve Decidable_FromList.
  Hint Resolve Decidable_occurs_free.
  Hint Resolve name_in_fundefs_bound_var_fundefs.
  Hint Constructors Union.
  Hint Constructors or.

  Local Ltac simplify_boolean_exprs := 
    simpl in *;
    repeat rewrite orb_false_r in *;
    repeat rewrite orb_true_r in *;
    simpl in *.

  Local Ltac rewrite_trivial_iffs :=
    repeat match goal with
    | [ Heq : ?a <-> ?b, Ha : ?a |- _ ] => (assert b by now rewrite <- Heq); clear Heq
    | [ Heq : ?a <-> ?b |- ?a ] => rewrite Heq
    | [ Heq : true = false <-> ~ In var ?S ?a |- _ ] =>
        apply not_iff_compat in Heq;
        rewrite <- negb_not in Heq;
        (rewrite Decidable_not_not in Heq; [|auto]);
        (assert (In var S a) by now rewrite <- Heq); clear Heq
    | [ Heq : false = false <-> In var ?S ?a |- _ ] =>
        (assert (In var S a) by now rewrite <- Heq); clear Heq
    | [ Heq : false = false <-> ~ In var ?S ?a |- _ ] => 
        (assert (~ In var S a) by now rewrite <- Heq); clear Heq
    end.

  Local Ltac eliminate_singleton_disjoints :=
    repeat match goal with
    | [ Hin : _ = _ <-> Disjoint _ _ [set _] |- _ ] =>
        rewrite Disjoint_Singleton_In in Hin; [|auto]
    | [ Hin : _ = _ <-> ~ Disjoint _ _ [set _] |- _ ] =>
        rewrite not_Disjoint_Singleton_In in Hin; [|auto]
    | [ Hin : Disjoint _ _ [set _] |- _ ] =>
        rewrite Disjoint_Singleton_In in Hin; [|auto]
    | [ Hin : ~ Disjoint _ _ [set _] |- _ ] =>
        rewrite not_Disjoint_Singleton_In in Hin; [|auto]
    end;
    try (rewrite Disjoint_Singleton_In; [|auto]);
    try (rewrite not_Disjoint_Singleton_In; [|auto]).

  Local Ltac demorgan_not_used_vars :=
    repeat match goal with
    | [ Hin : ~ In var (used_vars _) _ |- _ ] =>
        unfold used_vars in Hin;
        rewrite Union_demorgan in Hin;
        destruct Hin
    | [ Hin : ~ In var (used_vars_fundefs _) _ |- _ ] =>
        unfold used_vars_fundefs in Hin;
        rewrite Union_demorgan in Hin;
        destruct Hin
    end.

  Local Ltac cleanup :=
    try (rewrite occurs_in_vars_correct in *);
    try (rewrite occurs_in_vars_correct_neq in *);
    simplify_boolean_exprs;
    eliminate_singleton_disjoints;
    rewrite_trivial_iffs;
    demorgan_not_used_vars.

  Local Ltac super_destruct e Hvar :=
    destruct e eqn:Hvar;
    simpl in *;
    try rewrite Hvar in *;
    try (rewrite Pos.eqb_eq in Hvar; subst);
    try (rewrite Pos.eqb_neq in Hvar);
    cleanup;
    try congruence.

  Local Ltac inv_all :=
    repeat match goal with
    | [ H : In var _ _ |- _ ] => inv H
    | [ H : List.In _ _ |- _ ] => inv H
    | [ H : (_, _) = (_, _) |- _ ] => inv H
    end;
    eauto with Ensembles_DB.

  Lemma occurs_in_exp_correct_mut : forall x,
    (forall e, (fun e => occurs_in_exp x e = false <-> Disjoint _ (used_vars e) [set x]) e) /\
    (forall f, (fun f => occurs_in_fundefs x f = false <-> Disjoint _ (used_vars_fundefs f) [set x]) f).
  Proof.
    intros x.
    apply exp_def_mutual_ind.
    - (* Econstr *)
      simpl; intros v t l e He1; split; intros H.
      + super_destruct (eq_var v x) Hvar.
        super_destruct (occurs_in_vars x l) Hvars.
        intros contra; inv_all.
      + super_destruct (eq_var v x) Hvar.
        contradiction H; constructor.
        super_destruct (occurs_in_vars x l) Hvars.
        contradiction H0; now constructor.
        intros contra; inv_all.
    - (* Ecase [] *)
      simpl; intros v; split; intros H; super_destruct (eq_var x v) Hvar.
      + intros contra; inv_all.
      + contradiction H0; constructor.
    - (* Ecase :: *)
      simpl; intros v l c e He IHl; split; intros H.
      + super_destruct (eq_var x v) Hvar.
        super_destruct (occurs_in_exp x e) Hexp.
        intros contra; inv_all.
      + super_destruct (eq_var x v) Hvar.
        contradiction H1; constructor.
        super_destruct (occurs_in_exp x e) Hexp.
        inv H1.
        contradiction H; econstructor; [eassumption|now constructor].
        contradiction H0; now constructor.
        intros contra; inv_all.
        contradiction H; econstructor; [|right]; eassumption.
    - (* Eproj *)
      simpl; intros v t n v0 e He; split; intros H.
      + super_destruct (eq_var v x) Hvar.
        super_destruct (eq_var x v0) Hvar'.
        intros contra; inv_all.
      + super_destruct (eq_var v x) Hvar.
        super_destruct (occurs_in_exp x e) Hexp; try (contradiction H; constructor).
        super_destruct (eq_var x v0) Hvar'.
        contradiction H0; constructor.
        intros contra; inv_all.
    - (* Efun *)
      simpl; intros fds Hfds e He; split; intros H. 
      + super_destruct (occurs_in_exp x e) Hexp.
        super_destruct (occurs_in_fundefs x fds) Hfds'.
        intros contra; inv_all.
      + super_destruct (occurs_in_exp x e) Hexp.
        inv H0.
        contradiction H; now apply Bound_Efun2.
        super_destruct (occurs_in_fundefs x fds) Hfds'.
        inv H0.
        contradiction H; now constructor.
        contradiction H1; eauto.
        contradiction H1; apply Free_Efun1; [|assumption].
        intros contra; now apply name_in_fundefs_bound_var_fundefs in contra.
        intros contra; inv contra.
        contradiction H; now constructor.
        contradiction H2; now apply Free_Efun2.
    - (* Eapp *)
      simpl; intros v t l; split; intros H.
      + super_destruct (eq_var x v) Hvar.
        intros contra; inv contra; inv_all.
      + super_destruct (eq_var x v) Hvar.
        contradiction H0; constructor.
        eauto.
    - (* Eprim *)
      simpl; intros v p l e He; split; intros H.
      + super_destruct (eq_var v x) Hvar.
        super_destruct (occurs_in_vars x l) Hvars.
        intros contra; inv_all.
      + super_destruct (eq_var v x) Hvar.
        contradiction H; constructor.
        super_destruct (occurs_in_vars x l) Hvars.
        contradiction H0; now constructor.
        intros contra; inv_all.
    - (* Ehalt *)
      simpl; intros v; split; intros H; super_destruct (eq_var v x) Hvar.
      intros contra; inv_all.
      contradiction H0; constructor.
    - (* Fcons *)
      simpl; intros v t l e He1 fd Hfd1; split; intros H.
      + super_destruct (eq_var v x) Hvar.
        super_destruct (occurs_in_vars x l) Hvars.
        super_destruct (occurs_in_exp x e) Hexp.
        intros contra; inv_all.
      + super_destruct (eq_var v x) Hvar.
        contradiction H; constructor; now left.
        super_destruct (occurs_in_vars x l) Hvars.
        contradiction H; constructor; now right.
        super_destruct (occurs_in_exp x e) Hexp.
        inv H1.
        contradiction H; now apply Bound_Fcons3.
        contradiction H0; constructor; eauto.
        intros contra; apply name_in_fundefs_bound_var_fundefs in contra.
        contradiction H; now apply Bound_Fcons2.
        intros contra; inv contra.
        contradiction H. now apply Bound_Fcons2.
        contradiction H0; apply Free_Fcons2; auto.
    - (* Fnil *)
      cleanup; split; [intros _ contra; inv_all|easy].
  Qed.

  Corollary occurs_in_exp_correct : forall x e,
    occurs_in_exp x e = false <-> Disjoint _ (used_vars e) [set x].
  Proof. apply occurs_in_exp_correct_mut. Qed.

  Corollary occurs_in_fundefs_correct : forall x f,
    occurs_in_fundefs x f = false <-> Disjoint _ (used_vars_fundefs f) [set x].
  Proof. apply occurs_in_exp_correct_mut. Qed.

  Corollary occurs_in_exp_iff_used_vars : forall e a,
    occurs_in_exp a e = true <-> In _ (used_vars e) a.
  Proof.
    intros.
    rewrite <- Decidable_not_not; auto.
    replace true with (negb false); auto.
    rewrite negb_not.
    apply not_iff_compat.
    rewrite <- Disjoint_Singleton_In; auto.
    apply occurs_in_exp_correct.
  Qed.

  Corollary not_occurs_in_exp_iff_used_vars : forall e a,
    occurs_in_exp a e = false <-> ~ In _ (used_vars e) a.
  Proof. intros. rewrite <- Disjoint_Singleton_In; auto. apply occurs_in_exp_correct. Qed.

  Corollary occurs_in_fundefs_iff_used_vars_fundefs : forall e a,
    occurs_in_fundefs a e = true <-> In _ (used_vars_fundefs e) a.
  Proof.
    intros.
    rewrite <- Decidable_not_not; auto.
    replace true with (negb false); auto.
    rewrite negb_not.
    apply not_iff_compat.
    rewrite <- Disjoint_Singleton_In; auto.
    apply occurs_in_fundefs_correct.
  Qed.

  Corollary not_occurs_in_fundefs_iff_used_vars_fundefs : forall e a,
    occurs_in_fundefs a e = false <-> ~ In _ (used_vars_fundefs e) a.
  Proof. intros. rewrite <- Disjoint_Singleton_In; auto. apply occurs_in_fundefs_correct. Qed.

  Lemma Ensemble_iff_In_iff : forall {A} (S1 S2 : _ A),
    (S1 <--> S2) <-> (forall a, In _ S1 a <-> In _ S2 a).
  Proof.
    split; intros.
    now rewrite H.
    unfold Same_set, Included.
    firstorder.
  Qed.

  Lemma eq_var_iff_Singleton_l : forall b a, eq_var a b = true <-> In _ [set a] b.
  Proof.
    split; intros H; destruct (eq_var a b) eqn:Heq; try congruence.
    rewrite Peqb_eq in Heq; now subst.
    rewrite Pos.eqb_neq in Heq; contradiction Heq; now inv H.
  Qed.

  Lemma eq_var_iff_Singleton_r : forall a b, eq_var a b = true <-> In _ [set b] a.
  Proof.
    split; intros H; destruct (eq_var a b) eqn:Heq; try congruence.
    rewrite Peqb_eq in Heq; now subst.
    rewrite Pos.eqb_neq in Heq; contradiction Heq; now inv H.
  Qed.

  Lemma In_or_Iff_Union : forall {A} (a : A) S1 S2,
    In _ (S1 :|: S2) a <-> In _ S1 a \/ In _ S2 a.
  Proof. split; intros; destruct H; auto. Qed.

  Ltac translate_used_vars_to_firstorder a :=
    repeat (
      repeat rewrite <- occurs_in_exp_iff_used_vars in *; simpl in *;
      repeat rewrite <- occurs_in_fundefs_iff_used_vars_fundefs in *; simpl in *;
      repeat rewrite orb_true_iff in *;
      repeat rewrite (eq_var_iff_Singleton_r a) in *;
      repeat rewrite (eq_var_iff_Singleton_l a) in *;
      repeat rewrite occurs_in_vars_correct in *;
      repeat rewrite occurs_in_exp_iff_used_vars in *;
      repeat rewrite occurs_in_fundefs_iff_used_vars_fundefs in *;
      repeat rewrite In_or_Iff_Union in *
    ).

  Local Ltac solve_used_vars_lemma :=
    intros;
    rewrite Ensemble_iff_In_iff; intros a;
    translate_used_vars_to_firstorder a;
    firstorder.

  Lemma used_vars_Econstr : forall x c args e,
    used_vars (Econstr x c args e) <--> x |: FromList args :|: used_vars e.
  Proof. solve_used_vars_lemma. Qed.

  Lemma used_vars_Ecase_nil : forall x,
    used_vars (Ecase x []) <--> [set x].
  Proof. solve_used_vars_lemma. Qed.

  Lemma used_vars_Ecase_cons : forall x c e arms,
    used_vars (Ecase x ((c, e) :: arms)) <--> used_vars e :|: used_vars (Ecase x arms).
  Proof.
    induction arms.
    - intros; rewrite Ensemble_iff_In_iff; intros a.
      translate_used_vars_to_firstorder a.
      firstorder.
    - destruct a; rewrite Ensemble_iff_In_iff; intros a.
      translate_used_vars_to_firstorder a.
      clear IHarms; firstorder.
  Qed.

  Lemma used_vars_Eproj : forall x c n y e,
    used_vars (Eproj x c n y e) <--> x |: (y |: used_vars e).
  Proof. solve_used_vars_lemma. Qed.

  Lemma used_vars_Efun : forall fds e,
    used_vars (Efun fds e) <--> used_vars_fundefs fds :|: used_vars e.
  Proof. solve_used_vars_lemma. Qed.

  Lemma used_vars_Eapp: forall f t args,
    used_vars (Eapp f t args) <--> f |: FromList args.
  Proof. solve_used_vars_lemma. Qed.

  Lemma used_vars_Eprim : forall x p args e,
    used_vars (Eprim x p args e) <--> x |: FromList args :|: used_vars e.
  Proof. solve_used_vars_lemma. Qed.

  Lemma used_vars_Ehalt : forall x, used_vars (Ehalt x) <--> [set x].
  Proof. solve_used_vars_lemma. Qed.

  Lemma used_vars_Fcons : forall f t v e fds,
    used_vars_fundefs (Fcons f t v e fds) <-->
    f |: FromList v :|: used_vars e :|: used_vars_fundefs fds.
  Proof. solve_used_vars_lemma. Qed.

  Lemma used_vars_Fnil : used_vars_fundefs Fnil <--> Empty_set _.
  Proof. solve_used_vars_lemma. Qed.

  Ltac normalize_used_vars := 
    match goal with
    | |- context [ used_vars (Econstr _ _ _ _) ] => rewrite used_vars_Econstr
    | |- context [ used_vars (Eproj _ _ _ _ _) ] => rewrite used_vars_Eproj
    | |- context [ used_vars (Ecase _ []) ] => rewrite used_vars_Ecase_nil
    | |- context [ used_vars (Ecase _ (_ :: _)) ] => rewrite used_vars_Ecase_cons
    | |- context [ used_vars (Efun _ _) ] => rewrite used_vars_Efun
    | |- context [ used_vars (Eapp _ _ _) ] => rewrite used_vars_Eapp
    | |- context [ used_vars (Eprim _ _ _ _) ] => rewrite used_vars_Eprim
    | |- context [ used_vars (Ehalt _) ] => rewrite used_vars_Ehalt
    | |- context [ used_vars_fundefs (Fcons _ _ _ _ _) ] => rewrite used_vars_Fcons
    | |- context [ used_vars_fundefs Fnil ] => rewrite used_vars_Fnil
    | [ H : context [ used_vars (Econstr _ _ _ _)         ] |- _ ] => rewrite used_vars_Econstr in H
    | [ H : context [ used_vars (Eproj _ _ _ _ _)         ] |- _ ] => rewrite used_vars_Eproj in H
    | [ H : context [ used_vars (Ecase _ [])              ] |- _ ] => rewrite used_vars_Ecase_nil in H
    | [ H : context [ used_vars (Ecase _ (_ :: _))        ] |- _ ] => rewrite used_vars_Ecase_cons in H
    | [ H : context [ used_vars (Efun _ _)                ] |- _ ] => rewrite used_vars_Efun in H
    | [ H : context [ used_vars (Eapp _ _ _)              ] |- _ ] => rewrite used_vars_Eapp in H
    | [ H : context [ used_vars (Eprim _ _ _ _)           ] |- _ ] => rewrite used_vars_Eprim in H
    | [ H : context [ used_vars (Ehalt _)                 ] |- _ ] => rewrite used_vars_Ehalt in H
    | [ H : context [ used_vars_fundefs (Fcons _ _ _ _ _) ] |- _ ] => rewrite used_vars_Fcons in H
    | [ H : context [ used_vars_fundefs Fnil              ] |- _ ] => rewrite used_vars_Fnil in H
    end.

  (* "a small step" of uncurrying *)
  Inductive uncurry_step :
    exp -> (* original expression *)
    Ensemble var -> (* used variables *)
    localMap -> (* already uncurried functions *)
    exp -> (* expression w/ 1 function uncurried *)
    Ensemble var -> (* new used variables *)
    localMap -> (* new uncurried functions *)
    Prop :=
  | uncurry_constr : forall x c args e e1 s s1 m m1,
      uncurry_step e s m e1 s1 m1 ->
      uncurry_step (Econstr x c args e) s m (Econstr x c args e1) s1 m1
  | uncurry_case_expr : forall x arms c e e1 s s1 m m1,
      uncurry_step e s m e1 s1 m1 ->
      uncurry_step (Ecase x ((c, e) :: arms)) s m (Ecase x ((c, e1) :: arms)) s1 m1
  | uncurry_case_arms : forall x arms arms1 arm s s1 m m1,
      uncurry_step (Ecase x arms) s m (Ecase x arms1) s1 m1 ->
      uncurry_step (Ecase x (arm :: arms)) s m (Ecase x (arm :: arms1)) s1 m1
  | uncurry_proj : forall x c n y e e1 s s1 m m1,
      uncurry_step e s m e1 s1 m1 ->
      uncurry_step (Eproj x c n y e) s m (Eproj x c n y e1) s1 m1
  | uncurry_prim : forall x p args e e1 s s1 m m1,
      uncurry_step e s m e1 s1 m1 ->
      uncurry_step (Eprim x p args e) s m (Eprim x p args e1) s1 m1
  | uncurry_fun_expr : forall fds e e1 s s1 m m1,
      uncurry_step e s m e1 s1 m1 ->
      uncurry_step (Efun fds e) s m (Efun fds e1) s1 m1
  | uncurry_fun_fds : forall fds fds1 e s s1 m m1,
      uncurry_fundefs_step fds s m fds1 s1 m1 ->
      uncurry_step (Efun fds e) s m (Efun fds1 e) s1 m1
  with uncurry_fundefs_step :
    fundefs ->
    Ensemble var ->
    localMap ->
    fundefs ->
    Ensemble var ->
    localMap ->
    Prop :=
  | uncurry_fundefs_fds : forall f t args e fds fds1 s s1 m m1,
      uncurry_fundefs_step fds s m fds1 s1 m1 ->
      uncurry_fundefs_step (Fcons f t args e fds) s m (Fcons f t args e fds1) s1 m1
  | uncurry_fundefs_e : forall f t args e e1 fds s s1 m m1,
      uncurry_step e s m e1 s1 m1 ->
      uncurry_fundefs_step (Fcons f t args e fds) s m (Fcons f t args e1 fds) s1 m1
  | uncurry_fundefs_g : forall e e1 f ft k kt fv g gt gv fds s s1 m m1,
      uncurry_step e s m e1 s1 m1 ->
      uncurry_fundefs_step
        (Fcons f ft (k :: fv) (Efun (Fcons g gt gv e  Fnil) (Eapp k kt [g])) fds) s m
        (Fcons f ft (k :: fv) (Efun (Fcons g gt gv e1 Fnil) (Eapp k kt [g])) fds) s1 m1
  | uncurry_fundefs_curried :
      forall f f1 ft ft1 k kt fv fv1
             g gt gv gv1 ge fds s m s',
      match M.get g m with Some true => true | _ => false end = false ->
      occurs_in_exp g ge = false ->
      occurs_in_exp k ge = false ->
      fresh_copies s gv1 ->
      length gv1 = length gv ->
      fresh_copies (s :|: FromList gv1) fv1 ->
      length fv1 = length fv ->
      ~(In _ (s :|: FromList gv1 :|: FromList fv1) f1) ->
      s' <--> s :|: FromList gv1 :|: FromList fv1 :|: [set f1] ->
      uncurry_fundefs_step 
        (Fcons f ft (k :: fv) (Efun (Fcons g gt gv ge Fnil) (Eapp k kt [g])) fds) s m
        (Fcons f ft (k :: fv1)
           (Efun (Fcons g gt gv1 (Eapp f1 ft1 (gv1 ++ fv1)) Fnil) (Eapp k kt [g]))
           (Fcons f1 ft1 (gv ++ fv) ge fds))
        s' 
        (M.set g true m).
        (* TODO: restrict ft1? *)

  Hint Constructors uncurry_step.
  Hint Constructors uncurry_fundefs_step.

  Scheme uncurry_step_mut := Minimality for uncurry_step Sort Prop
  with uncurry_step_fundefs_mut := Minimality for uncurry_fundefs_step Sort Prop.

  Ltac uncurry_step_induction P Q IHuncurry IH :=
    apply uncurry_step_mut with (P := P) (P0 := Q);
    [ intros ? ? ? ? ? ? ? ? ? IHuncurry IH
    | intros ? ? ? ? ? ? ? ? ? IHuncurry IH
    | intros ? ? ? ? ? ? ? ? IHuncurry IH
    | intros ? ? ? ? ? ? ? ? ? ? IHuncurry IH
    | intros ? ? ? ? ? ? ? ? ? IHuncurry IH
    | intros ? ? ? ? ? ? ? IHuncurry IH
    | intros ? ? ? ? ? ? ? IHuncurry IH
    | intros ? ? ? ? ? ? ? ? ? ? IHuncurry IH
    | intros ? ? ? ? ? ? ? ? ? ? IHuncurry IH
    | intros ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? IHuncurry IH
    | intros
    ].

  Ltac uncurry_fundefs_step_induction P Q IHuncurry IH :=
    apply uncurry_step_mut with (P := P) (P0 := Q);
    [ intros ? ? ? ? ? ? ? ? ? IHuncurry IH
    | intros ? ? ? ? ? ? ? ? ? IHuncurry IH
    | intros ? ? ? ? ? ? ? ? IHuncurry IH
    | intros ? ? ? ? ? ? ? ? ? ? IHuncurry IH
    | intros ? ? ? ? ? ? ? ? ? IHuncurry IH
    | intros ? ? ? ? ? ? ? IHuncurry IH
    | intros ? ? ? ? ? ? ? IHuncurry IH
    | intros ? ? ? ? ? ? ? ? ? ? IHuncurry IH
    | intros ? ? ? ? ? ? ? ? ? ? IHuncurry IH
    | intros ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? IHuncurry IH
    | intros
    ].

  Lemma uncurry_step_mutual_ind : 
  forall (P : exp -> Ensemble var -> localMap -> exp -> Ensemble var -> localMap -> Prop)
    (P0 : fundefs -> Ensemble var -> localMap -> fundefs -> Ensemble var -> localMap -> Prop),
  (forall (x : var) (c : cTag) (args : list var) (e e1 : exp) (s s1 : Ensemble var) (m m1 : localMap),
   uncurry_step e s m e1 s1 m1 ->
   P e s m e1 s1 m1 -> P (Econstr x c args e) s m (Econstr x c args e1) s1 m1) ->
  (forall (x : var) (arms : list (cTag * exp)) (c : cTag) (e e1 : exp) (s s1 : Ensemble var)
     (m m1 : localMap),
   uncurry_step e s m e1 s1 m1 ->
   P e s m e1 s1 m1 -> P (Ecase x ((c, e) :: arms)) s m (Ecase x ((c, e1) :: arms)) s1 m1) ->
  (forall (x : var) (arms arms1 : list (cTag * exp)) (arm : cTag * exp) (s s1 : Ensemble var)
     (m m1 : localMap),
   uncurry_step (Ecase x arms) s m (Ecase x arms1) s1 m1 ->
   P (Ecase x arms) s m (Ecase x arms1) s1 m1 ->
   P (Ecase x (arm :: arms)) s m (Ecase x (arm :: arms1)) s1 m1) ->
  (forall (x : var) (c : cTag) (n : N) (y : var) (e e1 : exp) (s s1 : Ensemble var) (m m1 : localMap),
   uncurry_step e s m e1 s1 m1 -> P e s m e1 s1 m1 -> P (Eproj x c n y e) s m (Eproj x c n y e1) s1 m1) ->
  (forall (x : var) (p : prim) (args : list var) (e e1 : exp) (s s1 : Ensemble var) (m m1 : localMap),
   uncurry_step e s m e1 s1 m1 ->
   P e s m e1 s1 m1 -> P (Eprim x p args e) s m (Eprim x p args e1) s1 m1) ->
  (forall (fds : fundefs) (e e1 : exp) (s s1 : Ensemble var) (m m1 : localMap),
   uncurry_step e s m e1 s1 m1 -> P e s m e1 s1 m1 -> P (Efun fds e) s m (Efun fds e1) s1 m1) ->
  (forall (fds fds1 : fundefs) (e : exp) (s s1 : Ensemble var) (m m1 : localMap),
   uncurry_fundefs_step fds s m fds1 s1 m1 ->
   P0 fds s m fds1 s1 m1 -> P (Efun fds e) s m (Efun fds1 e) s1 m1) ->
  (forall (f6 : var) (t : fTag) (args : list var) (e : exp) (fds fds1 : fundefs) 
     (s s1 : Ensemble var) (m m1 : localMap),
   uncurry_fundefs_step fds s m fds1 s1 m1 ->
   P0 fds s m fds1 s1 m1 -> P0 (Fcons f6 t args e fds) s m (Fcons f6 t args e fds1) s1 m1) ->
  (forall (f7 : var) (t : fTag) (args : list var) (e e1 : exp) (fds : fundefs) 
     (s s1 : Ensemble var) (m m1 : localMap),
   uncurry_step e s m e1 s1 m1 ->
   P e s m e1 s1 m1 -> P0 (Fcons f7 t args e fds) s m (Fcons f7 t args e1 fds) s1 m1) ->
  (forall (e e1 : exp) (f8 : var) (ft : fTag) (k : var) (kt : fTag) (fv : list var) 
     (g : var) (gt : fTag) (gv : list var) (fds : fundefs) (s s1 : Ensemble var) 
     (m m1 : localMap),
   uncurry_step e s m e1 s1 m1 ->
   P e s m e1 s1 m1 ->
   P0 (Fcons f8 ft (k :: fv) (Efun (Fcons g gt gv e Fnil) (Eapp k kt [g])) fds) s m
     (Fcons f8 ft (k :: fv) (Efun (Fcons g gt gv e1 Fnil) (Eapp k kt [g])) fds) s1 m1) ->
  (forall (f9 f10 : var) (ft ft1 : fTag) (k : var) (kt : fTag) (fv fv1 : list var) 
     (g : positive) (gt : fTag) (gv gv1 : list var) (ge : exp) (fds : fundefs) 
     (s : Ensemble var) (m : M.t bool) (s' : Ensemble var),
   match M.get g m with
   | Some true => true
   | Some false => false
   | None => false
   end = false ->
   occurs_in_exp g ge = false ->
   occurs_in_exp k ge = false ->
   fresh_copies s gv1 ->
   length gv1 = length gv ->
   fresh_copies (s :|: FromList gv1) fv1 ->
   length fv1 = length fv ->
   ~ In var (s :|: FromList gv1 :|: FromList fv1) f10 ->
   s' <--> s :|: FromList gv1 :|: FromList fv1 :|: [set f10] ->
   P0 (Fcons f9 ft (k :: fv) (Efun (Fcons g gt gv ge Fnil) (Eapp k kt [g])) fds) s m
     (Fcons f9 ft (k :: fv1) (Efun (Fcons g gt gv1 (Eapp f10 ft1 (gv1 ++ fv1)) Fnil) (Eapp k kt [g]))
        (Fcons f10 ft1 (gv ++ fv) ge fds)) s'
     (M.set g true m)) ->
    (forall (e : exp) (e0 : Ensemble var) (l : localMap) (e1 : exp) (e2 : Ensemble var)
      (l0 : localMap), uncurry_step e e0 l e1 e2 l0 -> P e e0 l e1 e2 l0) /\
    (forall (f10 : fundefs) (e : Ensemble var) (l : localMap) (f11 : fundefs) 
      (e0 : Ensemble var) (l0 : localMap),
      uncurry_fundefs_step f10 e l f11 e0 l0 ->
      P0 f10 e l f11 e0 l0).
  Proof.
    intros. split.
    apply (uncurry_step_mut P P0); assumption.
    apply (uncurry_step_fundefs_mut P P0); assumption.
  Qed.

  (* to do proofs simultaneously *) 
  Ltac uncurry_step_induction_mut P Q IHuncurry IH :=
    apply uncurry_step_mutual_ind with (P := P) (P0 := Q);
    [ intros ? ? ? ? ? ? ? ? ? IHuncurry IH
    | intros ? ? ? ? ? ? ? ? ? IHuncurry IH
    | intros ? ? ? ? ? ? ? ? IHuncurry IH
    | intros ? ? ? ? ? ? ? ? ? ? IHuncurry IH
    | intros ? ? ? ? ? ? ? ? ? IHuncurry IH
    | intros ? ? ? ? ? ? ? IHuncurry IH
    | intros ? ? ? ? ? ? ? IHuncurry IH
    | intros ? ? ? ? ? ? ? ? ? ? IHuncurry IH
    | intros ? ? ? ? ? ? ? ? ? ? IHuncurry IH
    | intros ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? IHuncurry IH
    | intros
    ].

  Lemma preord_val_fundefs : forall pr cenv k rho rho1 fds f, 
    preord_env_P pr cenv (occurs_free_fundefs fds) k rho rho1 ->
    preord_val pr cenv k (Vfun rho fds f) (Vfun rho1 fds f).
  Proof.
    intros. rewrite preord_val_eq. simpl. intros.
    pose (Hlen := H2). apply setlist_length in Hlen. rewrite <- Hlen in H0.
    rename rho1' into rho'.
    eapply length_exists_setlist in H0. destruct H0 as [rho1' Hrho1'].
    do 3 eexists. split; [eassumption|split]; [eassumption|].

    intros Hj Hvs. apply preord_exp_refl.
    assert (preord_env_P pr cenv (occurs_free_fundefs fds :|: name_in_fundefs fds) j
                         (def_funs fds fds rho rho)
                         (def_funs fds fds rho1 rho1)). {
      apply preord_env_P_monotonic with (k := k). omega.
      apply preord_env_P_def_funs_cor.
      eapply preord_env_P_antimon.
      eassumption.
      auto with Ensembles_DB.
    }
    clear H.
    eapply preord_env_P_setlist_l; [eassumption| |eassumption|eauto|eauto].

    apply find_def_correct in H1.
    assert (occurs_free e1 \\ FromList xs1 \subset occurs_free_fundefs fds :|: name_in_fundefs fds). {
      apply occurs_free_in_fun in H1.
      apply Setminus_Included_Included_Union.
      rewrite Union_commut.
      now rewrite Union_commut with (s1 := occurs_free_fundefs fds).
    }

    intros. assert ((occurs_free e1 \\ FromList xs1) x) by (now split).
    now apply H.
  Qed.

  Lemma Union_Included_subst : forall {A} (a : Ensemble A) b b' c,
    a \subset b :|: c -> b \subset b' -> a \subset b' :|: c.
  Proof with eauto with Ensembles_DB.
    intros A a b b' c Hb Hb' x Hx.
    destruct Hb with (x := x)...
  Qed.

  Lemma name_in_fundefs_bound_var_fundefs : forall fds,
    name_in_fundefs fds \subset bound_var_fundefs fds.
  Proof with auto.
    induction fds; [|simpl;auto with Ensembles_DB].
    inversion 1; subst.
    - inversion H0; subst...
    - apply IHfds in H0...
  Qed.

  Lemma preord_env_P_union_converse : forall pr cenv A B k rho rho1,
    preord_env_P pr cenv (A :|: B) k rho rho1 ->
    preord_env_P pr cenv A k rho rho1 /\
    preord_env_P pr cenv B k rho rho1.
  Proof.
    split; intros a Hin; apply H; [now left|now right].
  Qed.

  Definition ctx_preord_exp (k : nat) (e e1 : exp) := forall rho rho1 pr cenv,
    preord_env_P pr cenv (occurs_free e) k rho rho1 ->
    preord_exp pr cenv k (e, rho) (e1, rho1).

  Lemma preord_env_P_setlist_extend: forall pr cenv k vs vs1 vs2 P rho1 rho2 rho1' rho2',
    preord_env_P pr cenv (P \\ FromList vs) k rho1 rho2 ->
    Some rho1' = setlist vs vs1 rho1 ->
    Some rho2' = setlist vs vs2 rho2 ->
    Forall2 (preord_val pr cenv k) vs1 vs2 ->
    preord_env_P pr cenv P k rho1' rho2'.
  Proof.
    induction vs; intros vs1 vs2 P rho1 rho2 rho1' rho2' Hrho Hrho1' Hrho2' Hvs1_vs2.
    - destruct vs1; [|apply setlist_length in Hrho1'; discriminate].
      destruct vs2; [|apply setlist_length in Hrho2'; discriminate].
      inv Hrho1'; inv Hrho2'.
      eapply preord_env_P_antimon; [apply Hrho|].
      intros a Ha; split; [apply Ha|inversion 1].
    - destruct vs1; [apply setlist_length in Hrho1'; discriminate|].
      destruct vs2; [apply setlist_length in Hrho2'; discriminate|].
      simpl in Hrho1', Hrho2'.
      destruct (setlist vs vs1 rho1) as [rho3|] eqn:Hrho3; [|congruence].
      destruct (setlist vs vs2 rho2) as [rho4|] eqn:Hrho4; [|congruence].
      inv Hrho1'; inv Hrho2'.
      apply preord_env_P_extend; [|now inv Hvs1_vs2].
      eapply IHvs; [|eauto|eauto|now inv Hvs1_vs2].
      eapply preord_env_P_antimon; [apply Hrho|].
      intros a' Ha'; split; [inv Ha'; now inv H|];
        intros contra; inv contra;
        [inv Ha'; inv H; contradiction H2; easy|inv Ha'; inv H0; contradiction].
  Qed.

  Lemma preord_env_P_setlist_extend': forall pr cenv k vs vs1 vs2 P rho1 rho2 rho1' rho2',
    preord_env_P pr cenv P k rho1 rho2 ->
    Some rho1' = setlist vs vs1 rho1 ->
    Some rho2' = setlist vs vs2 rho2 ->
    Forall2 (preord_val pr cenv k) vs1 vs2 ->
    preord_env_P pr cenv P k rho1' rho2'.
  Proof with eauto with Ensembles_DB.
    induction vs; intros vs1 vs2 P rho1 rho2 rho1' rho2' Hrho Hrho1' Hrho2' Hvs1_vs2.
    - destruct vs1; [|apply setlist_length in Hrho1'; discriminate].
      destruct vs2; [|apply setlist_length in Hrho2'; discriminate].
      inv Hrho1'; inv Hrho2'.
      eapply preord_env_P_antimon...
    - destruct vs1; [apply setlist_length in Hrho1'; discriminate|].
      destruct vs2; [apply setlist_length in Hrho2'; discriminate|].
      simpl in Hrho1', Hrho2'.
      destruct (setlist vs vs1 rho1) as [rho3|] eqn:Hrho3; [|congruence].
      destruct (setlist vs vs2 rho2) as [rho4|] eqn:Hrho4; [|congruence].
      inv Hrho1'; inv Hrho2'.
      apply preord_env_P_extend; [|now inv Hvs1_vs2].
      eapply IHvs; [|eauto|eauto|now inv Hvs1_vs2].
      eapply preord_env_P_antimon...
  Qed.

  Lemma preord_env_P_subst : forall pr cenv P k rho rho1 rho' rho1',
    preord_env_P pr cenv P k rho rho1 ->
    (forall a, P a -> M.get a rho = M.get a rho') ->
    (forall a, P a -> M.get a rho1 = M.get a rho1') ->
    preord_env_P pr cenv P k rho' rho1'.
  Proof.
    intros pr cenv P k rho rho1 rho' rho1' Heq Hrho Hrho1 a Ha v1 Hv1.
    rewrite <- Hrho in Hv1; [|apply Ha].
    rewrite <- Hrho1; [|apply Ha].
    now apply Heq.
  Qed.

  Lemma setlist_set_permut : forall {A} x (y : A) xs ys rho rho',
    ~ List.In x xs ->
    Some rho' = setlist xs ys (M.set x y rho) -> exists rho1,
    Some rho1 = setlist xs ys rho /\ forall a,
    M.get a rho' = M.get a (M.set x y rho1).
  Proof.
    intros A x y xs ys rho rho' Hx Hrho.
    assert (Hrho1 : length xs = length ys) by now apply setlist_length in Hrho.
    eapply length_exists_setlist in Hrho1; destruct Hrho1 as [rho1 Hrho1].
    exists rho1; split; [apply Hrho1|].
    intros a.
    split_var_in_list a xs.
    - assert (forall A (l : list A), Forall2 eq l l) by (induction l; auto); specialize H with (l := ys).
      symmetry in Hrho, Hrho1.
      destruct (setlist_Forall2_get _ _ _ _ _ _ _ _ _ H Hrho Hrho1 i)
        as [v1 [v2 [Hv1 [Hv2 Hv1_v2]]]]; subst.
      rewrite M.gso.
      transitivity (Some v2); auto.
      intros Ha; contradiction Hx; now subst.
    - erewrite <- setlist_not_In; [|symmetry in Hrho; apply Hrho|assumption].
      split_var_eq a x; [subst; now do 2 rewrite M.gss|].
      do 2 (rewrite M.gso; [|assumption]).
      erewrite <- setlist_not_In with (rho'0 := rho1); eauto.
  Qed.

  Lemma Forall2_preord_val_monotonic : forall pr cenv k k1 l1 l2,
    k1 <= k ->
    Forall2 (preord_val pr cenv k) l1 l2 ->
    Forall2 (preord_val pr cenv k1) l1 l2.
  Proof.
    induction l1; [now inversion 2|intros].
    destruct l2; inv H0.
    constructor; [|now apply IHl1].
    eapply preord_val_monotonic; eassumption.
  Qed.

  Lemma preord_var_env_extend_neq_r : forall pr cenv k rho rho1 a b v,
    preord_var_env pr cenv k rho rho1 a a ->
    a <> b ->
    preord_var_env pr cenv k rho (M.set b v rho1) a a.
  Proof.
    unfold preord_var_env; intros.
    rewrite M.gso; auto.
  Qed.
  Lemma def_funs_get_neq : forall B' B B1 rho a,
    ~ In _ (name_in_fundefs B') a ->
    M.get a (def_funs B1 (fundefs_append B' B) rho rho) =
    M.get a (def_funs B1 B rho rho).
  Proof.
    induction B'.
    - intros; simpl.
      rewrite M.gso.
      apply IHB'; intros contra; contradiction H; now right.
      intros contra; subst; contradiction H; now left.
    - auto.
  Qed.
  Lemma preord_var_env_def_funs_neq : forall pr cenv k B' B B1 B2 B3 rho rho1 a,
    preord_var_env pr cenv k
                   (def_funs B2 B rho rho)
                   (def_funs B3 B1 rho1 rho1) a a ->
    ~ In _ (name_in_fundefs B') a ->
    preord_var_env pr cenv k
                   (def_funs B2 (fundefs_append B' B) rho rho)
                   (def_funs B3 (fundefs_append B' B1) rho1 rho1) a a.
  Proof.
    intros.
    unfold preord_var_env.
    do 2 (rewrite def_funs_get_neq; auto).
  Qed.

  Lemma Ensemble_In : forall {U : Type} S a,
    In U S a -> S a.
  Proof. auto. Qed.

  Lemma preord_var_env_extend' : forall pr cenv rho1 rho2 k x y v1 v2,
    (y <> x -> preord_var_env pr cenv k rho1 rho2 y y) ->
    preord_val pr cenv k v1 v2 ->
    preord_var_env pr cenv k (M.set x v1 rho1) (M.set x v2 rho2) y y.
  Proof.
    intros.
    unfold preord_var_env.
    split_var_eq y x; subst.
    do 2 rewrite M.gss; intros v0 Hv0; inv Hv0; eexists; split; eauto.
    do 2 (rewrite M.gso; auto).
    now apply H.
  Qed.

  Lemma find_def_fundefs_append_eq : forall f B B1,
    name_in_fundefs B f ->
    find_def f (fundefs_append B B1) = find_def f B.
  Proof.
    induction B.
    - intros; simpl.
      destruct (M.elt_eq f v); subst; auto.
      rewrite IHB; auto.
      inv H; auto.
      now inv H0.
    - inversion 1.
  Qed.

  Lemma find_def_fundefs_append_neq : forall f B B1,
    ~ name_in_fundefs B f ->
    find_def f (fundefs_append B B1) = find_def f B1.
  Proof.
    induction B.
    - intros; simpl.
      destruct (M.elt_eq f v); subst.
      contradiction H; now left.
      apply IHB; intros contra.
      contradiction H; now right.
    - auto.
  Qed.

  Lemma occurs_free_fundefs_append : forall fds1 fds a,
    ~ In _ (name_in_fundefs fds1) a ->
    occurs_free_fundefs fds a ->
    occurs_free_fundefs (fundefs_append fds1 fds) a.
  Proof.
    induction fds1.
    intros fds a Ha Hfds.
    simpl; apply Free_Fcons2.
    apply IHfds1; auto.
    intros contra; contradiction Ha.
    now right.
    intros contra; subst; contradiction Ha; now left.
    auto.
  Qed.

  Lemma occurs_free_fundefs_append_l : forall fds1 fds a,
    ~ In _ (name_in_fundefs fds) a ->
    occurs_free_fundefs fds1 a ->
    occurs_free_fundefs (fundefs_append fds1 fds) a.
  Proof.
    induction fds1.
    intros fds a Ha Hfds.
    inv Hfds.
    constructor; auto.
    intros contra.
    assert (In _ (name_in_fundefs (fundefs_append fds1 fds)) a) by auto.
    rewrite fundefs_append_name_in_fundefs in H; [|reflexivity].
    inv H; contradiction.
    apply Free_Fcons2; auto.
    inversion 2.
  Qed.

  Lemma find_def_fundefs_append_neq_l: forall (f : var) (B B1 : fundefs),
    unique_bindings_fundefs (fundefs_append B B1) ->
    ~ name_in_fundefs B1 f ->
    find_def f (fundefs_append B B1) = find_def f B.
  Proof.
    induction B.
    intros B1 Huniq Hname.
    simpl.
    destruct (M.elt_eq f v); auto.
    inv Huniq.
    apply IHB; auto.
    intros.
    rewrite name_not_in_fundefs_find_def_None; auto.
  Qed.

  Lemma fundefs_append_unique : forall (f : var) (B B1 : fundefs),
    unique_bindings_fundefs (fundefs_append B B1) ->
    name_in_fundefs B1 f ->
    ~ name_in_fundefs B f.
  Proof.
    induction B.
    intros B1 Huniq Hname.
    intros contra.
    inv contra.
    inv H.
    inv Huniq.
    contradiction H5.
    apply Ensemble_In; erewrite fundefs_append_bound_vars; [|reflexivity]; right.
    now apply name_in_fundefs_bound_var_fundefs.
    inv Huniq.
    unfold not in IHB; eapply IHB; eauto.
    inversion 3.
  Qed.

  Lemma fundefs_append_unique_l : forall (f : var) (B1 B : fundefs),
    unique_bindings_fundefs (fundefs_append B1 B) ->
    name_in_fundefs B1 f ->
    ~ name_in_fundefs B f.
  Proof.
    induction B1.
    intros B Huniq Hname.
    intros contra.
    inv Hname.
    inv H.
    inv Huniq.
    contradiction H5.
    apply Ensemble_In; erewrite fundefs_append_bound_vars; [|reflexivity]; right.
    now apply name_in_fundefs_bound_var_fundefs.
    inv Huniq.
    unfold not in IHB1; eapply IHB1; eauto.
    inversion 2.
  Qed.

  Lemma fundefs_append_unique_and : forall B B1,
    unique_bindings_fundefs (fundefs_append B B1) ->
    unique_bindings_fundefs B /\ unique_bindings_fundefs B1.
  Proof.
    induction B.
    intros B1 Huniq; split.
    inv Huniq.
    constructor; auto.
    intros contra.
    contradiction H5; apply Ensemble_In; rewrite fundefs_append_bound_vars; [|reflexivity].
    now left.
    eapply Disjoint_Included_l; eauto.
    intros a Ha; rewrite fundefs_append_bound_vars; [|reflexivity]; now left.
    eapply Disjoint_Included_r; eauto.
    intros a Ha; rewrite fundefs_append_bound_vars; [|reflexivity]; now left.
    edestruct IHB; eauto.
    inv Huniq.
    edestruct IHB; eauto.
    split; auto.
    constructor.
  Qed.

  (* unnesting fundefs_curried case of uncurry_step_correct *)
  Lemma uncurry_step_correct_fundefs_curried :
    forall pr cenv k e f ft k0 kt fv g gt gv ge pre_fds fds f1 ft1 fv1 gv1 s rho rho1 already_uncurried,
    let curried := fundefs_append pre_fds
        (Fcons f ft (k0 :: fv) (Efun (Fcons g gt gv ge Fnil) (Eapp k0 kt [g])) fds) in
    let uncurried := fundefs_append pre_fds
        (Fcons f ft (k0 :: fv1)
                (Efun (Fcons g gt gv1 (Eapp f1 ft1 (gv1 ++ fv1)) Fnil) (Eapp k0 kt [g]))
                (Fcons f1 ft1 (gv ++ fv) ge fds)) in
    (used_vars e :|: used_vars_fundefs curried \subset s) ->
    (used_vars e :|: used_vars_fundefs uncurried \subset
       s :|: FromList gv1 :|: FromList fv1 :|: [set f1]) ->
    (match M.get g already_uncurried with
         | Some true => true | Some false => false | None => false end
     = false) ->
    (occurs_in_exp g ge = false) ->
    (occurs_in_exp k0 ge = false) ->
    (unique_bindings_fundefs curried) ->
    (used_vars_fundefs curried \subset s) ->
    (unique_bindings_fundefs uncurried) ->
    (fresh_copies s gv1) ->
    (length gv1 = length gv) ->
    (fresh_copies (s :|: FromList gv1) fv1) ->
    (length fv1 = length fv) ->
    (~ In var (s :|: FromList gv1 :|: FromList fv1) f1) ->
    (preord_env_P pr cenv (occurs_free (Efun curried e)) k rho rho1) ->
    preord_exp pr cenv k (Efun curried e, rho) (Efun uncurried e, rho1).
  Proof with unfold used_vars in *; eauto 15 with Ensembles_DB.
    intros pr cenv k e f ft k0 kt fv g gt gv ge pre_fds fds f1 ft1 fv1 gv1 s rho rho1
           already_uncurried curried uncurried
           Hcurried_used Huncurried_used Halready_uncurried
           Hg_nonrec Hk0_nonrec Hcurried_unique_fundefs Hcurried_used_fundefs
           Huncurried_unique_fundefs Hgv1_fresh Hgv_gv1 Hfv1_fresh Hfv_fv1 Hf1_fresh Henv.
    apply preord_exp_fun_compat.
    apply preord_exp_refl.
    intros h Hh; unfold preord_var_env.

    (* useful facts for later *)
    assert (Hf1_gv1 : ~ List.In f1 gv1). {
      rewrite Union_demorgan in Hf1_fresh; destruct Hf1_fresh as [Hf1_fresh2 Hf1_fresh3].
      rewrite Union_demorgan in Hf1_fresh2; destruct Hf1_fresh2 as [Hf1_fresh1 Hf1_fresh2].
      assumption.
    }
    assert (Hf1_k0fv1 : ~ List.In f1 (k0 :: fv1)). {
      rewrite Union_demorgan in Hf1_fresh; destruct Hf1_fresh as [Hf1_fresh2 Hf1_fresh3].
      rewrite Union_demorgan in Hf1_fresh2; destruct Hf1_fresh2 as [Hf1_fresh1 Hf1_fresh2].
      intros contra; inv contra; [|contradiction].
      apply fundefs_append_unique_and in Huncurried_unique_fundefs.
      destruct Huncurried_unique_fundefs as [HL HR].
      inv HR. inv H7. contradiction (H f1).
      split.
      constructor; now left.
      now left.
    }
    assert (Hg_f1 : g <> f1). {
      intros contra; subst.
      apply fundefs_append_unique_and in Huncurried_unique_fundefs.
      destruct Huncurried_unique_fundefs as [HL HR].
      inv HR. inv H8.
      contradiction (H f1).
      split.
      constructor; constructor; now left.
      constructor; now left.
    }
    assert (f_f1 : f <> f1). {
      intros contra; subst.
      apply fundefs_append_unique_and in Huncurried_unique_fundefs.
      destruct Huncurried_unique_fundefs as [HL HR].
      inv HR. contradiction H5; constructor; now left.
    }
    assert (Hk0_fv1 : ~ List.In k0 fv1). {
      intros contra.
      apply fundefs_append_unique_and in Huncurried_unique_fundefs.
      destruct Huncurried_unique_fundefs as [HL HR].
      inv HR. now inv H10.
    }
    assert (Hg_fv1 : ~ List.In g fv1). {
      intros contra.
      apply fundefs_append_unique_and in Huncurried_unique_fundefs.
      destruct Huncurried_unique_fundefs as [HL HR].
      inv HR.
      inv H6.
      contradiction (H g).
      split.
      constructor; constructor; now left.
      now right.
    }
    assert (Hk0_g : k0 <> g). {
      intros contra; subst.
      apply fundefs_append_unique_and in Hcurried_unique_fundefs.
      destruct Hcurried_unique_fundefs as [HL HR].
      inv HR.
      inv H6. contradiction (H g).
      split.
      constructor; constructor; now left.
      now left.
    }
    assert (Hf1_pre_fds : ~ name_in_fundefs pre_fds f1). {
      intros contra.
      apply fundefs_append_unique_l with (f := f1) in Huncurried_unique_fundefs; auto.
      contradiction Huncurried_unique_fundefs.
      right; now left.
    }
    assert (Hf_pre_fds : ~ name_in_fundefs pre_fds f). {
      intros contra.
      apply fundefs_append_unique_l with (f := f) in Hcurried_unique_fundefs; auto.
      contradiction Hcurried_unique_fundefs.
      now left.
    }
    assert (Hcurried_uncurried : name_in_fundefs curried \subset name_in_fundefs uncurried). {
      intros a Ha.
      rewrite fundefs_append_name_in_fundefs; [|reflexivity].
      split_var_in_fundefs a pre_fds Ha_pre_fds.
      now left.
      split_var_eq a f; subst.
      right; now left.
      split_var_in_fundefs a fds Ha_fds.
      right; right; now right.
      rewrite fundefs_append_name_in_fundefs in Ha; [|reflexivity].
      inv Ha; try contradiction.
      inv H; try contradiction.
      inv H0; contradiction.
    }
    assert (Hgv_g : ~ List.In g gv). {
      intros contra.
      apply fundefs_append_unique_and in Hcurried_unique_fundefs.
      destruct Hcurried_unique_fundefs as [HL HR].
      inv HR.
      inv H11.
      now inv H2.
    }
    assert (Hpre_fds_curried : name_in_fundefs pre_fds \subset name_in_fundefs curried). {
      subst curried; intros a Ha.
      rewrite fundefs_append_name_in_fundefs; [|reflexivity]; now left.
    }
    assert (Hpre_fds_uncurried : name_in_fundefs pre_fds \subset name_in_fundefs uncurried). {
      subst uncurried; intros a Ha.
      rewrite fundefs_append_name_in_fundefs; [|reflexivity]; now left.
    }
    assert (Hf1_ge : ~ In _ (occurs_free ge) f1). {
      intros contra1.
      rewrite Union_demorgan in Hf1_fresh; destruct Hf1_fresh as [Hf1_fresh2 Hf1_fresh3];
      rewrite Union_demorgan in Hf1_fresh2; destruct Hf1_fresh2 as [Hf1_fresh1 Hf1_fresh2].
      contradiction Hf1_fresh1.
      apply Hcurried_used; right; right.
      subst curried; apply occurs_free_fundefs_append; auto.
      constructor; auto.
      inversion 1; subst.
      - apply fundefs_append_unique_and in Huncurried_unique_fundefs.
        destruct Huncurried_unique_fundefs as [HL HR].
        inv HR.
        inv H8; contradiction (H0 f1).
        split; [constructor; now left|now left].
      - apply fundefs_append_unique_and in Huncurried_unique_fundefs.
        destruct Huncurried_unique_fundefs as [HL HR].
        inv HR.
        inv H14.
        contradiction H20.
        apply Ensemble_In; rewrite FromList_app.
        now right.
      - apply fundefs_append_unique_and in Huncurried_unique_fundefs.
        destruct Huncurried_unique_fundefs as [HL HR].
        inv HR.
        inv H12.
        intros contra; contradiction H14; now apply name_in_fundefs_bound_var_fundefs.
      - apply Free_Efun2.
        constructor; auto; [|inversion 1].
        intros contra.
        apply fundefs_append_unique_and in Huncurried_unique_fundefs.
        destruct Huncurried_unique_fundefs as [HL HR].
        inv HR.
        inv H12.
        contradiction H18; apply Ensemble_In; rewrite FromList_app; now left.
    }
    assert (Hf1_curried : ~ In _ (name_in_fundefs curried) f1). {
      intros contra.
      rewrite Union_demorgan in Hf1_fresh; destruct Hf1_fresh as [Hf1_fresh2 Hf1_fresh3];
      rewrite Union_demorgan in Hf1_fresh2; destruct Hf1_fresh2 as [Hf1_fresh1 Hf1_fresh2].
      contradiction Hf1_fresh1.
      apply Hcurried_used; right; left.
      now apply name_in_fundefs_bound_var_fundefs.
    }
    assert (Hf_curried : In _ (name_in_fundefs curried) f). {
      rewrite fundefs_append_name_in_fundefs; [|reflexivity].
      right; now left.
    }
    assert (Hf_uncurried : In _ (name_in_fundefs uncurried) f) by now apply Hcurried_uncurried.

    split_var_in_fundefs
      h
      curried 
      Hfds; clear Hfds; rename n into Hfds; simpl in Hfds.
    - (* h\in pre_fds ++ f |: fundefs(fds) *)
      rewrite def_funs_eq; auto.
      rewrite def_funs_eq; [|now apply Hcurried_uncurried].
      intros v1 Hv1; inv Hv1.
      eexists; split; [reflexivity|].
      generalize dependent h. generalize dependent e.
      induction k as [k IHk] using lt_wf_rec1.
      Opaque preord_exp.
      intros e Hcurried_used Huncurried_used Henv h Hh Hfds.
      split_var_eq h f; subst; rewrite preord_val_eq; simpl.
      + (* h = f *)
        rename curried into curried'; pose (curried := curried').
        rename uncurried into uncurried'; pose (uncurried := uncurried').
        subst curried'; subst uncurried'.
        do 2 (rewrite find_def_fundefs_append_neq; auto; simpl).
        destruct (M.elt_eq f f) as [Heq|]; [clear Heq|contradiction].
        intros vs1 vs2 k1 t xs1 e1 rho' Hlen_vs1_vs2 Hsome Hrho'; inv Hsome.
        assert (Hrho1' : length (k0 :: fv1) = length vs2). {
          apply setlist_length in Hrho'.
          rewrite <- Hlen_vs1_vs2.
          rewrite <- Hrho'.
          simpl; rewrite Hfv_fv1.
          reflexivity.
        }
        eapply length_exists_setlist in Hrho1'.
        destruct Hrho1' as [rho1' Hrho1'].
        do 3 eexists; split; [reflexivity|split]; [eassumption|intros Hk1 Hvs1_vs2].
        apply preord_exp_fun_compat.
        apply preord_exp_refl.
        (* wrt k0 and g, the environments
             rho'' = g + [k0 :: fv -> vs1] + curried f + fds + rho
             rho1'' = uncurried g + [k0 :: fv1 -> vs2] + uncurried f + f1 + fds + rho1
           agree. *)
        destruct vs1 as [|hvs1 tvs1]; [apply setlist_length in Hrho'; inv Hrho'|].
        destruct vs2 as [|hvs2 tvs2]; [apply setlist_length in Hrho1'; inv Hrho1'|].
        intros a Ha.
        inv Ha; [rename a into k0|inv H3]; [|rename a into g|inv H].
        * (* k0: hvs1 == hvs2 *)
          unfold preord_var_env; simpl.
          do 2 (rewrite M.gso; [|assumption]).
          apply set_setlist in Hrho'; destruct Hrho' as [rho'k0 [Hrho' Hrho'k0]].
          apply set_setlist in Hrho1'; destruct Hrho1' as [rho1'k0 [Hrho1' Hrho1'k0]].
          subst rho'; subst rho1'; do 2 rewrite M.gss.
          intros v1 Hv1; inv Hv1; eexists; split; [reflexivity|now inv Hvs1_vs2].
        * (* g *)
          unfold preord_var_env; simpl.
          do 2 rewrite M.gss.
          intros v1 Hv1; inv Hv1; eexists; split; [reflexivity|].
          rewrite preord_val_eq; simpl.
          destruct (M.elt_eq g g) as [Heq|]; [clear Heq|contradiction].
          intros vs3 vs4 k2 t0 xs1 e1 rho'' Hlen_vs3_vs4 Hsome Hrho''.
          inversion Hsome; subst t0; subst xs1; subst e1; clear Hsome.
          assert (Hrho1'' : length gv1 = length vs4). {
            apply setlist_length in Hrho''.
            rewrite <- Hlen_vs3_vs4.
            rewrite <- Hrho''.
            assumption.
          }
          eapply length_exists_setlist in Hrho1''; destruct Hrho1'' as [rho1'' Hrho1''].
          do 3 eexists; split; [reflexivity|split]; [eassumption|intros Hk2 Hvs3_vs4].
          assert (Hrho''' : length (gv ++ fv) = length (vs4 ++ tvs2)). {
            do 2 rewrite app_length.
            apply setlist_length in Hrho1''.
            rewrite <- Hrho1''.
            rewrite <- Hgv_gv1.
            apply setlist_length in Hrho1'.
            inv Hrho1'.
            rewrite <- Hfv_fv1.
            reflexivity.
          }
          Transparent preord_exp. intros v1 c1 Hc1 Hv1. 
          apply length_exists_setlist with
            (rho0 := (def_funs uncurried uncurried rho1 rho1)) in Hrho'''.
          destruct Hrho''' as [rho''' Hrho'''].
          assert (Hgoal : preord_exp pr cenv k2 (ge, rho'') (ge, rho''')). {
            apply preord_exp_refl.
            (* wrt free variables of ge, the environments
                 rho'' = [gv -> vs3] + g + [k0 :: fv -> vs1] + curried f + fds + rho
                 rho''' = [gv ++ fv -> vs4 ++ tvs2] + uncurried f + f1 + fds + rho1
               agree. 
             *)

            (* rho''g := rho'' \ g *)
            eapply setlist_set_permut in Hgv_g; [|apply Hrho''].
            destruct Hgv_g as [rho''g [Hrho''g Hrho''_rho''g]].
            eapply preord_env_P_subst; [|intros a Ha;symmetry; apply Hrho''_rho''g|reflexivity]. 
            apply preord_env_P_set_not_in_P_l;
              [|apply Disjoint_Union_r with (s1 := bound_var ge);
                replace (bound_var ge :|: occurs_free ge) with (used_vars ge) by reflexivity;
                now rewrite <- occurs_in_exp_correct].

            (* split [gv ++ fv -> vs4 ++ tvs2] into [gv -> vs4] + [fv -> tvs2] *)
            symmetry in Hrho'''; eapply setlist_app in Hrho''';
              [|apply setlist_length in Hrho1''; now rewrite <- Hrho1''].
            destruct Hrho''' as [rho'''fv [Hrho'''fv Hrho''']].

            (* [[gv]](rho''g) ==_k2 [[gv]](rho''') *)
            eapply preord_env_P_setlist_extend; eauto.

            (* rho'k0 := rho' \ k0 *)
            eapply set_setlist in Hrho'; destruct Hrho' as [rho'k0 [Hrho' Hrho'k0]]; subst rho'.
            apply preord_env_P_set_not_in_P_l;
              [|eapply Disjoint_Included_l;
                  [|rewrite <- occurs_in_exp_correct];
                  [|apply Hk0_nonrec];
                apply Setminus_Included_preserv;
                eapply Included_Union_r].

            (* [[fv]](rho'k0) ==_k2 [[gv]](rho''') *)
            inv Hvs1_vs2.
            eapply preord_env_P_setlist_extend; eauto;
              [|eapply Forall2_preord_val_monotonic];
              [| |eassumption];
              [|omega].

            intros a Ha.
            (* remove pre_fds from (pre_fds + curried f + fds + rho),
                                   (pre_fds + f + f1 + fds + rho1) *)
            split_var_in_fundefs a pre_fds Hpre_fds. {
              unfold preord_var_env.
              rewrite def_funs_eq; [|now apply Hpre_fds_curried].
              rewrite def_funs_eq; [|now apply Hpre_fds_uncurried].
              intros v0 Hv0; inv Hv0; eexists; split; [reflexivity|].
              apply IHk with (e := Ehalt a); [omega| | | |constructor| ].
              * rewrite Union_Same_set; [assumption|].
                unfold used_vars.
                rewrite bound_var_Ehalt.
                rewrite Union_Empty_set_neut_l.
                intros a' Ha'; inv Ha'; left.
                rewrite fundefs_append_bound_vars; [|reflexivity]; left.
                now apply name_in_fundefs_bound_var_fundefs.
              * unfold used_vars.
                rewrite bound_var_Ehalt.
                rewrite Union_Empty_set_neut_l.
                rewrite Union_Same_set; [eapply Union_Included_r; eassumption|].
                intros a' Ha'; inv Ha'; left.
                rewrite fundefs_append_bound_vars; [|reflexivity]; left.
                now apply name_in_fundefs_bound_var_fundefs.
              * eapply preord_env_P_antimon.
                eapply preord_env_P_monotonic; [|eassumption]; omega.
                intros a' Ha'; inv Ha'.
                inv H5; contradiction H1.
                apply Ensemble_In.
                rewrite fundefs_append_name_in_fundefs; [|reflexivity]; now left.
                now apply Free_Efun2.
              * apply Ensemble_In.
                rewrite fundefs_append_name_in_fundefs; [|reflexivity]; now left.
            }
            rename uncurried into uncurried'; pose (uncurried := uncurried'); subst uncurried'.
            apply preord_var_env_def_funs_neq; auto.

            (* remove curried f, uncurried f *)
            simpl; apply preord_var_env_extend'. intros Ha_f.

            (* remove f1 *)
            apply preord_var_env_extend_neq_r.

            (* remove fds *) {
            rename Hfds into Hname_fds.
            split_var_in_fundefs a fds Hfds.
            - unfold preord_var_env.
              do 2 (rewrite def_funs_eq; [|assumption]).
              intros v0 Hv0; inv Hv0; eexists; split; [reflexivity|].
              apply IHk with (e := Ehalt a); [omega| | | |constructor|].
              * rewrite Union_Same_set; [assumption|].
                unfold used_vars.
                rewrite bound_var_Ehalt.
                rewrite Union_Empty_set_neut_l.
                intros a' Ha'; inv Ha'; left.
                rewrite fundefs_append_bound_vars; [|reflexivity].
                right; apply Bound_Fcons2.
                now apply name_in_fundefs_bound_var_fundefs.
              * unfold used_vars.
                rewrite bound_var_Ehalt.
                rewrite Union_Empty_set_neut_l.
                rewrite Union_Same_set; [eapply Union_Included_r; eassumption|].
                intros a' Ha'; inv Ha'; left.
                rewrite fundefs_append_bound_vars; [|reflexivity].
                right; do 2 apply Bound_Fcons2.
                now apply name_in_fundefs_bound_var_fundefs.
              * eapply preord_env_P_antimon.
                eapply preord_env_P_monotonic; [|eassumption]; omega.
                intros a' Ha'; inv Ha'.
                inv H5; contradiction H1.
                apply Ensemble_In; rewrite fundefs_append_name_in_fundefs; [|reflexivity].
                right; now right.
                now apply Free_Efun2.
              * apply Ensemble_In; rewrite fundefs_append_name_in_fundefs; [|reflexivity].
                right; now right.
            - unfold preord_var_env.
              do 2 (rewrite def_funs_neq; auto).
              assert ((occurs_free ge
                                   \\ FromList gv
                                   \\ FromList fv
                                   \\ [set f]
                                   \\ name_in_fundefs pre_fds
                                   \\ name_in_fundefs fds) a). {
                do 3 (split; auto).
                intros contra; now inv contra.
              }
              clear Ha; clear n; clear Ha_f; clear n0; generalize dependent a.
              eapply preord_env_P_antimon.
              eapply preord_env_P_monotonic; [|eassumption]; omega.
              intros a Ha; inv Ha; inv H; inv H1; inv H.
              apply Free_Efun2.
              apply occurs_free_fundefs_append; auto.
              apply Free_Fcons1;
                [intros contra; subst; now contradiction H5| |assumption|].
              * intros contra; inv contra; [|contradiction].
                rewrite occurs_in_exp_correct in Hk0_nonrec.
                rewrite Disjoint_Singleton_In in Hk0_nonrec; auto.
                contradiction Hk0_nonrec; inv H1; now right.
              * inv H1.
                apply Free_Efun2; apply Free_Fcons1; [|assumption|inversion 1|assumption].
                intros contra; subst.
                rewrite occurs_in_exp_correct in Hg_nonrec.
                rewrite Disjoint_Singleton_In in Hg_nonrec; auto. 
                contradiction Hg_nonrec; now right.
            }

            (* f1 not in (occurs_free ge) *) {
              intros contra; subst; inv Ha; inv H.
              contradiction.
            }

            (* [[curried f]](f + fds + rho) ==_k2 [[uncurried f]](f + f1 + fds + rho1) *) {
              eapply IHk; eauto; [omega|].
              eapply preord_env_P_monotonic; [|eassumption]; omega.
            }
          }
          unfold preord_exp in Hgoal.
          specialize Hgoal with (v1 := v1) (c1 := c1); destruct Hgoal; [apply Hc1|apply Hv1|].
          rename x into v2; destruct H as [c2 [Hv2 Hv1_v2]].
          do 2 eexists; split; [|eassumption].
          econstructor; [| | |eauto|eassumption].
          {
            erewrite <- setlist_not_In; [|symmetry; eassumption|assumption].
            rewrite M.gso; [|auto].
            erewrite <- setlist_not_In; [|symmetry; eassumption|assumption].
            rewrite def_funs_get_neq; auto.
            simpl; rewrite M.gso; auto.
            now rewrite M.gss.
          }
          {
            apply getlist_app.
            eapply getlist_setlist; [now inv Hgv1_fresh|symmetry; eassumption].
            erewrite getlist_setlist_Disjoint;
              [|inv Hfv1_fresh; apply Disjoint_Union_r in H; apply H|symmetry; eassumption].
            rewrite getlist_set_neq; [|assumption].
            apply set_setlist in Hrho1'.
            destruct Hrho1' as [rho1'k0 [Hrho1'k0 Hrho1']]; subst rho1'.
            rewrite getlist_set_neq; [|assumption].
            eapply getlist_setlist; [now inv Hfv1_fresh|symmetry; eassumption].
          }
          {
            rename uncurried into uncurried'; pose (uncurried := uncurried'); subst uncurried'.
            rewrite find_def_fundefs_append_neq; auto.
            simpl; destruct (M.elt_eq f1 f) as [|Heq]; [now subst|clear Heq].
            destruct (M.elt_eq f1 f1) as [Heq|]; [clear Heq|contradiction].
            reflexivity.
          }
      + (* h \in pre_fds ++ fds *)
        assert (Hf : h <> f). {
          intros contra; subst; inv Hcurried_unique_fundefs.
          now apply name_in_fundefs_bound_var_fundefs in Hfds.
          contradiction.
        }
        assert (Hf1: h <> f1). {
          (* f1 is not in curried (freshly generated by uncurrier) *)
          intros contra; subst; contradiction.
        }
        destruct (M.elt_eq h f) as [|Heq]; [contradiction|clear Heq].
        destruct (M.elt_eq h f1) as [|Heq]; [contradiction|clear Heq].
        intros vs1 vs2 k1 t xs1 e1 rho' Hlen_vs1_vs2 Hfind_def Hrho'.
        assert (Hrho1' : length xs1 = length vs2). {
          apply setlist_length in Hrho'.
          now rewrite <- Hlen_vs1_vs2.
        }
        eapply length_exists_setlist in Hrho1'; destruct Hrho1' as [rho1' Hrho1'].
        exists xs1, e1; eexists; split; [|split]; [|eassumption|intros Hk1 Hvs1_vs2].
        (* only f is uncurried, so h in uncurried = h in curried (Hfind_def) *)
        assert (HLR : In _ (name_in_fundefs curried) h) by auto.
        rewrite fundefs_append_name_in_fundefs in HLR; [|reflexivity].
        split_var_in_fundefs h pre_fds Hh_pre_fds.
        subst curried; subst uncurried.
        rewrite find_def_fundefs_append_eq; auto.
        rewrite find_def_fundefs_append_eq in Hfind_def; auto.
        inv HLR; [contradiction|]; inv H; [inv H0; contradiction|].
        subst curried; subst uncurried.
        rewrite find_def_fundefs_append_neq; auto.
        rewrite find_def_fundefs_append_neq in Hfind_def; auto.
        simpl; simpl in Hfind_def.
        destruct (M.elt_eq h f); try contradiction.
        destruct (M.elt_eq h f1); try contradiction; auto.
        apply preord_exp_refl.

        (* wrt free variables of e1, the environments
             rho' = [xs1 -> vs1] + f + fds + rho
             rho1' = [xs1 -> vs2] + f + f1 + fds + rho1
           agree. 
         *)

        (* [[xs1]](rho') ==_k1 [[xs1]](rho1') *)
        eapply preord_env_P_setlist_extend; eauto.

        (* remove pre_fds *)
        intros a Ha.
        split_var_in_fundefs a pre_fds Hpre_fds. {
          unfold preord_var_env.
          rewrite def_funs_eq; [|now apply Hpre_fds_curried].
          rewrite def_funs_eq; [|now apply Hpre_fds_uncurried].
          intros v0 Hv0; inv Hv0; eexists; split; [reflexivity|].
          apply IHk with (e := Ehalt a); [omega| | | |constructor| ].
          * rewrite Union_Same_set; [assumption|].
            unfold used_vars.
            rewrite bound_var_Ehalt.
            rewrite Union_Empty_set_neut_l.
            intros a' Ha'; inv Ha'; left.
            rewrite fundefs_append_bound_vars; [|reflexivity]; left.
            now apply name_in_fundefs_bound_var_fundefs.
          * unfold used_vars.
            rewrite bound_var_Ehalt.
            rewrite Union_Empty_set_neut_l.
            rewrite Union_Same_set; [eapply Union_Included_r; eassumption|].
            intros a' Ha'; inv Ha'; left.
            rewrite fundefs_append_bound_vars; [|reflexivity]; left.
            now apply name_in_fundefs_bound_var_fundefs.
          * eapply preord_env_P_antimon.
            eapply preord_env_P_monotonic; [|eassumption]; omega.
            intros a' Ha'; inv Ha'.
            inv H3; contradiction H1.
            apply Ensemble_In.
            rewrite fundefs_append_name_in_fundefs; [|reflexivity]; now left.
            now apply Free_Efun2.
          * apply Ensemble_In.
            rewrite fundefs_append_name_in_fundefs; [|reflexivity]; now left.
        }
        rename uncurried into uncurried'; pose (uncurried := uncurried'); subst uncurried'.
        apply preord_var_env_def_funs_neq; auto.

        (* remove f and f1 *)
        simpl; apply preord_var_env_extend'. intros Ha_f.
        apply preord_var_env_extend_neq_r.

        (* remove fds *) {
          split_var_in_fundefs a fds Hfds'; unfold preord_var_env; simpl.
          - do 2 (rewrite def_funs_eq; [|assumption]).
            intros v1 Hv1; inv Hv1; eexists; split; [reflexivity|].
            (* todo: basically a duplicate with the previous application of IH *)
            apply IHk with (e := Ehalt a); [omega| | | |constructor|].
            + rewrite Union_Same_set; [assumption|].
              unfold used_vars.
              rewrite bound_var_Ehalt.
              rewrite Union_Empty_set_neut_l.
              intros a' Ha'; inv Ha'; left.
              rewrite fundefs_append_bound_vars; [|reflexivity].
              right; apply Bound_Fcons2.
              now apply name_in_fundefs_bound_var_fundefs.
            + unfold used_vars.
              rewrite bound_var_Ehalt.
              rewrite Union_Empty_set_neut_l.
              rewrite Union_Same_set; [eapply Union_Included_r; eassumption|].
              intros a' Ha'; inv Ha'; left.
              rewrite fundefs_append_bound_vars; [|reflexivity].
              right; do 2 apply Bound_Fcons2.
              now apply name_in_fundefs_bound_var_fundefs.
            + eapply preord_env_P_antimon.
              eapply preord_env_P_monotonic; [|eassumption]; omega.
              intros a' Ha'; inv Ha'.
              inv H3; contradiction H1.
              apply Ensemble_In; rewrite fundefs_append_name_in_fundefs; [|reflexivity].
              right; now right.
              now apply Free_Efun2.
            + apply Ensemble_In; rewrite fundefs_append_name_in_fundefs; [|reflexivity].
              right; now right.
          - unfold preord_var_env.
            do 2 (rewrite def_funs_neq; auto).
            assert ((occurs_free e1
                                 \\ FromList xs1
                                 \\ [set f]
                                 \\ name_in_fundefs pre_fds
                                 \\ name_in_fundefs fds) a). {
              do 3 (split; auto).
              intros contra; now inv contra.
            }
            clear Ha; clear n1; clear Ha_f; clear n0; generalize dependent a.
            eapply preord_env_P_antimon.
            eapply preord_env_P_monotonic; [|eassumption]; omega.
            intros a Ha; inv Ha; inv H; inv H1; inv H.
            apply Free_Efun2.
            subst curried.
            split_var_in_fundefs h pre_fds Hh_pre_fds.
            + apply occurs_free_fundefs_append_l.
              intros contra; inv contra; auto.
              eapply find_def_is_Some_occurs_free_fundefs; eauto.
              rewrite <- find_def_fundefs_append_neq_l
                with (B1 := Fcons f ft (k0 :: fv)
                                 (Efun (Fcons g gt gv ge Fnil) (Eapp k0 kt [g])) fds); auto.
              apply Hfind_def.
              intros contra; inv contra.
              apply fundefs_append_unique with (f := h) in Huncurried_unique_fundefs.
              contradiction.
              now inv H.
              apply fundefs_append_unique with (f := h) in Huncurried_unique_fundefs.
              contradiction.
              right; now right.
            + apply occurs_free_fundefs_append; auto.
              apply Free_Fcons2; [|intros contra; subst; now contradiction H3].
              eapply find_def_is_Some_occurs_free_fundefs; eauto.
              rewrite <- find_def_fundefs_append_neq
                with (B := Fcons f ft (k0 :: fv)
                                 (Efun (Fcons g gt gv ge Fnil) (Eapp k0 kt [g])) Fnil); auto.
              rewrite <- find_def_fundefs_append_neq with (B := pre_fds); auto.
              apply Hfind_def.
              auto.
              intros contra; inv contra; now inv H.
        }

        (* f1 never occurs in the definition of h *)
        {
          intros contra; subst.
          rewrite Union_demorgan in Hf1_fresh; destruct Hf1_fresh as [Hf1_fresh2 Hf1_fresh3].
          rewrite Union_demorgan in Hf1_fresh2; destruct Hf1_fresh2 as [Hf1_fresh1 Hf1_fresh2].
          contradiction Hf1_fresh1.
          apply Hcurried_used_fundefs.
          right.
          eapply find_def_is_Some_occurs_free_fundefs; eauto; now inv Ha.
        }

        (* [[curried f]](rho') ==_k1 [[uncurried f]](rho1') *)
        apply IHk with (e := Ehalt f); [omega| | | |constructor|assumption].
        (* todo: basically a duplicate with the previous application of IH,
           but with left instaed of right soemtimes *)
        * rewrite Union_Same_set; [assumption|].
          unfold used_vars.
          rewrite bound_var_Ehalt.
          rewrite Union_Empty_set_neut_l.
          intros b Hb; inv Hb.
          left; now apply name_in_fundefs_bound_var_fundefs.
        * unfold used_vars.
          rewrite bound_var_Ehalt.
          rewrite Union_Empty_set_neut_l.
          rewrite Union_Same_set; [eapply Union_Included_r; eassumption|].
          rewrite occurs_free_Ehalt.
          intros b Hb; inv Hb.
          left; now apply name_in_fundefs_bound_var_fundefs.
        * eapply preord_env_P_antimon.
          eapply preord_env_P_monotonic; [|eassumption]; omega.
          repeat normalize_occurs_free.
          intros b Hb; inv Hb.
          now left.
          inv H.
          contradiction H1.
          now inv H0.
    - (* h\not\in pre_fds ++ f |: fundefs(fds) *)
      assert (h <> f). {
        intros contra; subst.
        contradiction Hfds.
      }
      assert (h <> f1). {
        intros contra; subst.
        rewrite Union_demorgan in Hf1_fresh; destruct Hf1_fresh as [Hf1_fresh2 Hf1_fresh3].
        rewrite Union_demorgan in Hf1_fresh2; destruct Hf1_fresh2 as [Hf1_fresh1 Hf1_fresh2].
        contradiction Hf1_fresh1.
        apply Hcurried_used.
        now left; right.
      }
      simpl.
      rename curried into curried'; pose (curried := curried'); subst curried'.
      rename uncurried into uncurried'; pose (uncurried := uncurried'); subst uncurried'.
      assert (~ name_in_fundefs fds h). {
        intros contra; contradiction Hfds.
        apply Ensemble_In; rewrite fundefs_append_name_in_fundefs; [|reflexivity].
        right; now right.
      }
      assert (~ name_in_fundefs pre_fds h). {
        intros contra; contradiction Hfds.
        apply Ensemble_In; rewrite fundefs_append_name_in_fundefs; [|reflexivity].
        now left.
      }
      do 2 (rewrite def_funs_get_neq; auto).
      simpl; do 3 (rewrite M.gso; auto).
      do 2 (rewrite def_funs_neq; [|assumption]).
      apply Henv.
      constructor; [simpl|assumption]; auto. 
  Qed.

  Lemma uncurry_step_preserves_ctag : forall x s m s1 m1 arms arms1,
    uncurry_step (Ecase x arms) s m (Ecase x arms1) s1 m1 ->
    Forall2 (fun p p' : cTag * exp => fst p = fst p') arms arms1.
  Proof.
    induction arms; intros.
    - destruct arms1; inv H.
    - destruct arms1; inv H; (constructor; [easy|]).
      now apply List_util.Forall2_refl.
      now apply IHarms.
  Qed.

  Lemma Union_Included_subst_l: forall (A : Type) (a b b' c : Ensemble A),
    a :|: b' \subset c -> b \subset b' -> a :|: b \subset c.
  Proof. intros; intros x Hx; destruct Hx; eauto with Ensembles_DB. Qed.

  Lemma used_vars_fundefs_Fcons_Included: forall f t v e fds,
    used_vars_fundefs fds \subset used_vars_fundefs (Fcons f t v e fds).
  Proof.
    intros; intros x Hx.
    destruct Hx; [left; now apply Bound_Fcons2|inv H].
    split_var_eq x f; subst.
    left; auto.
    right; apply Free_Fcons2; auto.
    split_var_eq x f; subst.
    left; auto.
    right; apply Free_Fcons2; auto.
  Qed.

  Lemma used_vars_Fcons_Included: forall f t v e fds,
    used_vars e \subset used_vars_fundefs (Fcons f t v e fds).
  Proof.
    intros; intros x Hx.
    destruct Hx; [left; now apply Bound_Fcons3|].
    split_var_eq x f; subst.
    left; auto.
    split_var_in_list x v; [left; constructor; auto|].
    split_var_in_fundefs x fds Hfds.
    left; apply Bound_Fcons2; now apply name_in_fundefs_bound_var_fundefs.
    right; apply Free_Fcons1; auto.
  Qed.

  Lemma used_vars_Eprim_cons_Included: forall x p a args e,
    used_vars (Eprim x p args e) \subset used_vars (Eprim x p (a :: args) e).
  Proof.
    intros; intros y Hy; destruct Hy.
    left. inv H; auto.
    inv H; right.
    constructor; now right.
    apply Free_Eprim2; auto.
  Qed.

  Lemma used_vars_Efun_Included: forall fds e,
    used_vars e \subset used_vars (Efun fds e).
  Proof.
    intros; intros x Hx.
    destruct Hx; [left; auto|].
    split_var_in_fundefs x fds Hfds.
    left; constructor; now apply name_in_fundefs_bound_var_fundefs.
    right; constructor; auto.
  Qed.

  Lemma used_vars_fundefs_Efun_Included: forall fds e,
    used_vars_fundefs fds \subset used_vars (Efun fds e).
  Proof.
    intros; intros x Hx.
    destruct Hx; [left; auto|].
    right; now apply Free_Efun2.
  Qed.

  Lemma uncurry_step_s_nondecreasing_mut :
    let P := (fun e s m e1 s1 m1 => s \subset s1) in
    let Q := (fun f s m f1 s1 m1 => s \subset s1) in
    (forall e s m e1 s1 m1, uncurry_step e s m e1 s1 m1 -> P e s m e1 s1 m1) /\
    (forall f s m f1 s1 m1, uncurry_fundefs_step f s m f1 s1 m1 -> Q f s m f1 s1 m1).
  Proof with auto with Ensembles_DB.
    intros P Q.
    uncurry_step_induction_mut P Q IHstep IH;
      subst P; subst Q; simpl in *...
    rewrite H7...
  Qed.

  Corollary uncurry_step_s_nondecreasing : forall e s m e1 s1 m1,
    uncurry_step e s m e1 s1 m1 -> s \subset s1.
  Proof. apply uncurry_step_s_nondecreasing_mut. Qed.

  Corollary uncurry_fundefs_step_s_nondecreasing : forall e s m e1 s1 m1,
    uncurry_fundefs_step e s m e1 s1 m1 -> s \subset s1.
  Proof. apply uncurry_step_s_nondecreasing_mut. Qed.

  Lemma Union_Included_lr : forall {A} (S1 S2 S3 : _ A),
    S1 :|: S2 \subset S3 -> S1 \subset S3 /\ S2 \subset S3.
  Proof.
    intros; split; [eapply Union_Included_l|eapply Union_Included_r]; eauto.
  Qed.

  Local Ltac destruct_Union_Included :=
    repeat match goal with
      [ H : _ :|: _ \subset _ |- _ ] => apply Union_Included_lr in H; destruct H
    end.

  Lemma uncurry_step_preserves_used_vars_mut :
    let P := (fun e s m e1 s1 m1 => used_vars e \subset s -> used_vars e1 \subset s1) in
    let Q := (fun f s m f1 s1 m1 =>
                used_vars_fundefs f \subset s ->
                used_vars_fundefs f1 \subset s1) in
    (forall e s m e1 s1 m1, uncurry_step e s m e1 s1 m1 -> P e s m e1 s1 m1) /\
    (forall f s m f1 s1 m1, uncurry_fundefs_step f s m f1 s1 m1 -> Q f s m f1 s1 m1).
  Proof with eauto with Ensembles_DB.
    intros P Q.
    uncurry_step_induction_mut P Q IHstep IH; subst P; subst Q; simpl in *; intros He;
    try destruct arm;
    try solve [
      (apply uncurry_step_s_nondecreasing in IHstep
         || apply uncurry_fundefs_step_s_nondecreasing in IHstep);
      repeat normalize_used_vars;
      destruct_Union_Included;
      try solve [eapply Included_trans; [|eauto]; eauto with Ensembles_DB];
      apply Union_Included; eauto with Ensembles_DB;
      eapply Included_trans; [|eauto]; eauto with Ensembles_DB].
    - (* Eproj *)
      apply uncurry_step_s_nondecreasing in IHstep.
      rewrite used_vars_Eproj in *.
      destruct_Union_Included.
      apply Union_Included; [|apply Union_Included]...
    - (* Fcons e *)
      apply uncurry_step_s_nondecreasing in IHstep.
      rewrite used_vars_Fcons in *.
      destruct_Union_Included.
      apply Union_Included; [apply Union_Included|]...
      all: eapply Included_trans; [|eassumption]...
    - (* Fcons ge *)
      apply uncurry_step_s_nondecreasing in IHstep.
      repeat (rewrite used_vars_Fcons in * + rewrite used_vars_Efun in *).
      destruct_Union_Included.
      repeat rewrite Union_assoc.
      do 7 (
        match goal with
          [ _ : _ |- used_vars _ \subset _ ] => idtac
        | _ => try apply Union_Included
        end;
        try solve [eapply Included_trans; [|eassumption]; eauto with Ensembles_DB]).
      now apply IH.
    - (* Fcons curried *)
      rewrite H7.
      repeat (rewrite used_vars_Fcons in * + rewrite used_vars_Efun in *).
      destruct_Union_Included.
      repeat rewrite Union_assoc.
      repeat rewrite used_vars_Eapp.
      apply Union_Included. apply Union_Included. apply Union_Included. apply Union_Included.
      apply Union_Included. apply Union_Included. apply Union_Included. apply Union_Included.
      apply Union_Included. apply Union_Included.
      all: eauto with Ensembles_DB.
      + intros a Ha; inv Ha. (* admit: this sort of stuff should be automated away *)
        do 3 left; apply H15; now left.
        left; now right.
      + intros a Ha; inv_all.
        rewrite FromList_app in H16; inv H16; eauto.
      + intros a Ha; inv_all.
        do 3 left; apply H11; rewrite used_vars_Eapp; auto.
        contradiction.
      + rewrite FromList_app.
        rewrite FromList_cons in H15.
        intros a Ha; inv Ha; do 3 left; eauto.
  Qed.

  Corollary uncurry_step_preserves_used_vars : forall e s m e1 s1 m1,
    uncurry_step e s m e1 s1 m1 -> used_vars e \subset s -> used_vars e1 \subset s1.
  Proof. apply uncurry_step_preserves_used_vars_mut. Qed.

  Corollary uncurry_fundefs_step_preserves_used_vars : forall e s m e1 s1 m1,
    uncurry_fundefs_step e s m e1 s1 m1 ->
    used_vars_fundefs e \subset s ->
    used_vars_fundefs e1 \subset s1.
  Proof. apply uncurry_step_preserves_used_vars_mut. Qed.

  Ltac destruct_Union_Intersection :=
    repeat match goal with
      [ H : In _ (_ :&: _) _ |- _ ] => destruct H
    | [ H : In _ (_ :|: _) _ |- _ ] => destruct H
    end.

  Lemma Intersection_Union_distr : forall {A} (S1 S2 S3 : _ A),
    (S1 :|: S2) :&: S3 <--> (S1 :&: S3) :|: (S2 :&: S3).
  Proof.
    split; intros a Ha; destruct_Union_Intersection; auto with Ensembles_DB.
  Qed.

  Lemma uncurry_step_maintains_bindings_mut :
    let P := (fun e s m e1 s1 m1 =>
                used_vars e \subset s -> bound_var e1 :&: s <--> bound_var e) in
    let Q := (fun f s m f1 s1 m1 =>
                used_vars_fundefs f \subset s ->
                bound_var_fundefs f1 :&: s <--> bound_var_fundefs f) in
    (forall e s m e1 s1 m1, uncurry_step e s m e1 s1 m1 -> P e s m e1 s1 m1) /\
    (forall f s m f1 s1 m1, uncurry_fundefs_step f s m f1 s1 m1 -> Q f s m f1 s1 m1).
  Proof with eauto with Ensembles_DB.
    intros P Q.
    uncurry_step_induction_mut P Q IHstep IH; subst P; subst Q; simpl in *; intros;
    try destruct arm;
    try (
      repeat normalize_bound_var; repeat normalize_used_vars;
      rewrite Intersection_Union_distr;
      rewrite IH; [rewrite Intersection_Same_set; [reflexivity| ] |];
      eapply Included_trans; [|eauto| |eauto]; eauto with Ensembles_DB).
    - (* Fcons fds *)
      repeat rewrite bound_var_fundefs_Fcons.
      repeat rewrite Intersection_Union_distr.
      rewrite IH.
      repeat rewrite Intersection_Same_set.
      reflexivity.
      all: rewrite used_vars_Fcons in H.
      eapply Included_trans; [|eassumption]...
      eapply Union_Included_r.
      do 2 eapply Union_Included_l...
      do 3 eapply Union_Included_l...
      eapply Included_trans; [|eassumption]...
    - (* Fcons e *)
      repeat rewrite bound_var_fundefs_Fcons.
      repeat rewrite Intersection_Union_distr.
      rewrite IH.
      repeat rewrite Intersection_Same_set.
      reflexivity.
      all: rewrite used_vars_Fcons in H.
      eapply Included_trans; [|eassumption]...
      eapply Union_Included_r.
      do 2 eapply Union_Included_l...
      do 3 eapply Union_Included_l...
      eapply Included_trans; [|eassumption]...
    - (* Fcons ge *)
      repeat rewrite bound_var_fundefs_Fcons.
      repeat rewrite bound_var_Efun.
      repeat rewrite bound_var_fundefs_Fcons.
      repeat rewrite Intersection_Union_distr.
      rewrite IH.
      repeat rewrite Intersection_Same_set.
      reflexivity.
      all: repeat (rewrite used_vars_Fcons in H + rewrite used_vars_Efun in H);
           repeat rewrite Union_assoc in H.
      eapply Included_trans; [|eassumption]...
      rewrite bound_var_Eapp...
      rewrite bound_var_fundefs_Fnil...
      eapply Union_Included_r; do 5 eapply Union_Included_l...
      eapply Union_Included_r; do 5 eapply Union_Included_l...
      eapply Union_Included_r; do 6 eapply Union_Included_l...
      do 7 eapply Union_Included_l...
      eapply Union_Included_r; do 3 eapply Union_Included_l...
    - (* Fcons curried *)
      assert (Hsubst :
              bound_var_fundefs
                (Fcons f9 ft (k :: fv1)
                       (Efun (Fcons g gt gv1
                                    (Eapp f10 ft1 (gv1 ++ fv1))
                                    Fnil)
                             (Eapp k kt [g]))
                       (Fcons f10 ft1 (gv ++ fv) ge fds)) <-->
             bound_var_fundefs
                (Fcons f9 ft (k :: fv) (Efun (Fcons g gt gv ge Fnil) (Eapp k kt [g])) fds)
                :|: FromList (f10 :: fv1 ++ gv1)). {
        repeat (rewrite bound_var_fundefs_Fcons + rewrite bound_var_Efun).
        repeat rewrite bound_var_Eapp.
        repeat rewrite FromList_cons.
        repeat rewrite FromList_app.
        split; intros a Ha; destruct_Union_Intersection; auto 10 with Ensembles_DB.
      }
      assert (Hsubst1 : FromList (f10 :: fv1 ++ gv1) :&: s <--> Empty_set _). {
        rewrite FromList_cons.
        rewrite FromList_app.
        split; intros a Ha; [|inv Ha].
        repeat rewrite Union_demorgan in H6.
        unfold fresh_copies in *.
        repeat match goal with
          [ H : _ /\ _ |- _ ] => destruct H
        | [ H : _ \/ _ |- _ ] => destruct H
        end.
        destruct_Union_Intersection; inv_all.
        contradiction.
        inv H4. contradiction (H15 x); auto.
        inv H2. contradiction (H15 x); auto.
      }
      rewrite Hsubst.
      rewrite Intersection_Union_distr.
      rewrite Hsubst1.
      rewrite Intersection_Same_set.
      now rewrite Union_Empty_set_neut_r.
      eapply Union_Included_l; eauto.
  Qed.

  Corollary uncurry_step_maintains_bindings: forall e s m e1 s1 m1,
    uncurry_step e s m e1 s1 m1 ->
    used_vars e \subset s ->
    bound_var e1 :&: s <--> bound_var e.
  Proof. apply uncurry_step_maintains_bindings_mut. Qed.

  Corollary uncurry_fundefs_step_maintains_bindings: forall f s m f1 s1 m1,
    uncurry_fundefs_step f s m f1 s1 m1 ->
    used_vars_fundefs f \subset s ->
    bound_var_fundefs f1 :&: s <--> bound_var_fundefs f.
  Proof. apply uncurry_step_maintains_bindings_mut. Qed.

  Corollary uncurry_step_maintains_bindings_fn: forall e s m e1 s1 m1,
    uncurry_step e s m e1 s1 m1 ->
    used_vars e \subset s -> forall a,
    In _ (bound_var e1) a ->
    In _ s a ->
    In _ (bound_var e) a.
  Proof. intros; rewrite <- uncurry_step_maintains_bindings; eauto. Qed.

  Corollary uncurry_fundefs_step_maintains_bindings_fn: forall f s m f1 s1 m1,
    uncurry_fundefs_step f s m f1 s1 m1 ->
    used_vars_fundefs f \subset s -> forall a,
    In _ (bound_var_fundefs f1) a ->
    In _ s a ->
    In _ (bound_var_fundefs f) a.
  Proof. intros; rewrite <- uncurry_fundefs_step_maintains_bindings; eauto. Qed.

  Lemma uncurry_step_maintains_used_vars_mut :
    let P := (fun e s m e1 s1 m1 =>
                used_vars e \subset s -> used_vars e1 :&: s <--> used_vars e) in
    let Q := (fun f s m f1 s1 m1 =>
                used_vars_fundefs f \subset s ->
                used_vars_fundefs f1 :&: s <--> used_vars_fundefs f) in
    (forall e s m e1 s1 m1, uncurry_step e s m e1 s1 m1 -> P e s m e1 s1 m1) /\
    (forall f s m f1 s1 m1, uncurry_fundefs_step f s m f1 s1 m1 -> Q f s m f1 s1 m1).
  Proof with eauto with Ensembles_DB.
    intros P Q.
    uncurry_step_induction_mut P Q IHstep IH; subst P; subst Q; simpl in *; intros;
    try destruct arm;
    try (
      repeat normalize_used_vars;
      rewrite Intersection_Union_distr;
      rewrite IH; [rewrite Intersection_Same_set; eauto with Ensembles_DB|];
      eapply Included_trans; [|eauto| |eauto]; eauto with Ensembles_DB).
    - (* Eproj *)
      repeat rewrite used_vars_Eproj.
      do 2 rewrite Intersection_Union_distr.
      rewrite IH.
      rewrite Intersection_Same_set...
      rewrite Intersection_Same_set...
      all: rewrite used_vars_Eproj in H...
      eapply Included_trans; eauto...
    - (* Fcons fds *)
      repeat rewrite used_vars_Fcons.
      repeat rewrite Intersection_Union_distr.
      rewrite IH.
      repeat rewrite Intersection_Same_set...
      all: rewrite used_vars_Fcons in H.
      eapply Included_trans; [|eassumption]...
      eapply Union_Included_r.
      do 2 eapply Union_Included_l...
      do 3 eapply Union_Included_l...
      eapply Included_trans; [|eassumption]...
    - (* Fcons ge *)
      repeat rewrite used_vars_Fcons.
      repeat rewrite used_vars_Efun.
      repeat rewrite used_vars_Fcons.
      repeat rewrite Intersection_Union_distr.
      rewrite IH.
      repeat rewrite Intersection_Same_set...
      all: repeat (rewrite used_vars_Fcons in H + rewrite used_vars_Efun in H);
           repeat rewrite Union_assoc in H.
      eapply Included_trans; [|eassumption]...
      rewrite used_vars_Eapp in *; eapply Included_trans; eauto...
      rewrite used_vars_Fnil...
      eapply Union_Included_r; do 5 eapply Union_Included_l...
      eapply Union_Included_r; do 5 eapply Union_Included_l...
      eapply Union_Included_r; do 6 eapply Union_Included_l...
      do 7 eapply Union_Included_l...
      eapply Union_Included_r; do 3 eapply Union_Included_l...
    - (* Fcons curried *)
      assert (Hsubst :
              used_vars_fundefs
                (Fcons f9 ft (k :: fv1)
                       (Efun (Fcons g gt gv1
                                    (Eapp f10 ft1 (gv1 ++ fv1))
                                    Fnil)
                             (Eapp k kt [g]))
                       (Fcons f10 ft1 (gv ++ fv) ge fds)) <-->
             used_vars_fundefs
                (Fcons f9 ft (k :: fv) (Efun (Fcons g gt gv ge Fnil) (Eapp k kt [g])) fds)
                :|: FromList (f10 :: fv1 ++ gv1)). {
        repeat (rewrite used_vars_Fcons + rewrite used_vars_Efun).
        repeat rewrite used_vars_Eapp.
        repeat rewrite FromList_cons.
        repeat rewrite FromList_app.
        split; intros a Ha; destruct_Union_Intersection; auto 10 with Ensembles_DB.
      }
      assert (Hsubst1 : FromList (f10 :: fv1 ++ gv1) :&: s <--> Empty_set _). {
        rewrite FromList_cons.
        rewrite FromList_app.
        split; intros a Ha; [|inv Ha].
        repeat rewrite Union_demorgan in H6.
        unfold fresh_copies in *.
        repeat match goal with
          [ H : _ /\ _ |- _ ] => destruct H
        | [ H : _ \/ _ |- _ ] => destruct H
        end.
        destruct_Union_Intersection; inv_all.
        contradiction.
        inv H4. contradiction (H15 x); auto.
        inv H2. contradiction (H15 x); auto.
      }
      rewrite Hsubst.
      rewrite Intersection_Union_distr.
      rewrite Hsubst1.
      rewrite Intersection_Same_set.
      now rewrite Union_Empty_set_neut_r.
      eapply Union_Included_l...
  Qed.

  Corollary uncurry_step_maintains_used_vars: forall e s m e1 s1 m1,
    uncurry_step e s m e1 s1 m1 ->
    used_vars e \subset s ->
    used_vars e1 :&: s <--> used_vars e.
  Proof. apply uncurry_step_maintains_used_vars_mut. Qed.

  Corollary uncurry_fundefs_step_maintains_used_vars: forall f s m f1 s1 m1,
    uncurry_fundefs_step f s m f1 s1 m1 ->
    used_vars_fundefs f \subset s ->
    used_vars_fundefs f1 :&: s <--> used_vars_fundefs f.
  Proof. apply uncurry_step_maintains_used_vars_mut. Qed.

  Corollary uncurry_step_maintains_used_vars_fn: forall e s m e1 s1 m1,
    uncurry_step e s m e1 s1 m1 ->
    used_vars e \subset s -> forall a,
    In _ (used_vars e1) a ->
    In _ s a ->
    In _ (used_vars e) a.
  Proof. intros; rewrite <- uncurry_step_maintains_used_vars; eauto. Qed.

  Corollary uncurry_fundefs_step_maintains_used_vars_fn: forall f s m f1 s1 m1,
    uncurry_fundefs_step f s m f1 s1 m1 ->
    used_vars_fundefs f \subset s -> forall a,
    In _ (used_vars_fundefs f1) a ->
    In _ s a ->
    In _ (used_vars_fundefs f) a.
  Proof. intros; rewrite <- uncurry_fundefs_step_maintains_used_vars; eauto. Qed.

  Lemma uncurry_step_preserves_unique_bindings_mut :
    let P := (fun e s m e1 s1 m1 =>
                used_vars e \subset s ->
                unique_bindings e ->
                unique_bindings e1) in
    let Q := (fun f s m f1 s1 m1 =>
                used_vars_fundefs f \subset s ->
                unique_bindings_fundefs f ->
                unique_bindings_fundefs f1) in
    (forall e s m e1 s1 m1, uncurry_step e s m e1 s1 m1 -> P e s m e1 s1 m1) /\
    (forall f s m f1 s1 m1, uncurry_fundefs_step f s m f1 s1 m1 -> Q f s m f1 s1 m1).
  Proof with eauto with Ensembles_DB.
    intros P Q.
    uncurry_step_induction_mut P Q IHstep IH; subst P; subst Q; simpl in *; intros.
    - (* Econstr *)
      rewrite used_vars_Econstr in H; inv H0.
      assert (used_vars e \subset s).
      eapply Union_Included_r...
      assert (unique_bindings e)...
      constructor; auto.
      intros contra.
      contradiction H3.
      eapply uncurry_step_maintains_bindings_fn; eauto.
    - (* Ecase arm *)
      rewrite used_vars_Ecase_cons in H; inv H0.
      assert (used_vars e \subset s).
      eapply Union_Included_l...
      constructor; auto.
      constructor; intros a contra; destruct contra.
      inv H7. contradiction (H3 x0).
      split; auto.
      eapply uncurry_step_maintains_bindings_fn; eauto.
      apply H; right; now left.
    - (* Ecase arms *)
      destruct arm; rewrite used_vars_Ecase_cons in H; inv H0.
      assert (used_vars (Ecase x arms) \subset s).
      eapply Union_Included_r...
      constructor; auto.
      constructor; intros a contra; destruct contra.
      inv H7. contradiction (H3 x0).
      split; auto.
      eapply uncurry_step_maintains_bindings_fn; eauto.
      apply H; left; now left.
    - (* Eproj *)
      rewrite used_vars_Eproj in H; inv H0.
      assert (used_vars e \subset s).
      do 2 eapply Union_Included_r...
      constructor; auto.
      intros contra.
      contradiction H3.
      eapply uncurry_step_maintains_bindings_fn; eauto.
    - (* Eprim *)
      rewrite used_vars_Eprim in H; inv H0.
      assert (used_vars e \subset s).
      eapply Union_Included_r...
      constructor; auto.
      intros contra; contradiction H3; eapply uncurry_step_maintains_bindings_fn; eauto.
    - (* Efun e *)
      rewrite used_vars_Efun in H; inv H0.
      assert (used_vars e \subset s).
      eapply Union_Included_r...
      constructor; auto.
      constructor; intros a contra; destruct contra.
      inv H5. contradiction (H6 x).
      split; auto.
      eapply uncurry_step_maintains_bindings_fn; eauto.
      apply H; left; now left.
    - (* Efun fds *)
      rewrite used_vars_Efun in H; inv H0.
      assert (used_vars_fundefs fds \subset s).
      eapply Union_Included_l...
      constructor; auto.
      constructor; intros a contra; destruct contra.
      inv H5. contradiction (H6 x).
      split; auto.
      eapply uncurry_fundefs_step_maintains_bindings_fn; eauto.
      apply H; right; now left.
    - (* Fcons fds *)
      rewrite used_vars_Fcons in H; inv H0.
      assert (used_vars_fundefs fds \subset s).
      eapply Union_Included_r...
      constructor; auto.
      intros contra.
      contradiction H7; eapply uncurry_fundefs_step_maintains_bindings_fn; eauto.
      constructor; intros a contra; destruct contra.
      inv H9. contradiction (H3 x).
      split; auto.
      eapply uncurry_fundefs_step_maintains_bindings_fn; eauto.
      constructor; intros a contra; destruct contra.
      inv H10. contradiction (H3 x).
      split; auto.
      eapply uncurry_fundefs_step_maintains_bindings_fn; eauto.
      apply H; left; right; now left.
    - (* Fcons e *)
      rewrite used_vars_Fcons in H; inv H0.
      assert (used_vars e \subset s).
      eapply Union_Included_r. eapply Union_Included_l...
      constructor; auto.
      intros contra.
      contradiction H6; eapply uncurry_step_maintains_bindings_fn; eauto.
      constructor; intros a contra; destruct contra.
      inv H8. contradiction (H3 x). split; auto.
      eapply uncurry_step_maintains_bindings_fn; eauto.
      constructor; intros a contra; destruct contra.
      inv H10; contradiction (H3 x); split; auto.
      eapply uncurry_step_maintains_bindings_fn; eauto.
      apply H; right; now left.
    - (* Fcons ge *)
      repeat (rewrite used_vars_Fcons in H + rewrite used_vars_Efun in H); inv H0.
      repeat rewrite Union_assoc in H.
      assert (used_vars e \subset s).
      eapply Union_Included_r; do 3 eapply Union_Included_l...
      constructor; auto.
      + intros contra.
        contradiction H6.
        inv contra.
        inv H4.
        constructor. constructor. auto.
        inv H17.
        constructor. apply Bound_Fcons3.
        eapply uncurry_step_maintains_bindings_fn; eauto.
        apply H; now do 7 left.
        now apply Bound_Efun2.
      + constructor; intros a contra; destruct contra.
        inv H8. contradiction (H3 x); split; auto.
        inv H1; [constructor|now apply Bound_Efun2].
        inv H15; [now apply Bound_Fcons1|now apply Bound_Fcons2|apply Bound_Fcons3].
        eapply uncurry_step_maintains_bindings_fn; eauto.
        apply H; do 6 left; now right.
      + constructor; intros a contra; destruct contra.
        inv H10; contradiction (H3 x); split; auto.
        inv H1; [constructor|now apply Bound_Efun2].
        inv H15; [now apply Bound_Fcons1|now apply Bound_Fcons2|apply Bound_Fcons3].
        eapply uncurry_step_maintains_bindings_fn; eauto.
        apply H; right; now left.
      + constructor; [constructor|constructor|].
        intros contra. inv H13. inv H4.
        contradiction H17; eapply uncurry_step_maintains_bindings_fn; eauto.
        apply H; do 5 left; now right.
        inversion 1.
        constructor; intros a contra; destruct contra.
        inv H13. inv H15.
        inv H21. contradiction (H3 x).
        split; auto.
        eapply uncurry_step_maintains_bindings_fn; eauto.
        apply H; do 4 left; now right.
        rewrite bound_var_fundefs_Fnil...
        rewrite bound_var_fundefs_Fnil...
        all: inv H13; inv H4; auto.
        rewrite bound_var_Eapp...
    - (* Fcons curried *)
      repeat (rewrite used_vars_Fcons in H8 + rewrite used_vars_Efun in H8).
      repeat rewrite Union_assoc in H8.
      rewrite not_occurs_in_exp_iff_used_vars in H0.
      rewrite not_occurs_in_exp_iff_used_vars in H1.
      unfold fresh_copies in *; destruct H2; destruct H4.
      repeat rewrite Union_demorgan in H6.
      do 2 destruct H6.
      constructor.
      Local Ltac clear_false_bound_var_hyps :=
        try match goal with
          [ H : bound_var_fundefs Fnil _ |- _ ] => inv H
        | [ H : bound_var (Eapp _ _ _) _ |- _ ] => inv H
        | [ _ : _ |- ~ bound_var_fundefs Fnil _ ] => inversion 1
        | [ _ : _ |- ~ bound_var (Eapp _ _ _) _ ] => inversion 1
        end.
      + intros contra; inv contra; clear_false_bound_var_hyps.
        inv H17; inv_all; clear_false_bound_var_hyps.
        * inv H9.
          contradiction H19. constructor. constructor. now left.
        * inv H2. contradiction (H15 f9).
          split; auto. apply H8; now do 7 left.
      + intros contra; inv contra.
        inv_all.
        * contradiction H6; apply H8; now do 7 left.
        * rewrite FromList_app in H14; inv H14.
          inv H9.
          contradiction H20.
          constructor.
          constructor.
          now right.
          inv H9.
          contradiction H25; now right.
        * now inv H9.
        * inv H9. contradiction H19.
          constructor.
          now apply Bound_Fcons3.
      + constructor; intros a contra; destruct contra.
        inv_all; clear_false_bound_var_hyps.
        inv H18; inv_all; clear_false_bound_var_hyps.
        inv H9; inv_all; clear_false_bound_var_hyps.
        inv H21. contradiction (H9 x).
        split; [|now left].
        constructor; constructor; now constructor.
        inv H2. contradiction (H15 x).
        split; auto.
        apply H8; do 6 left; right; now left.
        inv H19; inv_all; clear_false_bound_var_hyps.
        inv H4. contradiction (H14 x).
        split; auto; left; apply H8; do 5 left; now right.
        inv H4; contradiction (H15 x); split; auto; right.
      + constructor; intros a contra; destruct contra.
        inv_all; clear_false_bound_var_hyps.
        * contradiction H6; apply H8; do 6 left; right; now left.
        * rewrite FromList_app in H14; inv H14.
          inv H9. inv H22. contradiction (H9 x).
          split; auto; now left.
          inv H9; inv H26. contradiction.
        * inv H9. inv H23. contradiction (H9 x); split; auto; now left.
        * contradiction H1; now left.
        * rewrite FromList_app in H14; inv H14.
          inv H4. contradiction (H14 x).
          split; auto; left; apply H8; do 4 left; now right.
          inv H4. contradiction (H14 x).
          split; auto; left; apply H8; do 6 left; right; now right.
        * inv H4. contradiction (H14 x).
          split; auto; left; apply H8; right; now left.
        * inv H4. contradiction (H14 x).
          split; auto; left; apply H8; do 3 left; right; now left.
      + constructor; intros a contra; destruct contra.
        inv_all; clear_false_bound_var_hyps.
        * inv H18; inv_all; clear_false_bound_var_hyps.
          contradiction H6; apply H8; do 5 left; now right.
        * rewrite FromList_app in H15; inv H15.
          inv H19; inv_all; clear_false_bound_var_hyps.
          inv H9. inv H27. inv H17. contradiction.
          inv H2. contradiction (H16 x); split; auto.
          apply H8; do 4 left; now right.
          inv H19; inv_all; clear_false_bound_var_hyps.
          inv H9. inv H27. inv H22. contradiction (H9 x).
          split; auto; now right.
          inv H2. contradiction (H16 x); split; auto.
          apply H8; do 6 left; right; now right.
        * inv H18; inv_all; clear_false_bound_var_hyps.
          inv H9. inv H24. contradiction (H9 x); split; auto.
          inv H2. contradiction (H15 x); split; auto.
          apply H8; right; now left.
        * inv H18; inv_all; clear_false_bound_var_hyps.
          inv H9. inv H27. inv H16. contradiction.
          inv H2. contradiction (H15 x). split; auto.
          apply H8; do 3 left; right; now left.
      + inversion 1; subst.
        inv H9. contradiction H25; now left.
        inv H4. contradiction (H16 f9); split; auto.
        left; apply H8; now do 7 left.
      + constructor; auto; intros contra.
        inv H4. contradiction (H14 k); split; auto.
        left; apply H8; do 6 left; right; now left.
      + constructor; [constructor ..|]; clear_false_bound_var_hyps; auto.
        rewrite bound_var_Eapp...
        rewrite bound_var_fundefs_Fnil...
        rewrite bound_var_Eapp...
        intros contra.
        inv H2. contradiction (H14 g); split; auto; apply H8.
        do 5 left; now right.
        constructor.
        constructor.
        rewrite bound_var_Eapp...
      + constructor.
        intros contra; contradiction H6; apply H8; do 3 left; right; now left.
        intros contra; contradiction H6; apply H8; right; now left.
        constructor; intros a contra; inv contra.
        rewrite FromList_app in H15; destruct H15.
        inv H9. inv H28. inv H18. inv H33. contradiction (H9 x); split; auto.
        inv H9. inv H23. contradiction (H9 x); split; auto; now right.
        constructor; intros a contra; inv contra.
        rewrite FromList_app in H15; destruct H15.
        inv H9. inv H25. contradiction (H9 x); split; auto.
        inv H9. inv H24. contradiction (H9 x); split; auto; now right.
        constructor; intros a contra; inv contra.
        inv H9. inv H25. contradiction (H9 a); split; auto.
        change (~ In _ (FromList (gv ++ fv)) f10).
        intros contra; rewrite FromList_app in contra; destruct contra.
        contradiction H6; apply H8; do 4 left; now right.
        contradiction H6; apply H8; do 6 left; right; now right.
        apply NoDup_app.
        inv H9. inv H26. now inv H16.
        inv H9. now inv H25.
        constructor; intros a contra; inv contra.
        inv H9. inv H23. contradiction (H9 a); split; auto; now right.
        inv H9. inv H26. now inv H16.
        now inv H9.
  Qed.

  Corollary uncurry_step_preserves_unique_bindings : forall e s m e1 s1 m1,
    uncurry_step e s m e1 s1 m1 ->
    used_vars e \subset s ->
    unique_bindings e ->
    unique_bindings e1.
  Proof. apply uncurry_step_preserves_unique_bindings_mut. Qed.

  Corollary uncurry_fundefs_step_preserves_unique_bindings : forall f s m f1 s1 m1,
    uncurry_fundefs_step f s m f1 s1 m1 ->
    used_vars_fundefs f \subset s ->
    unique_bindings_fundefs f ->
    unique_bindings_fundefs f1.
  Proof. apply uncurry_step_preserves_unique_bindings_mut. Qed.

  Hint Constructors unique_bindings.

  Lemma uncurry_fundefs_step_unique_names : forall a f s m f1 s1 m1,
    used_vars_fundefs f \subset s ->
    uncurry_fundefs_step f s m f1 s1 m1 ->
    name_in_fundefs f1 a ->
    ~ name_in_fundefs f a ->
    ~ In var s a.
  Proof with eauto with Ensembles_DB.
    intros a f s m f1 s1 m1 Hused Hstep Hf1 Hf.
    induction Hstep; try solve [inv Hf1; [inv H0|]; contradiction Hf; [now left|now right]].
    - apply IHHstep.
      eapply Included_trans; [|eauto]; repeat normalize_used_vars...
      inv Hf1; auto.
      inv H; contradiction Hf; now left.
      intros contra; contradiction Hf; now right.
    - simpl in *.
      inv Hf1; inv H0; inv H8.
      + contradiction Hf; now left.
      + inv H0. intros contra; contradiction H6; now do 2 left.
      + contradiction Hf; now right.
  Qed.

  Lemma uncurry_fundefs_step_preserves_names : forall a f s m f1 s1 m1,
    name_in_fundefs f a ->
    uncurry_fundefs_step f s m f1 s1 m1 ->
    name_in_fundefs f1 a.
  Proof.
    intros a f s m f1 s1 m1 Hf Hstep.
    induction Hstep; try solve [inv Hf; [inv H0; now left|now right]].
    - inv Hf.
      inv H; now left.
      right; now apply IHHstep.
    - inv Hf.
      inv H7; now left.
      right; now right.
  Qed.

  Lemma uncurry_fundefs_step_preserves_tags : forall a f s m f1 s1 m1 t v e t1 v1 e1,
    used_vars_fundefs f \subset s ->
    uncurry_fundefs_step f s m f1 s1 m1 ->
    find_def a f = Some (t, v, e) ->
    find_def a f1 = Some (t1, v1, e1) ->
    t = t1.
  Proof with eauto 10 with Ensembles_DB.
    intros a f s m f1 s1 m1 t v e t1 v1 e1 Hused Hstep Hf Hf1.
    induction Hstep; simpl in Hf, Hf1; destruct (M.elt_eq a f); subst;
      inv Hf; inv Hf1; auto;
      try solve [rewrite H1 in H2; now inv H2].
    - apply IHHstep; auto.
      rewrite used_vars_Fcons in Hused.
      eapply Included_trans...
    - destruct (M.elt_eq a f1); subst.
      + contradiction H6.
        left; left.
        apply Hused; left.
        apply Bound_Fcons2.
        apply name_in_fundefs_bound_var_fundefs.
        eapply find_def_name_in_fundefs; eauto.
      + rewrite H9 in H10; now inv H10.
  Qed.

  Lemma uncurry_fundefs_step_preserves_length : forall a f s m f1 s1 m1 t v e t1 v1 e1,
    used_vars_fundefs f \subset s ->
    uncurry_fundefs_step f s m f1 s1 m1 ->
    find_def a f = Some (t, v, e) ->
    find_def a f1 = Some (t1, v1, e1) ->
    length v = length v1.
  Proof with eauto 10 with Ensembles_DB.
    intros a f s m f1 s1 m1 t v e t1 v1 e1 Hused Hstep Hf Hf1.
    induction Hstep; simpl in Hf, Hf1; destruct (M.elt_eq a f); subst;
      inv Hf; inv Hf1; auto;
      try solve [rewrite H1 in H2; now inv H2].
    - apply IHHstep; auto.
      rewrite used_vars_Fcons in Hused.
      eapply Included_trans...
    - simpl; now apply f_equal.
    - destruct (M.elt_eq a f1); subst.
      + contradiction H6.
        left; left.
        apply Hused; left.
        apply Bound_Fcons2.
        apply name_in_fundefs_bound_var_fundefs.
        eapply find_def_name_in_fundefs; eauto.
      + rewrite H9 in H10; now inv H10.
  Qed.

  Lemma preord_exp_preord_env_com' : forall pr cenv rho1 rho2 rho1' rho2' S1 S2 e1 e2 k,
    occurs_free e1 \subset S1 ->
    occurs_free e2 \subset S2 ->
    (forall k : nat, preord_exp pr cenv k (e1, rho1) (e2, rho2)) ->
    preord_env_P pr cenv S1 k rho1' rho1 ->
    (forall k : nat, preord_env_P pr cenv S2 k rho2 rho2') ->
    preord_exp pr cenv k (e1, rho1') (e2, rho2').
  Proof.
    intros pr cenv rho1 rho2 rho1' rho2' S1 S2 e1 e2 k HS1 HS2 He Hrho1 Hrho2.
    eapply preord_exp_trans.
    apply preord_exp_refl.
    eapply preord_env_P_antimon; eauto.
    intros k1; eapply preord_exp_trans; eauto.
    intros k2; apply preord_exp_refl.
    eapply preord_env_P_antimon; eauto.
  Qed.

  Lemma find_def_body_occurs_free_Included : forall fds a t xs e,
    find_def a fds = Some (t, xs, e) ->
    occurs_free e \subset name_in_fundefs fds :|: occurs_free_fundefs fds :|: FromList xs.
  Proof.
    induction fds; intros a t xs e0 Hfind; [|inv Hfind].
    simpl in Hfind.
    destruct (M.elt_eq a v).
    - inv Hfind.
      intros a Ha.
      split_var_in_fundefs a (Fcons v t xs e0 fds) Hfds; [now do 2 left|].
      split_var_in_list a xs; [now right|].
      left; right; constructor; auto.
      intro contra; subst; contradiction n; now left.
      intros contra; contradiction n; now right.
    - eapply Included_trans.
      eapply IHfds; eauto.
      intros b Hb; inv Hb; [inv H|]; [left; left; now right| |now right].
      split_var_in_fundefs b (Fcons v f l e fds) Hfds; [left; now left|].
      left; right.
      apply Free_Fcons2; eauto.
      intros contra; subst; contradiction n0; now left.
  Qed.

  Lemma Union_Setminus_Included : forall {U : Type} (A B : Ensemble U),
    A :|: B \\ B \subset A.
  Proof.
    intros U A B a Ha.
    inv Ha.
    inv H; auto; contradiction.
  Qed.

  Lemma fundefs_append_assoc : forall A B C,
    fundefs_append A (fundefs_append B C) = fundefs_append (fundefs_append A B) C.
  Proof.
    induction A.
    - intros B C; simpl. now rewrite IHA.
    - auto.
  Qed.

  Lemma fundefs_append_used_vars : forall B B1,
    used_vars_fundefs (fundefs_append B B1) <--> used_vars_fundefs B :|: used_vars_fundefs B1.
  Proof with eauto 10 with Ensembles_DB.
    induction B.
    intros B1; split.
    - intros a Ha.
      simpl in Ha; rewrite used_vars_Fcons in Ha.
      inv Ha. inv H. inv H0. inv H.
      left; left; constructor; now left.
      left; left; constructor; now right.
      left; rewrite used_vars_Fcons...
      rewrite IHB in H.
      inv H.
      left; rewrite used_vars_Fcons...
      now right.
    - intros a Ha.
      rewrite used_vars_Fcons in Ha.
      inv Ha. inv H. inv H0. inv H. inv H0.
      all: simpl; rewrite used_vars_Fcons...
      right; rewrite IHB...
      right; rewrite IHB...
    - intros B1; simpl; rewrite used_vars_Fnil...
  Qed.

  Lemma fundefs_append_ctx_exists : forall f' c',
    exists c, forall e, c <[ e ]> = fundefs_append f' (c' <[ e ]>).
  Proof.
    induction f'.
    intros c'; simpl.
    edestruct IHf' as [c Hc].
    exists (Fcons2_c v f l e c); intros e0; simpl.
    now rewrite Hc.
    intros c'.
    eexists; simpl; eauto.
  Qed.
  Lemma preord_exp_eq_compat :
  forall pr cenv k rho1 rho2 c e1 e2 e1' e2',
    (forall (k0 : nat) (rho3 rho4 : env),
    preord_env_P pr cenv (occurs_free e1) k0 rho3 rho4 ->
    preord_exp pr cenv k0 (e1, rho3) (e2, rho4)) ->
    c |[ e1 ]| = e1' -> c |[ e2 ]| = e2' ->
    preord_env_P pr cenv (occurs_free e1') k rho1 rho2 ->
    preord_exp pr cenv k (e1', rho1) (e2', rho2).
  Proof.
    intros; rewrite <- H0; rewrite <- H1; apply preord_exp_compat; auto.
    now rewrite H0.
  Qed.

  Lemma uncurry_step_correct' :
    let P := (fun e s _ e1 s1 _ => forall k,
                  unique_bindings e ->
                  unique_bindings e1 -> (* TODO: remove this assumption *)
                  used_vars e \subset s ->
                  used_vars e1 \subset s1 -> (* TODO: remove this assumption *)
                  ctx_preord_exp k e e1) in
    let Q := (fun f s (m : localMap) f1 s1 (m1 : localMap) => forall f' k e,
                  unique_bindings (Efun (fundefs_append f' f) e) ->
                  unique_bindings (Efun (fundefs_append f' f1) e) -> (* TODO: remove this assumption *)
                  used_vars (Efun (fundefs_append f' f) e) \subset s ->
                  used_vars (Efun (fundefs_append f' f1) e) \subset s1 -> (* TODO: remove this assumption *)
                  ctx_preord_exp k (Efun (fundefs_append f' f) e) (Efun (fundefs_append f' f1) e)) in
    forall e s m e1 s1 m1,
    uncurry_step e s m e1 s1 m1 -> P e s m e1 s1 m1.
  Proof with eauto 10 with Ensembles_DB.
    intros P Q.
    uncurry_step_induction P Q IHuncurry IH;
      subst P; subst Q; simpl in *;
      [ intros k .. | intros f' k' e' | intros f' k' e' | intros f' k' e' | intros f' k' e' ];
      intros Hunique Hunique1 Hused Hused1 rho rho1 pr cenv Henv.
    - (* uncurry_constr *)
      apply preord_exp_const_compat.
      + unfold preord_env_P in Henv.
        apply Forall2_same.
        intros a Hin. apply Henv.
        now apply Free_Econstr1.
      + intros args1 args2 Hargs.
        apply IH; inv Hunique; inv Hunique1; auto.
        rewrite used_vars_Econstr in Hused.
        eapply Included_trans; [|eassumption]...
        rewrite used_vars_Econstr in Hused1.
        eapply Included_trans; [|eassumption]...
        apply preord_env_P_extend.
        * intros x1 Hx1. apply Henv.
          inversion Hx1. apply Free_Econstr2; [|assumption].
          intros contra. subst. intuition.
        * rewrite preord_val_eq. split; [trivial|].
          now apply Forall2_Forall2_asym_included.
    - (* uncurry_case_expr *)
      apply preord_exp_case_cons_compat.
      + now apply List_util.Forall2_refl.
      + now apply Henv.
      + apply IH; inv Hunique; inv Hunique1; auto.
        rewrite used_vars_Ecase_cons in Hused.
        eapply Included_trans; [|eassumption]...
        rewrite used_vars_Ecase_cons in Hused1.
        eapply Included_trans; [|eassumption]...
        eapply preord_env_P_antimon; [eassumption|].
        eapply occurs_free_Ecase_Included; simpl; eauto.
      + apply preord_exp_refl.
        eapply preord_env_P_antimon; [eassumption|].
        rewrite occurs_free_Ecase_cons...
    - (* uncurry_case_arms *)
      destruct arm.
      apply preord_exp_case_cons_compat.
      + eapply uncurry_step_preserves_ctag; eauto.
      + now apply Henv.
      + apply preord_exp_refl.
        eapply preord_env_P_antimon; [eassumption|].
        rewrite occurs_free_Ecase_cons...
      + apply IH; inv Hunique; inv Hunique1; auto.
        rewrite used_vars_Ecase_cons in Hused.
        eapply Included_trans; [|eassumption]...
        rewrite used_vars_Ecase_cons in Hused1.
        eapply Included_trans; [|eassumption]...
        eapply preord_env_P_antimon; [eassumption|].
        rewrite occurs_free_Ecase_cons...
    - (* uncurry_proj *)
      apply preord_exp_proj_compat.
      now apply Henv.
      intros v1 v2 Hv1_v2.
      apply IH; inv Hunique; inv Hunique1; auto.
      rewrite used_vars_Eproj in Hused.
      eapply Included_trans; [|eassumption]...
      rewrite used_vars_Eproj in Hused1.
      eapply Included_trans; [|eassumption]...
      intros a Ha; split_var_eq a x; subst; unfold preord_var_env.
      + do 2 rewrite M.gss.
        intros v0 Hv0; inv Hv0; eauto.
      + do 2 (rewrite M.gso; [|assumption]).
        apply Henv; auto.
    - (* uncurry_prim *)
      apply preord_exp_prim_compat.
      + induction args; constructor.
        apply Henv; constructor; now left.
        inv Hunique; inv Hunique1.
        apply IHargs; try constructor; auto.
        rewrite used_vars_Eprim in *.
        rewrite FromList_cons in Hused.
        eapply Included_trans; [|eassumption]...
        rewrite used_vars_Eprim in *.
        rewrite FromList_cons in Hused1.
        eapply Included_trans; [|eassumption]...
        eapply preord_env_P_antimon; [eassumption|].
        intros a' Ha'; inv Ha'.
        constructor; now right.
        apply Free_Eprim2; assumption.
      + intros v1 v2 Hv1_v2.
        apply IH; inv Hunique; inv Hunique1; auto.
        rewrite used_vars_Eprim in Hused.
        eapply Included_trans; [|eassumption]...
        rewrite used_vars_Eprim in Hused1.
        eapply Included_trans; [|eassumption]...
        intros a Ha; split_var_eq a x; subst; unfold preord_var_env.
        * do 2 rewrite M.gss.
          intros v0 Hv0; inv Hv0; eauto.
        * do 2 (rewrite M.gso; [|assumption]).
          apply Henv; auto.
    - (* uncurry_fun_expr *)
      apply preord_exp_fun_compat.
      apply IH; inv Hunique; inv Hunique1; auto.
      rewrite used_vars_Efun in Hused.
      eapply Included_trans; [|eassumption]...
      rewrite used_vars_Efun in Hused1.
      eapply Included_trans; [|eassumption]...
      intros a Ha; split_var_in_fundefs a fds Hfds; unfold preord_var_env.
      + do 2 (rewrite def_funs_eq; [|assumption]).
        intros v1 Hv1; inv Hv1; eexists; split; [reflexivity|].
        apply preord_val_fundefs.
        eapply preord_env_P_antimon; [eassumption|].
        rewrite occurs_free_Efun...
      + do 2 (rewrite def_funs_neq; [|assumption]).
        apply Henv; auto.
    - (* uncurry_fun_fds *)
      apply IH with (f' := Fnil); eauto.
    - (* uncurry_fundefs_fds *)
      replace (fundefs_append f' (Fcons f t args e fds))
        with (fundefs_append (fundefs_append f' (Fcons f t args e Fnil)) fds)
        by now rewrite <- fundefs_append_assoc.
      replace (fundefs_append f' (Fcons f t args e fds1))
        with (fundefs_append (fundefs_append f' (Fcons f t args e Fnil)) fds1)
        by now rewrite <- fundefs_append_assoc.
      apply IH with (f' := fundefs_append f' (Fcons f t args e Fnil));
        rewrite <- fundefs_append_assoc; auto.
    - (* uncurry_fundefs_e *)
      edestruct fundefs_append_ctx_exists
        with (f' := f') (c' := Fcons1_c f t args Hole_c fds) as [c Hc].
      eapply preord_exp_eq_compat with (c := Efun2_c c e') (e1 := e) (e2 := e1); eauto.
      unfold ctx_preord_exp in IH.
      inv Hunique; inv Hunique1.
      apply fundefs_append_unique_and in H2; destruct H2.
      apply fundefs_append_unique_and in H5; destruct H5.
      inv H0; inv H5.
      intros k rho0 rho2; eapply IH; auto.
      eapply Included_trans; eauto.
      rewrite used_vars_Efun.
      rewrite fundefs_append_used_vars.
      rewrite used_vars_Fcons...
      eapply Included_trans; eauto.
      rewrite used_vars_Efun.
      rewrite fundefs_append_used_vars.
      rewrite used_vars_Fcons...
      all: simpl; now rewrite Hc.
    - (* uncurry_fundefs_g *)
      edestruct fundefs_append_ctx_exists
        with (f' := f')
             (c' := Fcons1_c f ft (k :: fv)
                             (Efun2_c (Fcons1_c g gt gv Hole_c Fnil) (Eapp k kt [g])) fds) as [c Hc].
      eapply preord_exp_eq_compat with (c := Efun2_c c e') (e1 := e) (e2 := e1); eauto.
      unfold ctx_preord_exp in IH.
      inv Hunique; inv Hunique1.
      apply fundefs_append_unique_and in H2; destruct H2.
      apply fundefs_append_unique_and in H5; destruct H5.
      inv H0; inv H5.
      inv H19; inv H27.
      inv H8; inv H19.
      intros k0 rho0 rho2; eapply IH; auto.
      eapply Included_trans; eauto.
      rewrite used_vars_Efun.
      rewrite fundefs_append_used_vars.
      repeat (rewrite used_vars_Fcons + rewrite used_vars_Efun)...
      eapply Included_trans; eauto.
      rewrite used_vars_Efun.
      rewrite fundefs_append_used_vars.
      repeat (rewrite used_vars_Fcons + rewrite used_vars_Efun)...
      all: simpl; now rewrite Hc.
    - (* uncurry_fundefs_curried *)
      eapply uncurry_step_correct_fundefs_curried; eauto...
      eapply Included_trans; [|apply Hused].
      rewrite used_vars_Efun...
      rewrite H7 in Hused1.
      eapply Included_trans; [|apply Hused1].
      rewrite used_vars_Efun...
      now inv Hunique.
      eapply Union_Included_l.
      eapply Included_trans; [|apply Hused].
      rewrite used_vars_Efun...
      now inv Hunique1.
  Qed.

  Lemma uncurry_step_correct : forall k e s m e1 s1 m1,
    unique_bindings e ->
    unique_bindings e1 -> (* TODO: remove this assumption *)
    used_vars e \subset s ->
    used_vars e1 \subset s1 -> (* TODO: remove this assumption *)
    uncurry_step e s m e1 s1 m1 -> ctx_preord_exp k e e1.
  Proof. intros. intros rho rho1 pr cenv Henv. eapply uncurry_step_correct'; eauto. Qed.

  Lemma fds_noncircular : forall f t v e fds, Fcons f t v e fds <> fds.
  Proof. induction fds; inversion 1; now subst. Qed.

  Local Ltac circular_fds :=
    match goal with
    | [ H : Fcons ?f ?t ?v ?e ?fds = ?fds |- _ ] =>
      assert (Fcons f t v e fds <> fds) by apply fds_noncircular; contradiction
    | [ H : ?fds = Fcons ?f ?t ?v ?e ?fds |- _ ] =>
      symmetry in H; circular_fds
    end.

  Lemma uncurry_step_not_reflexive_mut :
    let P := (fun e s m e1 s1 m1 => e <> e1 /\ s <> s1 /\ m <> m1) in
    let Q := (fun f s m f1 s1 m1 => f <> f1 /\ s <> s1 /\ m <> m1) in
    (forall e s m e1 s1 m1, uncurry_step e s m e1 s1 m1 -> P e s m e1 s1 m1) /\
    (forall f s m f1 s1 m1, uncurry_fundefs_step f s m f1 s1 m1 -> Q f s m f1 s1 m1).
  Proof with eauto with Ensembles_DB.
    intros P Q.
    uncurry_step_induction_mut P Q IHstep IH; subst P; subst Q; simpl in *;
      (split; [|split]); try destruct IH as [? [? ?]]; auto;
      intros contra; inv contra; try easy.
    (* uncurry_fundefs_curried *)
    - circular_fds.
    - rewrite H7 in H6.
      contradiction H6.
      left; left; now right.
    - apply f_equal with
        (f := fun a =>
                match M.get g a with
                | Some true => true
                | _ => false
                end) in H8.
      rewrite H in H8.
      now rewrite M.gss in H8.
  Qed.

  Local Ltac solve_uncurry_step_not_reflexive :=
    intros; intros H; destruct uncurry_step_not_reflexive_mut as [He Hf];
    try (now apply He in H);
    try (now apply Hf in H).

  Corollary uncurry_step_not_reflexive : forall e s m s1 m1, ~ uncurry_step e s m e s1 m1.
  Proof. solve_uncurry_step_not_reflexive. Qed.

  Corollary uncurry_fundefs_step_not_reflexive : forall f s m s1 m1, ~ uncurry_fundefs_step f s m f s1 m1.
  Proof. solve_uncurry_step_not_reflexive. Qed.

  Corollary uncurry_step_not_reflexive_s : forall e s m e1 m1, ~ uncurry_step e s m e1 s m1.
  Proof. solve_uncurry_step_not_reflexive. Qed.

  Corollary uncurry_fundefs_step_not_reflexive_s : forall f s m f1 m1, ~ uncurry_fundefs_step f s m f1 s m1.
  Proof. solve_uncurry_step_not_reflexive. Qed.

  Corollary uncurry_step_not_reflexive_m : forall e s m e1 s1, ~ uncurry_step e s m e1 s1 m.
  Proof. solve_uncurry_step_not_reflexive. Qed.

  Corollary uncurry_fundefs_step_not_reflexive_m : forall f s m f1 s1, ~ uncurry_fundefs_step f s m f1 s1 m.
  Proof. solve_uncurry_step_not_reflexive. Qed.

  Local Ltac step_isnt_reflexive :=
    match goal with
    | [ H : uncurry_step ?a _ _ ?a _ _ |- _ ] =>
      now apply uncurry_step_not_reflexive in H
    | [ H : uncurry_fundefs_step ?a _ _ ?a _ _ |- _ ] =>
      now apply uncurry_fundefs_step_not_reflexive in H
    end.

  Lemma circular_app_f_ctx : forall f t v e e1 e2 ctx,
    Fcons f t v e (ctx <[ e1 ]>) <> ctx <[ e2 ]>.
  Proof.
    induction ctx; intros contra.
    inv contra. circular_fds.
    inv contra. contradiction.
  Qed.

  Lemma uncurry_step_subterm_invariant_mut :
    (forall c, (fun c => forall e s m e1 s1 m1,
      uncurry_step (c |[ e ]|) s m (c |[ e1 ]|) s1 m1 ->
      uncurry_step e s m e1 s1 m1) c) /\
    (forall f, (fun f => forall e s m e1 s1 m1,
      uncurry_fundefs_step (f <[ e ]>) s m (f <[ e1 ]>) s1 m1 ->
      uncurry_step e s m e1 s1 m1) f).
  Proof. (* with eauto with Ensembles_DB.*)
    exp_fundefs_ctx_induction IHe IHf; simpl;
      try rename e into c;
      try intros arms e s m e1 s1 m1 Hstep;
      try intros e s m e1 s1 m1 Hstep;
      try solve [easy|inv Hstep; now apply IHe].
    - (* Efun1_c *)
      induction l.
      + inv Hstep.
        now apply IHe.
        step_isnt_reflexive.
      + apply IHl.
        inv Hstep.
        step_isnt_reflexive.
        assumption.
    - (* Efun2_c *)
      apply IHe.
      inv Hstep.
      assumption.
      step_isnt_reflexive.
    - (* Fcons1_c *)
      inv Hstep.
      step_isnt_reflexive.
      now apply IHf.
    - (* Fcons2_c *)
      inv Hstep.
      step_isnt_reflexive.
      now apply IHe.
      apply IHe.
      rewrite <- H3; rewrite <- H7.
      inv H3; inv H7.
      apply uncurry_fun_fds; auto.
      circular_fds.
    - (* Fcons3_c *)
      inv Hstep.
      now apply IHf.
      step_isnt_reflexive.
      step_isnt_reflexive.
      pose circular_app_f_ctx.
      exfalso; eapply n; eauto.
  Qed.

  Corollary uncurry_step_subterm_invariant : forall c e s m e1 s1 m1,
    uncurry_step (c |[ e ]|) s m (c |[ e1 ]|) s1 m1 ->
    uncurry_step e s m e1 s1 m1.
  Proof. apply uncurry_step_subterm_invariant_mut. Qed.

  Corollary uncurry_fundefs_step_subterm_invariant : forall f e s m e1 s1 m1,
    uncurry_fundefs_step (f <[ e ]>) s m (f <[ e1 ]>) s1 m1 ->
    uncurry_step e s m e1 s1 m1.
  Proof. apply uncurry_step_subterm_invariant_mut. Qed.

  Lemma app_ctx_uncurry_step_mut : 
    (forall c, (fun c => forall e s m e1 s1 m1,
      used_vars (c |[ e ]|) \subset s ->
      uncurry_step e s m e1 s1 m1 ->
      uncurry_step (c |[ e ]|) s m (c |[ e1 ]|) s1 m1) c) /\
    (forall f, (fun f => forall e s m e1 s1 m1,
      used_vars_fundefs (f <[ e ]>) \subset s ->
      uncurry_step e s m e1 s1 m1 ->
      uncurry_fundefs_step (f <[ e ]>) s m (f <[ e1 ]>) s1 m1) f).
  Proof with eauto with Ensembles_DB.
    exp_fundefs_ctx_induction IHe IHf; simpl;
      try rename e into c;
      try intros arms e s m e1 s1 m1 Hused Hstep (* Huniq*);
      try intros e s m e1 s1 m1 Hused Hstep (* Huniq*);
      try assumption;
      try (
        constructor;
        repeat normalize_used_vars;
        ((apply IHe; auto) || (apply IHf; auto));
        eapply Included_trans; [|eauto]; eauto with Ensembles_DB).
    - induction l; simpl in *.
      + constructor; rewrite used_vars_Ecase_cons in Hused.
        apply IHe; auto.
        rewrite Union_commut in Hused.
        eapply Included_trans...
      + destruct a; constructor.
        rewrite used_vars_Ecase_cons in Hused.
        apply IHl; auto.
        eapply Included_trans...
  Qed.

  Corollary app_ctx_uncurry_step : forall c e s m e1 s1 m1,
      used_vars (c |[ e ]|) \subset s ->
      uncurry_step e s m e1 s1 m1 ->
      uncurry_step (c |[ e ]|) s m (c |[ e1 ]|) s1 m1.
  Proof. apply app_ctx_uncurry_step_mut. Qed.

  Corollary app_ctx_uncurry_fundefs_step : forall f e s m e1 s1 m1,
      used_vars_fundefs (f <[ e ]>) \subset s ->
      uncurry_step e s m e1 s1 m1 ->
      uncurry_fundefs_step (f <[ e ]>) s m (f <[ e1 ]>) s1 m1.
  Proof. apply app_ctx_uncurry_step_mut. Qed.

  Lemma uncurry_step_increases_size_mut :
    let P := (fun e s m e1 s1 m1 => sizeOf_exp e < sizeOf_exp e1) in
    let Q := (fun f s m f1 s1 m1 => sizeOf_fundefs f < sizeOf_fundefs f1) in
    (forall e s m e1 s1 m1, uncurry_step e s m e1 s1 m1 -> P e s m e1 s1 m1) /\
    (forall f s m f1 s1 m1, uncurry_fundefs_step f s m f1 s1 m1 -> Q f s m f1 s1 m1).
  Proof with eauto with Ensembles_DB.
    intros P Q.
    uncurry_step_induction_mut P Q IHstep IH; subst P; subst Q;
    try (try destruct arm; simpl in *; omega).
  Qed.

  Corollary uncurry_step_increases_size : forall e s m e1 s1 m1,
    uncurry_step e s m e1 s1 m1 -> sizeOf_exp e < sizeOf_exp e1.
  Proof. apply uncurry_step_increases_size_mut. Qed.

  Corollary uncurry_fundefs_step_increases_size : forall f s m f1 s1 m1,
    uncurry_fundefs_step f s m f1 s1 m1 -> sizeOf_fundefs f < sizeOf_fundefs f1.
  Proof. apply uncurry_step_increases_size_mut. Qed.

  Lemma uncurry_step_acyclic : forall e s m e1 s1 m1 s2 m2,
    uncurry_step e s m e1 s1 m1 -> ~ uncurry_step e1 s1 m1 e s2 m2.
  Proof.
    intros; intros H1.
    apply uncurry_step_increases_size in H.
    apply uncurry_step_increases_size in H1.
    omega.
  Qed.

  Lemma uncurry_fundefs_step_acyclic : forall e s m e1 s1 m1 s2 m2,
    uncurry_fundefs_step e s m e1 s1 m1 -> ~ uncurry_fundefs_step e1 s1 m1 e s2 m2.
  Proof.
    intros; intros H1.
    apply uncurry_fundefs_step_increases_size in H.
    apply uncurry_fundefs_step_increases_size in H1.
    omega.
  Qed.

  Local Ltac step_isnt_cyclic :=
    match goal with
    | [ H : uncurry_step ?a _ _ ?b _ _,
        H1 : uncurry_step ?b _ _ ?a _ _ |- _ ] =>
      destruct (uncurry_step_acyclic _ _ _ _ _ _ _ _ H H1)
    | [ H : uncurry_fundefs_step ?a _ _ ?b _ _,
        H1 : uncurry_fundefs_step ?b _ _ ?a _ _ |- _ ] =>
      destruct (uncurry_fundefs_step_acyclic _ _ _ _ _ _ _ _ H H1)
    end.

  Lemma uncurry_step_preserves_occurs_free_mut :
    let P := (fun e s m e1 s1 m1 =>
                used_vars e \subset s ->
                unique_bindings e ->
                occurs_free e <--> occurs_free e1) in
    let Q := (fun f s m f1 s1 m1 =>
                used_vars_fundefs f \subset s ->
                unique_bindings_fundefs f ->
                occurs_free_fundefs f <--> occurs_free_fundefs f1) in
    (forall e s m e1 s1 m1, uncurry_step e s m e1 s1 m1 -> P e s m e1 s1 m1) /\
    (forall f s m f1 s1 m1, uncurry_fundefs_step f s m f1 s1 m1 -> Q f s m f1 s1 m1).
  Proof with eauto with Ensembles_DB.
    Local Ltac ensemble_compat_simpl := match goal with
      [ _ : _ |- ?a :|: ?b \subset ?a :|: ?c ] => apply Included_Union_compat; eauto with Ensembles_DB
    | [ _ : _ |- ?a \\ ?b \subset ?a \\ ?c ] => apply Included_Setminus_compat; eauto with Ensembles_DB
    | [ _ : _ |- ?a :|: ?c \subset ?b :|: ?c ] => apply Included_Union_compat; eauto with Ensembles_DB
    | [ _ : _ |- ?a \\ ?c \subset ?b \\ ?c ] => apply Included_Setminus_compat; eauto with Ensembles_DB
    | [ _ : _ |- ?a :|: ?b <--> ?a :|: ?c ] => apply Same_set_Union_compat; eauto with Ensembles_DB
    | [ _ : _ |- ?a \\ ?b <--> ?a \\ ?c ] => apply Same_set_Setminus_compat; eauto with Ensembles_DB
    | [ _ : _ |- ?a :|: ?c <--> ?b :|: ?c ] => apply Same_set_Union_compat; eauto with Ensembles_DB
    | [ _ : _ |- ?a \\ ?c <--> ?b \\ ?c ] => apply Same_set_Setminus_compat; eauto with Ensembles_DB
    end.
    intros P Q.
    uncurry_step_induction_mut P Q IHstep IH; subst P; subst Q; simpl in *;
    try destruct arm;
    try (
      repeat normalize_occurs_free;
      repeat normalize_used_vars; intros Hused Huniq; inv Huniq;
      destruct IH as [HL HR]; eauto; [eapply Included_trans; [|eauto]; eauto with Ensembles_DB|];
      rewrite (conj HL HR : _ <--> _));
    try reflexivity.
    - (* Efun *)
      ensemble_compat_simpl; split.
      + intros a Ha; inv Ha; split; auto; intros contra.
        assert (~ In var s a). {
          eapply uncurry_fundefs_step_unique_names; eauto.
          eapply Included_trans; [|eauto]...
        }
        contradiction H4; apply Hused; right; now right.
      + ensemble_compat_simpl.
        intros a Ha; eapply uncurry_fundefs_step_preserves_names; eauto.
    - (* Fcons e *)
      split.
      + ensemble_compat_simpl.
        intros a Ha; inv Ha.
        repeat rewrite Union_demorgan in H0; destruct H0 as [Hf6 [Hargs Hfds]].
        split; auto; intros contra; inv contra; inv H0; auto.
        assert (~ In var s a). {
          eapply uncurry_fundefs_step_unique_names; eauto.
          eapply Included_trans; [|eauto]...
        }
        contradiction H0; apply Hused; left; right; now right.
      + repeat ensemble_compat_simpl; intros a Ha; eapply uncurry_fundefs_step_preserves_names; eauto.
    - (* Fcons ge *)
      intros Hused Huniq.
      repeat normalize_occurs_free; simpl.
      repeat ensemble_compat_simpl; apply IH.
      eapply Included_trans; [|eauto]; repeat normalize_used_vars...
      inv Huniq; inv H11; now inv H2. (* admit: automate something like this? basically keep inverting stuff until you find unique_bindings e *)
    - (* Fcons ge *)
      intros Hused Huniq.
      do 2 rewrite occurs_free_fundefs_Fcons.
      do 2 rewrite occurs_free_Efun; simpl; repeat rewrite Union_Empty_set_neut_r.
      rewrite occurs_free_Eapp.
      assert (Hrw : FromList [g] :|: [set k] \\ [set g] <--> [set k]). {
        split; intros a Ha; inv Ha.
        - inv H8. inv H10. now contradiction H9. inv H8. auto.
        - constructor; [now right|].
          intros contra; inv contra.
          inv Huniq.
          inv H15; contradiction (H8 a).
          split; [|now left].
          constructor; constructor; now left.
      }
      rewrite Hrw.
      repeat normalize_occurs_free.
      repeat (rewrite Union_Empty_set_neut_r + rewrite Setminus_Empty_set_abs_r).
      assert (Hrw1 :
        occurs_free ge \\ (g |: FromList gv) :|: [set k] \\
          (f9 |: (FromList (k :: fv) :|: name_in_fundefs fds)) <-->
        occurs_free ge \\ (f9 |: FromList gv :|: FromList fv :|: name_in_fundefs fds)). {
        rewrite Setminus_Union_Included; [|rewrite FromList_cons; eauto with Ensembles_DB].
        repeat rewrite <- Setminus_Union.
        rewrite <- Included_Setminus_Disjoint with (s2 := [set g]).
        repeat rewrite Setminus_Union.
        rewrite Union_assoc, FromList_cons.
        rewrite Union_commut.
        repeat rewrite <- Setminus_Union.
        rewrite <- Included_Setminus_Disjoint with (s2 := [set k]).
        repeat rewrite Setminus_Union.
        repeat rewrite Union_assoc.
        rewrite Union_commut.
        rewrite Union_commut with (s2 := FromList gv).
        repeat rewrite Union_assoc...
        apply Disjoint_Singleton_r; intros contra.
        rewrite not_occurs_in_exp_iff_used_vars in H1; contradiction H1; now right.
        apply Disjoint_Singleton_r; intros contra.
        rewrite not_occurs_in_exp_iff_used_vars in H0; contradiction H0; now right.
      }
      rewrite Hrw1.
      assert (Hrw2 : occurs_free_fundefs fds \\ [set f10] <--> occurs_free_fundefs fds). {
        split...
        intros a Ha; constructor...
        intros contra; inv contra.
        contradiction H6; do 2 left; apply Hused.
        normalize_used_vars; right; now right.
      }
      rewrite Hrw2.
      assert (Hrw3 :
        occurs_free ge \\ (f10 |: (FromList (gv ++ fv) :|: name_in_fundefs fds)) <-->
        occurs_free ge \\ (FromList gv :|: FromList fv :|: name_in_fundefs fds)). {
        rewrite Union_commut.
        rewrite <- Setminus_Union.
        symmetry.
        rewrite FromList_app.
        apply Included_Setminus_Disjoint.
        constructor; intros a contra; inv contra; inv H9.
        contradiction H6; do 2 left; apply Hused.
        inv H8.
        normalize_used_vars; left; right.
        normalize_used_vars; left; normalize_used_vars.
        left; right; now right.
      }
      rewrite Hrw3.
      assert (Hrw4 : FromList (gv1 ++ fv1) :|: [set f10] \\ (g |: FromList gv1) <-->
                              f10 |: FromList fv1). {
        rewrite Setminus_Union_distr.
        assert (Hrw5 : [set f10] \\ (g |: FromList gv1) <--> [set f10]). {
          symmetry.
          apply Included_Setminus_Disjoint.
          constructor; intros a contra; inv contra; inv H8.
          inv H9; [inv H8|]; contradiction H6.
          do 2 left; apply Hused; normalize_used_vars; left; right.
          normalize_used_vars; left; normalize_used_vars; now do 3 left.
          left; now right.
        }
        rewrite Hrw5.
        rewrite Union_commut; apply Same_set_Union_compat...
        rewrite FromList_app, Setminus_Union_distr.
        assert (Hrw6 : FromList gv1 \\ (g |: FromList gv1) <--> Empty_set _).
        apply Setminus_Included_Empty_set...
        rewrite Hrw6; rewrite Union_Empty_set_neut_l.
        symmetry.
        apply Included_Setminus_Disjoint.
        constructor; intros a contra; inv contra.
        destruct H4 as [HL HR].
        inv H9; [inv H4|].
        inv HL; contradiction (H4 a).
        split; auto.
        left; apply Hused; normalize_used_vars; left; right.
        normalize_used_vars; left; normalize_used_vars; now do 3 left.
        inv HL; contradiction (H9 a); split; auto.
      }
      rewrite Hrw4.
      assert (Hrw5 :
        (f10 |: FromList fv1 :|: [set k]) \\
          (f9 |: (FromList (k :: fv1) :|: (f10 |: name_in_fundefs fds))) <-->
          Empty_set _). {
        apply Setminus_Included_Empty_set.
        intros a Ha; inv Ha; inv H8; [inv H9| |].
        do 2 right; now left.
        right; left; now right.
        right; left; now left.
      }
      rewrite Hrw5; rewrite Union_Empty_set_neut_l.
      rewrite Setminus_Union_distr.
      rewrite Setminus_Union.
      rewrite Union_commut with (s2 := [set f9]).
      now repeat rewrite Union_assoc.
  Qed.

  Lemma uncurry_step_preserves_closed : forall e s m e1 s1 m1,
    used_vars e \subset s ->
    unique_bindings e ->
    uncurry_step e s m e1 s1 m1 -> closed_exp e -> closed_exp e1.
  Proof with eauto with Ensembles_DB.
    unfold closed_exp; intros.
    destruct uncurry_step_preserves_occurs_free_mut.
    rewrite <- H3; eauto.
  Qed.

  Inductive uncurry_rel :
    nat ->
    exp -> Ensemble var -> localMap ->
    exp -> Ensemble var -> localMap ->
    Prop :=
  | uncurry_rel_refl : forall e s m, uncurry_rel 0 e s m e s m
  | uncurry_rel_trans : forall n e s m e1 s1 m1 e2 s2 m2,
        uncurry_step e s m e1 s1 m1 ->
        uncurry_rel n e1 s1 m1 e2 s2 m2 ->
        uncurry_rel (S n) e s m e2 s2 m2.

  Inductive uncurry_rel_fundefs :
    nat ->
    fundefs -> Ensemble var -> localMap ->
    fundefs -> Ensemble var -> localMap ->
    Prop :=
  | uncurry_rel_fundefs_refl : forall f s m, uncurry_rel_fundefs 0 f s m f s m
  | uncurry_rel_fundefs_trans : forall n f s m f1 s1 m1 f2 s2 m2,
        uncurry_fundefs_step f s m f1 s1 m1 ->
        uncurry_rel_fundefs n f1 s1 m1 f2 s2 m2 ->
        uncurry_rel_fundefs (S n) f s m f2 s2 m2.

  Hint Constructors uncurry_rel.
  Hint Constructors uncurry_rel_fundefs.

  Lemma uncurry_rel_Sn : forall n e s m e1 s1 m1,
    uncurry_rel (S n) e s m e1 s1 m1 -> exists e2 s2 m2,
    uncurry_rel n e s m e2 s2 m2 /\ uncurry_step e2 s2 m2 e1 s1 m1.
  Proof.
    induction n.
    - do 3 eexists; split; auto.
      inv H; now inv H2.
    - intros.
      inv H.
      apply IHn in H2.
      destruct H2 as [e3 [s3 [m3 [Hrel Hstep]]]].
      do 3 eexists; split; eauto.
  Qed.

  Lemma Sn_uncurry_rel : forall n e s m e1 s1 m1 e2 s2 m2,
    uncurry_rel n e s m e2 s2 m2 ->
    uncurry_step e2 s2 m2 e1 s1 m1 ->
    uncurry_rel (S n) e s m e1 s1 m1.
  Proof.
    induction 1; intros.
    - econstructor; eauto.
    - apply IHuncurry_rel in H1.
      econstructor; eauto.
  Qed.

  Lemma uncurry_rel_fundefs_Sn : forall n e s m e1 s1 m1,
    uncurry_rel_fundefs (S n) e s m e1 s1 m1 -> exists e2 s2 m2,
    uncurry_rel_fundefs n e s m e2 s2 m2 /\ uncurry_fundefs_step e2 s2 m2 e1 s1 m1.
  Proof.
    induction n.
    - do 3 eexists; split; auto.
      inv H; now inv H2.
    - intros.
      inv H.
      apply IHn in H2.
      destruct H2 as [e3 [s3 [m3 [Hrel Hstep]]]].
      do 3 eexists; split; eauto.
  Qed.

  Lemma Sn_uncurry_rel_fundefs : forall n e s m e1 s1 m1 e2 s2 m2,
    uncurry_rel_fundefs n e s m e2 s2 m2 ->
    uncurry_fundefs_step e2 s2 m2 e1 s1 m1 ->
    uncurry_rel_fundefs (S n) e s m e1 s1 m1.
  Proof.
    induction 1; intros.
    - econstructor; eauto.
    - apply IHuncurry_rel_fundefs in H1.
      econstructor; eauto.
  Qed.

  Lemma uncurry_rel_compose : forall n1 n e s m e1 s1 m1 e2 s2 m2,
    uncurry_rel n e s m e1 s1 m1 ->
    uncurry_rel n1 e1 s1 m1 e2 s2 m2 ->
    uncurry_rel (n1 + n) e s m e2 s2 m2.
  Proof.
    induction n1; intros; [inv H0; auto|].
    apply uncurry_rel_Sn in H0.
    destruct H0 as [e3 [s3 [m3 [Hrel Hstep]]]].
    eapply Sn_uncurry_rel; eauto.
  Qed.

  Lemma uncurry_rel_fundefs_compose : forall n1 n e s m e1 s1 m1 e2 s2 m2,
    uncurry_rel_fundefs n e s m e1 s1 m1 ->
    uncurry_rel_fundefs n1 e1 s1 m1 e2 s2 m2 ->
    uncurry_rel_fundefs (n1 + n) e s m e2 s2 m2.
  Proof.
    induction n1; intros; [inv H0; auto|].
    apply uncurry_rel_fundefs_Sn in H0.
    destruct H0 as [e3 [s3 [m3 [Hrel Hstep]]]].
    eapply Sn_uncurry_rel_fundefs; eauto.
  Qed.
  
  Lemma uncurry_rel_preserves_unique_bindings : forall n e s m e1 s1 m1,
    used_vars e \subset s ->
    unique_bindings e ->
    uncurry_rel n e s m e1 s1 m1 ->
    unique_bindings e1.
  Proof.
    induction n; [inversion 3; subst; auto|].
    intros.
    inv H1.
    eapply IHn; [| |eassumption].
    eapply uncurry_step_preserves_used_vars; eauto.
    eapply uncurry_step_preserves_unique_bindings; eauto.
  Qed.
  
  Lemma uncurry_rel_preserves_closed : forall n e s m e1 s1 m1,
    used_vars e \subset s ->
    unique_bindings e ->
    closed_exp e ->
    uncurry_rel n e s m e1 s1 m1 ->
    closed_exp e1.
  Proof.
    induction n; [inversion 4; subst; auto|].
    intros.
    inv H2.
    eapply IHn; [| | |eassumption].
    eapply uncurry_step_preserves_used_vars; eauto.
    eapply uncurry_step_preserves_unique_bindings; eauto.
    eapply uncurry_step_preserves_closed; eauto.
  Qed.

  Lemma uncurry_rel_preserves_used_vars : forall n e s m e1 s1 m1,
    used_vars e \subset s ->
    uncurry_rel n e s m e1 s1 m1 ->
    used_vars e1 \subset s1.
  Proof.
    induction n; [inversion 2; subst; auto|].
    intros.
    inv H0.
    eapply IHn; [|eassumption].
    eapply uncurry_step_preserves_used_vars; eauto.
  Qed.

  Lemma uncurry_rel_s_nondecreasing : forall n e s m e1 s1 m1,
    uncurry_rel n e s m e1 s1 m1 -> s \subset s1.
  Proof.
    induction n; inversion 1; [eauto with Ensembles_DB|subst].
    eapply Included_trans.
    eapply uncurry_step_s_nondecreasing; eauto.
    eapply IHn; eauto.
  Qed.

  Lemma uncurry_fundefs_rel_s_nondecreasing : forall n f s m f1 s1 m1,
    uncurry_rel_fundefs n f s m f1 s1 m1 -> s \subset s1.
  Proof.
    induction n; inversion 1; [eauto with Ensembles_DB|subst].
    eapply Included_trans.
    eapply uncurry_fundefs_step_s_nondecreasing; eauto.
    eapply IHn; eauto.
  Qed.

  Lemma uncurry_fundefs_rel_preserves_used_vars : forall n f s m f1 s1 m1,
    uncurry_rel_fundefs n f s m f1 s1 m1 ->
    used_vars_fundefs f \subset s ->
    used_vars_fundefs f1 \subset s1.
  Proof.
    induction n; inversion 1; [eauto with Ensembles_DB|subst]; intros.
    apply uncurry_fundefs_step_preserves_used_vars in H1; auto.
    eapply IHn; eauto.
  Qed.

  Lemma uncurry_fundefs_rel_preserves_unique_bindings : forall n f s m f1 s1 m1,
    uncurry_rel_fundefs n f s m f1 s1 m1 ->
    used_vars_fundefs f \subset s ->
    unique_bindings_fundefs f ->
    unique_bindings_fundefs f1.
  Proof.
    induction 1; intros; auto.
    apply IHuncurry_rel_fundefs.
    eapply uncurry_fundefs_step_preserves_used_vars; eauto.
    eapply uncurry_fundefs_step_preserves_unique_bindings; eauto.
  Qed.

  Lemma uncurry_rel_maintains_bindings_fn: forall n e s m e1 s1 m1,
    uncurry_rel n e s m e1 s1 m1 ->
    used_vars e \subset s -> forall a,
    In _ (bound_var e1) a ->
    In _ s a ->
    In _ (bound_var e) a.
  Proof.
    induction 1; intros; auto.
    eapply uncurry_step_maintains_bindings_fn; eauto.
    eapply IHuncurry_rel; eauto.
    eapply uncurry_step_preserves_used_vars; eauto.
    eapply uncurry_step_s_nondecreasing; eauto.
  Qed.

  Lemma uncurry_fundefs_rel_maintains_bindings_fn: forall n f s m f1 s1 m1,
    uncurry_rel_fundefs n f s m f1 s1 m1 ->
    used_vars_fundefs f \subset s -> forall a,
    In _ (bound_var_fundefs f1) a ->
    In _ s a ->
    In _ (bound_var_fundefs f) a.
  Proof.
    induction 1; intros; auto.
    eapply uncurry_fundefs_step_maintains_bindings_fn; eauto.
    eapply IHuncurry_rel_fundefs; eauto.
    eapply uncurry_fundefs_step_preserves_used_vars; eauto.
    eapply uncurry_fundefs_step_s_nondecreasing; eauto.
  Qed.

  Lemma uncurry_rel_maintains_used_vars_fn: forall n e s m e1 s1 m1,
    uncurry_rel n e s m e1 s1 m1 ->
    used_vars e \subset s -> forall a,
    In _ (used_vars e1) a ->
    In _ s a ->
    In _ (used_vars e) a.
  Proof.
    induction 1; intros; auto.
    eapply uncurry_step_maintains_used_vars_fn; eauto.
    eapply IHuncurry_rel; eauto.
    eapply uncurry_step_preserves_used_vars; eauto.
    eapply uncurry_step_s_nondecreasing; eauto.
  Qed.

  Lemma uncurry_fundefs_rel_maintains_used_vars_fn: forall n f s m f1 s1 m1,
    uncurry_rel_fundefs n f s m f1 s1 m1 ->
    used_vars_fundefs f \subset s -> forall a,
    In _ (used_vars_fundefs f1) a ->
    In _ s a ->
    In _ (used_vars_fundefs f) a.
  Proof.
    induction 1; intros; auto.
    eapply uncurry_fundefs_step_maintains_used_vars_fn; eauto.
    eapply IHuncurry_rel_fundefs; eauto.
    eapply uncurry_fundefs_step_preserves_used_vars; eauto.
    eapply uncurry_fundefs_step_s_nondecreasing; eauto.
  Qed.

  Lemma app_ctx_uncurry_rel : forall n c e s m e1 s1 m1,
    used_vars (c |[ e ]|) \subset s ->
    uncurry_rel n e s m e1 s1 m1 ->
    uncurry_rel n (c |[ e ]|) s m (c |[ e1 ]|) s1 m1.
  Proof.
    induction n; [inversion 2; subst; constructor|].
    intros c e s m e1 s1 m1 Hused Hrel.
    inv Hrel.
    econstructor.
    apply app_ctx_uncurry_step; eauto.
    apply IHn; auto.
    eapply uncurry_step_preserves_used_vars.
    apply app_ctx_uncurry_step. all: eauto.
  Qed.

  Lemma app_ctx_uncurry_rel_fundefs : forall n f e s m e1 s1 m1,
    used_vars_fundefs (f <[ e ]>) \subset s ->
    uncurry_rel n e s m e1 s1 m1 ->
    uncurry_rel_fundefs n (f <[ e ]>) s m (f <[ e1 ]>) s1 m1.
  Proof.
    induction n; [inversion 2; subst; constructor|].
    intros f e s m e1 s1 m1 Hused Hrel.
    inv Hrel.
    econstructor.
    apply app_ctx_uncurry_fundefs_step; eauto.
    apply IHn; auto.
    eapply uncurry_fundefs_step_preserves_used_vars.
    apply app_ctx_uncurry_fundefs_step. all: eauto.
  Qed.

  Lemma uncurry_rel_correct : forall n k e s m e1 s1 m1,
    unique_bindings e ->
    unique_bindings e1 -> (* TODO: remove this assumption *)
    used_vars e \subset s ->
    used_vars e1 \subset s1 -> (* TODO: remove this assumption *)
    uncurry_rel n e s m e1 s1 m1 -> ctx_preord_exp k e e1.
  Proof.
    induction n; intros; intros rho rho1 pr cenv Henv; inv H3; [now apply preord_exp_refl|].
    assert (unique_bindings e2) by (eapply uncurry_step_preserves_unique_bindings; eauto).
    assert (used_vars e2 \subset s2) by (eapply uncurry_step_preserves_used_vars; eauto).
    eapply preord_exp_trans.
    eapply uncurry_step_correct; [| | | |apply H5|apply Henv]; auto.
    intros; eapply IHn; [| | | |apply H6|apply preord_env_P_refl]; auto.
  Qed.
    
  Transparent bind ret.

  (* Helper functions to extract fields from state *)
  Definition next_free (s : stateType) : var :=
    match s with (y, b, aenv, fenv, ft, lm, s) => y end.
  Definition already_uncurried (s : stateType) : localMap :=
    match s with (y, b, aenv, fenv, ft, lm, s) => lm end.

  (* This identity is useful for the Ecase case -- see below *)
  Lemma st_eq_Ecase {S} (m1 : state S (list (cTag * exp))) (x : var) y :
    st_eq
      (bind (bind m1 (fun ys => ret (y :: ys))) (fun ys' => ret (Ecase x ys')))
      (e <- (ys <- m1 ;;
             ret (Ecase x ys)) ;;
       match e with
         | Ecase x ys =>
           ret (Ecase x (y :: ys))
         | _ => ret e
       end).
  Proof.
    unfold pbind, ret.
    intros s. simpl. destruct (runState m1 s). reflexivity.
  Qed.

  (* arms of a case block are preserved by uncurrying *)
  Lemma uncurry_exp_Ecase x l :
    {{ fun _ => True }}
      uncurry_exp (Ecase x l)
    {{ fun _ e' _ => exists l',
         e' = Ecase x l' /\ Forall2 (fun p p' => fst p = fst p') l l'
    }}.
  Proof.
    Opaque bind ret.
    induction l.
    - simpl. eapply bind_triple with (fun _ x0 _ => x0 = []).
      + apply return_triple. auto.
      + intros. apply return_triple. intros. subst.
        exists []. split; auto.
    - destruct a. simpl. setoid_rewrite assoc. eapply bind_triple.
      + apply post_trivial.
      + intros e' s. rewrite st_eq_Ecase.
        eapply bind_triple.
        * apply IHl.
        * unfold triple. intros. destruct H as [l' [HL HR]]. subst.
          Transparent ret. simpl.
          exists ((c, e') :: l'). split. reflexivity.
          auto.
  Qed.

  Opaque pbind bind ret.

  Lemma app_l_injective : forall {A} (l : list A) r1 r2, l ++ r1 = l ++ r2 -> r1 = r2.
  Proof.
    induction l; [easy|intros r1 r2 Heq].
    apply IHl.
    now inv Heq.
  Qed.

  Lemma app_ctx_f_injective_mut :
    (forall c, (fun c => forall e e1, c |[ e ]| = c |[ e1 ]| -> e = e1) c) /\
    (forall f, (fun f => forall e e1, f <[ e ]> = f <[ e1 ]> -> e = e1) f).
  Proof. (* with eauto with Ensembles_DB.*)
    exp_fundefs_ctx_induction IHe IHf; simpl;
      try rename e into c;
      try intros arms e e1 H;
      try intros e e1 H;
      try easy; (* Hole_c *)
      try solve [apply IHe; now inv H|apply IHf; now inv H].
    (* Ecase_c *)
    apply IHe.
    inv H.
    apply app_l_injective in H1.
    now inv H1.
  Qed.

  Corollary app_ctx_f_injective : forall c e e1, c |[ e ]| = c |[ e1 ]| -> e = e1.
  Proof. apply app_ctx_f_injective_mut. Qed.

  Corollary app_f_ctx_f_injective : forall f e e1, f <[ e ]> = f <[ e1 ]> -> e = e1.
  Proof. apply app_ctx_f_injective_mut. Qed.

  Definition from_fresh st := fun a => (a < next_free st)%positive.

  Lemma pre_eq_state_lr : forall (A S : Type) (P : S -> Prop) (Q : S -> A -> S -> Prop) (e : state S A),
    (forall s : S, P s -> {{fun s' : S => s = s'}} e {{fun s' a s1 => s = s' -> Q s' a s1}}) ->
    {{P}} e {{Q}}.
  Proof.
    unfold triple; intros.
    specialize H with (s := i).
    specialize H with (i0 := i).
    destruct (runState e i).
    firstorder.
  Qed.

  Lemma pre_post_copy : forall (A S : Type) (P : S -> Prop) (Q : S -> A -> S -> Prop) (e : state S A),
    {{P}} e {{fun s a s1 => P s /\ Q s a s1}} <->
    {{P}} e {{Q}}.
  Proof.
    unfold triple; split; intros;
      destruct (runState e i) eqn:eq; try split; auto;
      specialize H with (i := i); rewrite eq in H; firstorder.
  Qed.

  Lemma bind_triple' : forall (A B S : Type) (m : state S A) (f : A -> state S B) (pre : S -> Prop)
    (post : S -> B -> S -> Prop) (post' : S -> A -> S -> Prop),
    {{pre}} m {{fun i x i' => pre i /\ post' i x i'}} ->
    (forall (x : A) (i : S),
      {{fun i' => pre i /\ post' i x i'}}
        f x
        {{fun _ : S => post i}}) ->
    {{pre}} bind m f {{post}}.
  Proof. intros; eapply bind_triple; eauto. Qed.

  Check bind_triple.

  Lemma triple_consequence : forall (A S : Type) (P P' : S -> Prop) (Q Q' : S -> A -> S -> Prop) (e : state S A),
    {{P}} e {{Q}} ->
    (forall i : S, P' i -> P i) ->
    (forall (i : S) (x : A) (i' : S), P i -> Q i x i' -> Q' i x i') ->
    {{P'}} e {{Q'}}.
  Proof. intros. eapply pre_strenghtening; [|eapply post_weakening]; eauto. Qed.

  Lemma uncurry_rel_fundefs_Efun : forall n f s m f1 s1 m1 e,
    uncurry_rel_fundefs n f s m f1 s1 m1 ->
    uncurry_rel n (Efun f e) s m (Efun f1 e) s1 m1.
  Proof.
    induction n; intros; inv H; auto.
    eapply IHn in H2.
    econstructor; eauto.
  Qed.

  Lemma uncurry_step_Ecase_l : forall v arms s m arms1 s1 m1,
    uncurry_step (Ecase v arms) s m (Ecase v arms1) s1 m1 -> exists l c e e1 r,
    arms = l ++ (c, e) :: r /\ arms1 = l ++ (c, e1) :: r /\ uncurry_step e s m e1 s1 m1.
  Proof.
    induction arms; intros; inv H.
    exists [], c, e, e1, arms; eauto.
    apply IHarms in H8.
    destruct H8 as [l [c [e [e1 [r [Harms [Harms2 Hstep]]]]]]].
    exists (a :: l), c, e, e1, r; split; [|split]; simpl; now f_equal.
  Qed.

  Lemma uncurry_rel_Ecase_l : forall n v arms s m arms1 s1 m1 c e,
    uncurry_rel n (Ecase v arms) s m (Ecase v arms1) s1 m1 ->
    uncurry_rel n (Ecase v ((c, e) :: arms)) s m (Ecase v ((c, e) :: arms1)) s1 m1.
  Proof.
    induction n; intros.
    - now inv H.
    - inv H.
      inv H1.
      + econstructor.
        apply uncurry_case_arms.
        apply uncurry_case_expr; eauto.
        now apply IHn.
      + econstructor.
        do 2 apply uncurry_case_arms; eauto.
        apply IHn; eauto.
  Qed.

  Lemma uncurry_rel_fundefs_Fcons : forall n f' t v f s m f1 s1 m1 e,
    uncurry_rel_fundefs n f s m f1 s1 m1 ->
    uncurry_rel_fundefs n (Fcons f' t v e f) s m (Fcons f' t v e f1) s1 m1.
  Proof.
    induction n; intros; inv H; auto.
    eapply IHn in H2.
    econstructor; eauto.
  Qed.

  Lemma uncurry_rel_case : forall n v l s m e s1 m1,
    uncurry_rel n (Ecase v l) s m e s1 m1 -> exists l', e = Ecase v l'.
  Proof.
    induction n; intros.
    - inv H; eauto.
    - inv H; inv H1; now apply IHn in H2.
  Qed.

  Lemma already_uncurried_triple : forall s f,
    {{fun s' => s = s'}} uncurry.already_uncurried f
    {{fun s a s1 => s = s1 /\
        a = match M.get f (already_uncurried s) with
              Some true => true
            | _ => false
            end }}.
  Proof.
    intros; eapply bind_triple.
    eapply pre_strenghtening; [|apply get_triple]; firstorder.
    simpl.
    intros s0 s0'; eapply pre_eq_state_lr.
    intros s0'' [Hs0 Hs0']; subst.
    destruct s0'', p, p, p, p, p; simpl.
    destruct (M.get f l) eqn:Hget; [destruct b0|]; apply return_triple; firstorder.
  Qed.

  Lemma next_free_not_In_from_fresh : forall s, ~ In _ (from_fresh s) (next_free s).
  Proof.
    intros s.
    destruct s, p, p, p, p, p; unfold from_fresh, In; simpl.
    apply Pos.lt_irrefl.
  Qed.

  Lemma copyVar_triple : forall s f,
    {{fun s' => s = s'}} uncurry.copyVar f
    {{fun s a s1 =>
        from_fresh s1 <--> a |: from_fresh s /\
        already_uncurried s1 = already_uncurried s /\
        a = next_free s}}.
  Proof.
    intros; eapply bind_triple.
    eapply pre_strenghtening; [|apply get_triple]; firstorder.
    intros s0 s0'; eapply pre_eq_state_lr.
    intros s0'' [Hs0 Hs0']; subst.
    destruct s0'', p, p, p, p, p.
    eapply bind_triple.
    eapply pre_strenghtening; [|apply put_triple]; firstorder.
    intros [] s0'; apply return_triple; intros; subst; split; auto.
    unfold from_fresh; simpl.
    split; unfold Included, In; intros.
    - destruct (Pos.eqb x v) eqn:Hxv.
      apply Peqb_true_eq in Hxv; subst; now left.
      right; unfold In.
      rewrite <- Pplus_one_succ_r in H.
      rewrite Pos.lt_succ_r in H.
      rewrite Pos.le_lteq in H; destruct H; auto; subst.
      now rewrite Pos.eqb_neq in Hxv.
    - inv H; [inv H0|].
      all: rewrite <- Pplus_one_succ_r; rewrite Pos.lt_succ_r; rewrite Pos.le_lteq; auto.
  Qed.

  Lemma copyVars_triple : forall l s,
    {{fun s' => s = s'}} uncurry.copyVars l
    {{fun s l1 s1 =>
        from_fresh s1 <--> from_fresh s :|: FromList l1 /\
        already_uncurried s1 = already_uncurried s /\
        fresh_copies (from_fresh s) l1 /\
        length l = length l1}}.
  Proof with eauto with Ensembles_DB.
    induction l.
    - intros s; apply return_triple; intros s' Hs'; split; [|split]; auto; [|split]; auto.
      rewrite FromList_nil...
      unfold fresh_copies; split; [|constructor].
      rewrite FromList_nil.
      apply Disjoint_Empty_set_r.
    - intros s; simpl.
      eapply bind_triple.
      apply copyVar_triple.
      intros a0 s0; apply pre_eq_state_lr.
      intros s1 [Hs1 Ha0].
      eapply bind_triple.
      apply IHl.
      intros l1 s2; apply pre_eq_state_lr.
      intros s3 [Hs3 Hl1].
      apply return_triple.
      intros s3' Hs3' _ Hs1'; subst.
      split; [|split]; [| |split]; [| |split|].
      + rewrite FromList_cons.
        rewrite Hs3.
        rewrite Hs1...
      + destruct Ha0, Hl1.
        now rewrite H1, H.
      + constructor.
        intros x contra; inv contra.
        inv H0.
        destruct Ha0 as [Ha0 Ha0']; subst.
        unfold from_fresh, next_free, In in H; destruct s0, p, p, p, p, p in H.
        revert H; now apply Pos.lt_irrefl.
        destruct Hl1 as [Heq [[H0 HL] HR]].
        inv H0; contradiction (H2 x).
        rewrite Hs1.
        split; auto.
      + destruct Hl1 as [Heq [[H HL] HR]]; constructor; auto.
        destruct Ha0 as [Ha0 Ha0']; subst.
        intros contra.
        inv H.
        contradiction (H0 (next_free s0)).
        split; auto.
        rewrite Hs1; auto.
      + simpl; destruct Hl1 as [H1 [H2 H3]]; auto.
  Qed.

  Lemma mark_as_uncurried_triple : forall s v,
    {{fun s' => s = s'}} uncurry.mark_as_uncurried v
    {{fun s _ s1 =>
        from_fresh s1 = from_fresh s /\
        already_uncurried s1 = M.set v true (already_uncurried s) }}.
  Proof.
    intros; eapply bind_triple.
    eapply pre_strenghtening; [|apply get_triple]; try firstorder.
    intros s' s''.
    destruct s', p, p, p, p, p.
    apply pre_eq_state_lr.
    intros s1 [Hs1 Hs1']; subst s''.
    eapply triple_consequence.
    apply put_triple.
    now intros.
    simpl; intros; subst; split; auto.
  Qed.

  Lemma click_triple : forall s,
    {{fun s' => s = s'}} uncurry.click
    {{fun s _ s1 =>
        from_fresh s1 = from_fresh s /\
        already_uncurried s1 = already_uncurried s }}.
  Proof.
    intros; eapply bind_triple.
    eapply pre_strenghtening; [|apply get_triple]; try firstorder.
    intros s' s''.
    destruct s', p, p, p, p, p.
    apply pre_eq_state_lr.
    intros s1 [Hs1 Hs1']; subst s''.
    eapply triple_consequence.
    apply put_triple.
    now intros.
    simpl; intros; subst; split; auto.
  Qed.

  Lemma markToInline_triple : forall s n f k,
    {{fun s' => s = s'}} uncurry.markToInline n f k
    {{fun s _ s1 =>
        from_fresh s1 = from_fresh s /\
        already_uncurried s1 = already_uncurried s }}.
  Proof.
    intros; eapply bind_triple.
    eapply pre_strenghtening; [|apply get_triple]; try firstorder.
    intros s' s''.
    destruct s', p, p, p, p, p.
    apply pre_eq_state_lr.
    intros s1 [Hs1 Hs1']; subst s''.
    eapply triple_consequence.
    apply put_triple.
    now intros.
    simpl; intros; subst; split; auto.
  Qed.

  Lemma get_fTag_triple : forall s n,
    {{fun s' => s = s'}} uncurry.get_fTag n
    {{fun s _ s1 =>
        from_fresh s1 = from_fresh s /\
        already_uncurried s1 = already_uncurried s }}.
  Proof.
    intros; eapply bind_triple.
    eapply pre_strenghtening; [|apply get_triple]; try firstorder.
    intros s' s''.
    destruct s', p, p, p, p, p.
    apply pre_eq_state_lr.
    intros s1 [Hs1 Hs1']; subst s''.
    simpl; destruct (M.get (N.succ_pos n) a).
    - apply return_triple; intros; subst; split; auto.
    - eapply bind_triple.
      eapply pre_strenghtening; [|apply put_triple]; try firstorder.
      intros; apply return_triple; intros; subst; split; auto.
  Qed.

  Lemma uncurry_step_subst_mut :
    let P := (fun e s m e1 s1 m1 => forall e' s' m' e1' s1' m1', 
      e = e' -> s <--> s' -> m = m' -> e1 = e1' -> s1 <--> s1' -> m1 = m1' ->
      uncurry_step e' s' m' e1' s1' m1') in
    let Q := (fun f s m f1 s1 m1 => forall f' s' m' f1' s1' m1', 
      f = f' -> s <--> s' -> m = m' -> f1 = f1' -> s1 <--> s1' -> m1 = m1' ->
      uncurry_fundefs_step f' s' m' f1' s1' m1') in
    (forall e s m e1 s1 m1, uncurry_step e s m e1 s1 m1 -> P e s m e1 s1 m1) /\
    (forall f s m f1 s1 m1, uncurry_fundefs_step f s m f1 s1 m1 -> Q f s m f1 s1 m1).
  Proof with eauto with Ensembles_DB.
    intros P Q.
    uncurry_step_induction_mut P Q IHstep IH; subst P; subst Q; simpl in *; intros; try solve
    [destruct e'; destruct e1'; try congruence; inv H; inv H2; constructor; apply IH; auto
    |destruct f'; destruct f1'; try congruence; inv H; inv H2; constructor; apply IH; auto].
    destruct f'; destruct f1'; try congruence.
    inv H8; inv H11.
    constructor; unfold fresh_copies in *; destruct H2, H4; try split; auto;
      try rewrite <- H9; try rewrite H12; try rewrite H7...
    rewrite <- H12.
    rewrite H7...
    rewrite <- H7; rewrite H12...
  Qed.

  Corollary uncurry_fundefs_step_subst : forall f s m f1 s1 m1 f' s' m' f1' s1' m1',
    uncurry_fundefs_step f s m f1 s1 m1 ->
    f = f' -> s <--> s' -> m = m' -> f1 = f1' -> s1 <--> s1' -> m1 = m1' ->
    uncurry_fundefs_step f' s' m' f1' s1' m1'.
  Proof. intros; eapply uncurry_step_subst_mut; eauto. Qed.

  Corollary uncurry_step_subst : forall e s m e1 s1 m1 e' s' m' e1' s1' m1',
    uncurry_step e s m e1 s1 m1 ->
    e = e' -> s <--> s' -> m = m' -> e1 = e1' -> s1 <--> s1' -> m1 = m1' ->
    uncurry_step e' s' m' e1' s1' m1'.
  Proof. intros; eapply uncurry_step_subst_mut; eauto. Qed.

  Lemma uncurry_corresp_mut :
    let P e uncurry_e :=
      {{ fun st => unique_bindings e /\ used_vars e \subset from_fresh st }}
        uncurry_e
      {{ fun st e1 st1 => exists n,
           uncurry_rel n
                       e (from_fresh st) (already_uncurried st)
                       e1 (from_fresh st1) (already_uncurried st1)
      }} in
    let Q f uncurry_f :=
      {{ fun st => unique_bindings_fundefs f /\ used_vars_fundefs f \subset from_fresh st }}
        uncurry_f
      {{ fun st f1 st1 => exists n,
           uncurry_rel_fundefs n
                               f (from_fresh st) (already_uncurried st)
                               f1 (from_fresh st1) (already_uncurried st1)
      }} in
    (forall e, P e (uncurry_exp e)) /\ (forall f, Q f (uncurry_fundefs f)).
  Proof with eauto with Ensembles_DB.
    intros P Q.
    Opaque uncurry_exp uncurry_fundefs.
    uncurry_induction_mut P Q IHe IHf IHeq; subst P; subst Q; simpl in *.
    Transparent uncurry_exp uncurry_fundefs.
    - (* Econstr *)
      eapply pre_eq_state_lr; intros st [Huniq Hused].
      eapply bind_triple.
      eapply pre_strenghtening; [|eapply IHe].
      simpl; intros; subst.
      split; [now inv Huniq|].
      eapply Included_trans; [|apply Hused].
      rewrite used_vars_Econstr...
      intros e1 st1; apply return_triple.
      intros st2 [n Hrel] Hst; subst st1; rename st2 into st1.
      assert (from_fresh st \subset from_fresh st1) by (eapply uncurry_rel_s_nondecreasing; eauto).
      destruct n; inv Hrel.
      exists 0; constructor.
      exists (S n); econstructor.
      constructor; eauto.
      apply app_ctx_uncurry_rel with (c := Econstr_c x c vs Hole_c).
      eapply uncurry_step_preserves_used_vars; eauto.
      apply app_ctx_uncurry_step with (c := Econstr_c x c vs Hole_c). all: eauto.
    - (* Ecase [] *)
      eapply pre_eq_state_lr; intros st [Huniq Hused].
      eapply bind_triple with (post' := fun s a s1 => s = s1 /\ a = []).
      apply return_triple; auto.
      intros a st1.
      apply return_triple.
      intros st2 [Hst2 Ha] Hst; subst; rename st2 into st1.
      exists 0; constructor.
    - (* Ecase :: *)
      eapply pre_eq_state_lr; intros st [Huniq Hused].
      Transparent pbind. setoid_rewrite assoc. Opaque pbind.
      eapply bind_triple'.
      rewrite pre_post_copy.
      eapply pre_strenghtening; [|apply IHe].
      intros st' Hst'; subst; split; [now inv Huniq|].
      eapply Included_trans; eauto; rewrite used_vars_Ecase_cons...
      intros e' st'.
      Transparent pbind. simpl; rewrite st_eq_Ecase; simpl in IHf. Opaque pbind.
      eapply pre_eq_state_lr; intros st0 [Hst [n_e He]]; subst; eapply bind_triple'.
      rewrite pre_post_copy.
      eapply pre_strenghtening; [|eapply IHf].
      intros st0' Hst0'; subst; split; [now inv Huniq|].
      apply Included_trans with (s2 := from_fresh st').
      eapply Included_trans; eauto; rewrite used_vars_Ecase_cons...
      eapply uncurry_rel_s_nondecreasing; eauto.
      intros c' st0'; apply pre_eq_state_lr.
      intros st1 [Hst0 [n_c Hc]]; subst.
      pose (Hc' := Hc).
      apply uncurry_rel_case in Hc'; destruct Hc' as [l' Hc']; subst.
      eapply return_triple.
      intros st1' Hst1 _ _ _; subst.
      exists (n_c + n_e).
      eapply uncurry_rel_compose.
      eapply app_ctx_uncurry_rel with (c := Ecase_c x [] c Hole_c t); eauto.
      now apply uncurry_rel_Ecase_l.
    - (* Eproj *)
      eapply pre_eq_state_lr; intros st [Huniq Hused].
      eapply bind_triple.
      eapply pre_strenghtening; [|eapply IHe].
      simpl; intros; subst.
      split; [now inv Huniq|].
      eapply Included_trans; [|apply Hused].
      rewrite used_vars_Eproj...
      intros e1 st'; apply return_triple.
      intros st1 [n1 Hrel] Hst; subst st'.
      assert (from_fresh st \subset from_fresh st1) by (eapply uncurry_rel_s_nondecreasing; eauto).
      destruct n1; inv Hrel.
      exists 0; constructor.
      exists (S n1); econstructor.
      constructor; eauto.
      apply app_ctx_uncurry_rel with (c := Eproj_c x c n y Hole_c).
      eapply uncurry_step_preserves_used_vars; eauto.
      apply app_ctx_uncurry_step with (c := Eproj_c x c n y Hole_c). all: eauto.
    - (* Eapp *)
      apply return_triple; intros.
      exists 0; constructor.
    - (* Eprim *)
      eapply pre_eq_state_lr; intros st [Huniq Hused].
      eapply bind_triple.
      eapply pre_strenghtening; [|eapply IHe].
      simpl; intros; subst.
      split; [now inv Huniq|].
      eapply Included_trans; [|apply Hused].
      rewrite used_vars_Eprim...
      intros e1 st1; apply return_triple.
      intros st2 [n Hrel] Hst; subst st1; rename st2 into st1.
      assert (from_fresh st \subset from_fresh st1) by (eapply uncurry_rel_s_nondecreasing; eauto).
      destruct n; inv Hrel.
      exists 0; constructor.
      exists (S n); econstructor.
      constructor; eauto.
      apply app_ctx_uncurry_rel with (c := Eprim_c x p xs Hole_c).
      eapply uncurry_step_preserves_used_vars; eauto.
      apply app_ctx_uncurry_step with (c := Eprim_c x p xs Hole_c). all: eauto.
    - (* Efun *)
      eapply pre_eq_state_lr; intros st [Huniq Hused].
      eapply bind_triple'. 
      rewrite pre_post_copy.
      eapply pre_strenghtening; [|apply IHf].
      intros i Hi; subst.
      split; [now inv Huniq|].
      eapply Included_trans; eauto.
      rewrite used_vars_Efun...
      intros f2' st0.
      eapply pre_eq_state_lr.
      intros s [Hst0 [n_f2 Hf2]]; subst.
      eapply bind_triple'.
      rewrite pre_post_copy.
      eapply pre_strenghtening; [|apply IHe].
      intros i Hi; subst.
      split; [now inv Huniq|].
      eapply Included_trans with (s2 := from_fresh st0).
      eapply Included_trans; eauto.
      rewrite used_vars_Efun...
      eapply uncurry_fundefs_rel_s_nondecreasing; eauto.
      intros e' st1.
      apply pre_eq_state_lr.
      intros s0 [Hst1 [n_e He]]; subst.
      eapply return_triple.
      intros s0' Hs0 _ _ _; subst.
      exists (n_e + n_f2).
      eapply uncurry_rel_compose.
      eapply uncurry_rel_fundefs_Efun; eauto.
      eapply app_ctx_uncurry_rel with (c := Efun1_c f2' Hole_c); simpl; eauto.
      rewrite used_vars_Efun.
      apply Union_Included.
      eapply uncurry_fundefs_rel_preserves_used_vars; eauto.
      eapply Included_trans; eauto.
      rewrite used_vars_Efun...
      eapply Included_trans with (s2 := from_fresh st0).
      eapply Included_trans; eauto.
      rewrite used_vars_Efun...
      eapply uncurry_fundefs_rel_s_nondecreasing; eauto.
    - (* Ehalt *)
      apply return_triple; intros.
      exists 0; constructor.
    - (* Fnil *)
      apply return_triple; intros.
      exists 0; constructor.
    - (* Fcons *)
      eapply pre_eq_state_lr; intros st [Huniq Hused].
      eapply bind_triple'. rewrite pre_post_copy.
      eapply pre_strenghtening; [|apply IHf].
      intros st0 Hst0; subst; split; [now inv Huniq|].
      eapply Included_trans; eauto.
      rewrite used_vars_Fcons...
      intros fds' st'.
      eapply pre_eq_state_lr.
      intros st0 [Hst [n_fds Hfds]]; subst.
      eapply bind_triple'.
      rewrite pre_post_copy.
      eapply pre_strenghtening; [|apply IHe]; auto.
      intros st0' Hst0'; subst; split; auto.
      inv Huniq; inv H11; now inv H2.
      apply Included_trans with (s2 := from_fresh st').
      eapply Included_trans; eauto.
      repeat (rewrite used_vars_Fcons + rewrite used_vars_Efun + rewrite used_vars_Eapp)...
      eapply uncurry_fundefs_rel_s_nondecreasing; eauto.
      intros e0' st0'; apply pre_eq_state_lr.
      intros st1 [Hst1 [n_e0 He0]]; subst.
      eapply bind_triple'.
      rewrite pre_post_copy.
      apply already_uncurried_triple.
      intros getb st1'; simpl.
      apply pre_eq_state_lr; intros st1'' [Hst1 [Hst1' Hget]]; subst st1'; subst st1''.
      destruct (eq_var k k &&
                eq_var g g &&
                negb (occurs_in_exp g ge) &&
                negb (occurs_in_exp k ge) &&
                negb getb) eqn:Hpred.
      + eapply bind_triple'.
        rewrite pre_post_copy. apply copyVars_triple.
        intros l0' st1'. apply pre_eq_state_lr.
        intros st2 [Hst1 [Hst2 [Hst2_m [Hl0' Hlen_l0']]]]; subst st1'.
        eapply bind_triple'.
        rewrite pre_post_copy. apply copyVars_triple.
        intros l' st2'. apply pre_eq_state_lr.
        intros st3 [Hst2' [Hst3 [Hst3_m [Hl' Hlen_l']]]]; subst st2'.
        eapply bind_triple'. rewrite pre_post_copy.
        apply copyVar_triple.
        intros v' st3'. apply pre_eq_state_lr.
        intros st4 [Hst3' [Hst4 [Hst4_m Hv]]]; subst st3'.
        eapply bind_triple'. rewrite pre_post_copy.
        apply mark_as_uncurried_triple.
        intros [] st4'. apply pre_eq_state_lr.
        intros st5 [Hst4' [Hst5 Hst5_m]]; subst st4'.
        eapply bind_triple'. rewrite pre_post_copy.
        apply click_triple.
        intros [] st5'. apply pre_eq_state_lr.
        intros st6 [Hst5' [Hst6 Hst6_m]]; subst st5'.
        eapply bind_triple'. rewrite pre_post_copy.
        apply markToInline_triple.
        intros [] st6'. apply pre_eq_state_lr.
        intros st7 [Hst6' [Hst7 Hst7_m]]; subst st6'.
        eapply bind_triple'. rewrite pre_post_copy.
        apply get_fTag_triple.
        intros ft' st7'. apply pre_eq_state_lr.
        intros st8 [Hst7' [Hst8 Hst8_m]]; subst st7'.
        apply return_triple.
        intros st8' Hst8' _ _ _ _ _ _ _ _ _ _ _; subst st8'.
        assert (Hfds_ctx :
          uncurry_rel_fundefs n_fds
            (Fcons f ft (k :: fv)
                   (Efun (Fcons g gt gv ge Fnil) (Eapp k kt [g]))
                   fds)
            (from_fresh st')
            (already_uncurried st')
            (Fcons f ft (k :: fv)
                   (Efun (Fcons g gt gv ge Fnil) (Eapp k kt [g]))
                   fds')
            (from_fresh st0')
            (already_uncurried st0')) by now apply uncurry_rel_fundefs_Fcons.
        exists (1 + n_e0 + n_fds).
        eapply uncurry_rel_fundefs_compose; eauto.
        eapply uncurry_rel_fundefs_compose.
        eapply app_ctx_uncurry_rel_fundefs
          with (f :=
                  Fcons1_c f ft (k :: fv)
                           (Efun2_c (Fcons1_c g gt gv Hole_c Fnil)
                                    (Eapp k kt [g])) fds'); eauto.
        simpl; eapply uncurry_fundefs_rel_preserves_used_vars; eauto.
        econstructor; [|constructor].
        repeat match goal with
          [ H : ?a && ?b = true |- _ ] => apply andb_prop in H; destruct H
        | [ H : negb ?a = true |- _ ] => rewrite negb_true_iff in H
        | [ H : eq_var ?a ?b = true |- _ ] => rewrite Pos.eqb_eq in H; subst a
        | [ H : occurs_in_exp ?a ?e = false |- _ ] =>
          rewrite not_occurs_in_exp_iff_used_vars in H
        end.
        eapply uncurry_fundefs_step_subst.
        apply uncurry_fundefs_curried with (s' := from_fresh st8).
        13: reflexivity.
        all:
          unfold fresh_copies in *;
          try rewrite <- Hst2 in *;
          try rewrite <- Hst3 in *;
          try setoid_rewrite <- Hst3;
          eauto with Ensembles_DB;
          try match goal with
            [ _ : _ |- occurs_in_exp ?a ?e = false ] =>
              apply not_occurs_in_exp_iff_used_vars; intros contra
          | [ _ : ?a = next_free ?s |- ~ In _ (from_fresh ?s) ?a ] =>
              subst a; apply next_free_not_In_from_fresh
        end.
        * contradiction H2.
          eapply uncurry_rel_maintains_used_vars_fn; eauto.
          eapply uncurry_rel_preserves_used_vars; eauto.
          apply Included_trans with (s2 := from_fresh st').
          eapply Included_trans; eauto.
          repeat (rewrite used_vars_Fcons + rewrite used_vars_Efun)...
          eapply uncurry_fundefs_rel_s_nondecreasing; eauto.
          apply Singleton_Included_r.
          apply Included_trans with (s2 := from_fresh st').
          eapply Included_trans; eauto.
          repeat (rewrite used_vars_Fcons + rewrite used_vars_Efun +
                  rewrite used_vars_Eapp + rewrite FromList_cons)...
          eapply uncurry_fundefs_rel_s_nondecreasing; eauto.
        * contradiction H1.
          eapply uncurry_rel_maintains_used_vars_fn; eauto.
          eapply uncurry_rel_preserves_used_vars; eauto.
          apply Included_trans with (s2 := from_fresh st').
          eapply Included_trans; eauto.
          repeat (rewrite used_vars_Fcons + rewrite used_vars_Efun)...
          eapply uncurry_fundefs_rel_s_nondecreasing; eauto.
          apply Singleton_Included_r.
          apply Included_trans with (s2 := from_fresh st').
          eapply Included_trans; eauto.
          repeat (rewrite used_vars_Fcons + rewrite used_vars_Efun +
                  rewrite used_vars_Eapp + rewrite FromList_cons)...
          eapply uncurry_fundefs_rel_s_nondecreasing; eauto.
        * rewrite Hst8, Hst7, Hst6, Hst5, Hst4...
        * now rewrite Hst8_m, Hst7_m, Hst6_m, Hst5_m, Hst4_m, Hst3_m, Hst2_m.
      + apply return_triple.
        intros st1' Hst1 _ _ _ _; subst st1'.
        exists (n_e0 + n_fds).
        eapply uncurry_rel_fundefs_compose.
        apply uncurry_rel_fundefs_Fcons; eauto.
        apply app_ctx_uncurry_rel_fundefs
          with (f := Fcons1_c f ft (k :: fv)
                              (Efun2_c (Fcons1_c g gt gv Hole_c Fnil) (Eapp k kt [g])) fds'); auto.
        simpl; repeat (rewrite used_vars_Fcons + rewrite used_vars_Efun + rewrite used_vars_Eapp).
        intros a Ha; inv Ha.
        revert H; apply Included_trans with (s2 := from_fresh st').
        eapply Included_trans; eauto.
        simpl; repeat (rewrite used_vars_Fcons + rewrite used_vars_Efun + rewrite used_vars_Eapp)...
        eapply uncurry_fundefs_rel_s_nondecreasing; eauto.
        eapply uncurry_fundefs_rel_preserves_used_vars; eauto.
        eapply Included_trans; eauto.
        repeat (rewrite used_vars_Fcons + rewrite used_vars_Efun + rewrite used_vars_Eapp)...
    - (* Fcons2 *)
      eapply pre_eq_state_lr; intros st [Huniq Hused].
      eapply bind_triple'. rewrite pre_post_copy.
      eapply pre_strenghtening; [|apply IHf].
      intros st0 Hst0; subst; split; [now inv Huniq|].
      eapply Included_trans; eauto.
      rewrite used_vars_Fcons...
      intros fds' st'.
      eapply pre_eq_state_lr.
      intros st0 [Hst [n_fds Hfds]]; subst.
      eapply bind_triple'.
      rewrite pre_post_copy.
      eapply pre_strenghtening; [|apply IHe]; auto.
      intros st0' Hst0'; subst; split; auto.
      inv Huniq; inv H11; now inv H2.
      apply Included_trans with (s2 := from_fresh st').
      eapply Included_trans; eauto.
      repeat (rewrite used_vars_Fcons + rewrite used_vars_Efun + rewrite used_vars_Eapp)...
      eapply uncurry_fundefs_rel_s_nondecreasing; eauto.
      intros e0' st0'; apply pre_eq_state_lr.
      intros st1 [Hst1 [n_e0 He0]]; subst.
      eapply bind_triple'.
      rewrite pre_post_copy.
      apply already_uncurried_triple.
      intros getb st1'; simpl.
      apply pre_eq_state_lr; intros st1'' [Hst1 [Hst1' Hget]]; subst st1'; subst st1''.
      assert (Hpred : eq_var k k' &&
                eq_var g g' &&
                negb (occurs_in_exp g ge) &&
                negb (occurs_in_exp k ge) &&
                negb getb = false). {
        destruct IHeq as [Heq|Heq].
        rewrite <- Pos.eqb_neq in Heq.
        unfold eq_var; rewrite Heq; auto.
        rewrite <- Pos.eqb_neq in Heq.
        unfold eq_var; rewrite Heq; repeat rewrite <- andb_assoc; simpl; now rewrite andb_comm.
      }
      rewrite Hpred.
      apply return_triple.
      intros st1' Hst1' _ _ _ _; subst st1'.
      exists (n_e0 + n_fds).
      eapply uncurry_rel_fundefs_compose.
      apply uncurry_rel_fundefs_Fcons; eauto.
      apply app_ctx_uncurry_rel_fundefs
        with (f := Fcons1_c f ft (k :: fv)
                            (Efun2_c (Fcons1_c g gt gv Hole_c Fnil) (Eapp k' kt [g'])) fds'); auto.
      simpl; repeat (rewrite used_vars_Fcons + rewrite used_vars_Efun + rewrite used_vars_Eapp).
      intros a Ha; inv Ha.
      revert H; apply Included_trans with (s2 := from_fresh st').
      eapply Included_trans; eauto.
      simpl; repeat (rewrite used_vars_Fcons + rewrite used_vars_Efun + rewrite used_vars_Eapp)...
      eapply uncurry_fundefs_rel_s_nondecreasing; eauto.
      eapply uncurry_fundefs_rel_preserves_used_vars; eauto.
      eapply Included_trans; eauto.
      repeat (rewrite used_vars_Fcons + rewrite used_vars_Efun + rewrite used_vars_Eapp)...
    - (* Fcons3 *)
      destruct v; simpl.
      + apply pre_eq_state_lr; intros st [Huniq Hused].
        eapply bind_triple'. rewrite pre_post_copy.
        eapply pre_strenghtening; [|apply IHf].
        intros st' Hst'; split; subst st'; [now inv Huniq|].
        eapply Included_trans; eauto; rewrite used_vars_Fcons...
        intros fds' st'; apply pre_eq_state_lr.
        intros st0 [Hst' [n_fds Hfds]]; subst st'.
        eapply bind_triple'. rewrite pre_post_copy.
        eapply pre_strenghtening; [|apply IHe].
        intros st0' Hst0; subst st0'; split; [now inv Huniq|].
        apply Included_trans with (s2 := from_fresh st).
        eapply Included_trans; eauto; rewrite used_vars_Fcons...
        eapply uncurry_fundefs_rel_s_nondecreasing; eauto.
        intros e' st0'; apply return_triple.
        intros st1 [Hst0' [n_e He]] _ _; subst st0'.
        exists (n_e + n_fds); eapply uncurry_rel_fundefs_compose.
        apply uncurry_rel_fundefs_Fcons; eauto.
        apply app_ctx_uncurry_rel_fundefs with (f := Fcons1_c f ft [] Hole_c fds'); auto.
        simpl; rewrite used_vars_Fcons.
        intros a Ha; inv Ha.
        revert H; apply Included_trans with (s2 := from_fresh st).
        eapply Included_trans; eauto; rewrite used_vars_Fcons...
        eapply uncurry_fundefs_rel_s_nondecreasing; eauto.
        eapply uncurry_fundefs_rel_preserves_used_vars; eauto.
        eapply Included_trans; eauto; rewrite used_vars_Fcons...
      + destruct e.
        4: destruct f0; try destruct f1; try destruct e; try destruct l0; try destruct l0.
        all: try solve [
          apply pre_eq_state_lr; intros st [Huniq Hused];
          eapply bind_triple';
            [rewrite pre_post_copy;
             eapply pre_strenghtening; [|apply IHf];
             intros st' Hst'; split; subst st'; [now inv Huniq|];
             eapply Included_trans; eauto; rewrite used_vars_Fcons;
             eauto with Ensembles_DB
            |];
          intros fds' st'; apply pre_eq_state_lr;
          intros st0 [Hst' [n_fds Hfds]]; subst st';
          eapply bind_triple';
            [rewrite pre_post_copy;
             eapply pre_strenghtening; [|apply IHe];
             intros st0' Hst0; subst st0'; split; [now inv Huniq|];
             apply Included_trans with (s2 := from_fresh st);
             [eapply Included_trans; eauto; rewrite used_vars_Fcons; eauto with Ensembles_DB
             |eapply uncurry_fundefs_rel_s_nondecreasing; eauto]
            |];
          intros e' st0'; apply return_triple;
          intros st1 [Hst0' [n_e He]] _ _; subst st0';
          exists (n_e + n_fds); eapply uncurry_rel_fundefs_compose;
            [apply uncurry_rel_fundefs_Fcons; eauto|];
          apply app_ctx_uncurry_rel_fundefs
            with (f := Fcons1_c f ft (v :: v0) Hole_c fds'); auto;
          simpl; rewrite used_vars_Fcons;
          intros a Ha; inv Ha;
          [revert H; apply Included_trans with (s2 := from_fresh st);
           [eapply Included_trans; eauto; rewrite used_vars_Fcons; eauto with Ensembles_DB
           |eapply uncurry_fundefs_rel_s_nondecreasing; eauto]
          |eapply uncurry_fundefs_rel_preserves_used_vars; eauto;
           eapply Included_trans; eauto; rewrite used_vars_Fcons; eauto with Ensembles_DB]].
        contradiction IHeq; do 9 eexists; eauto.
        Grab Existential Variables.
        exact M.Leaf.
        exact M.Leaf.
  Qed.

  Corollary uncurry_exp_corresp : forall e,
    {{ fun st => unique_bindings e /\ used_vars e \subset from_fresh st }}
      uncurry_exp e
    {{ fun st e1 st1 => exists n,
         uncurry_rel n
                     e (from_fresh st) (already_uncurried st)
                     e1 (from_fresh st1) (already_uncurried st1)
    }}.
  Proof. intros; eapply uncurry_corresp_mut; eauto. Qed.
  
  Corollary uncurry_fundefs_corresp : forall f,
    {{ fun st => unique_bindings_fundefs f /\ used_vars_fundefs f \subset from_fresh st }}
      uncurry_fundefs f
    {{ fun st f1 st1 => exists n,
         uncurry_rel_fundefs n
                             f (from_fresh st) (already_uncurried st)
                             f1 (from_fresh st1) (already_uncurried st1)
    }}.
  Proof. intros; eapply uncurry_corresp_mut; eauto. Qed.
  
  Lemma uncurry_exp_correct : forall e,
    {{ fun st => unique_bindings e /\ used_vars e \subset from_fresh st }}
      uncurry_exp e
    {{ fun st e1 st1 => forall k, ctx_preord_exp k e e1 }}.
  Proof.
    intros.
    eapply triple_consequence.
    apply uncurry_exp_corresp.
    - intros st [Huniq Hused]; now split.
    - intros st e' st' [Huniq Hused] [n Hrel].
      intros; eapply uncurry_rel_correct; eauto.
      eapply uncurry_rel_preserves_unique_bindings; eauto.
      eapply uncurry_rel_preserves_used_vars; eauto.
  Qed.

  Lemma uncurry_exp_good_preserving : forall e,
    {{ fun st => closed_exp e /\ unique_bindings e /\ used_vars e \subset from_fresh st }}
      uncurry_exp e
    {{ fun _ e1 _ => closed_exp e1 /\ unique_bindings e1 }}.
  Proof.
    intros.
    apply pre_eq_state_lr; intros s [Hclosed [Huniq Hused]].
    eapply triple_consequence.
    apply uncurry_exp_corresp.
    - intros; subst; split; auto.
    - simpl; intros; subst.
      destruct H; destruct H0; split.
      eapply uncurry_rel_preserves_closed; eauto.
      eapply uncurry_rel_preserves_unique_bindings; eauto.
  Qed.

End uncurry_correct.






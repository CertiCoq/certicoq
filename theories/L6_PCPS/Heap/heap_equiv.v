(* Heap equivalence definitions for L6. Part of the CertiCoq project.
 * Author: Zoe Paraskevopoulou, 2016
 *)

From Coq Require Import NArith.BinNat Relations.Relations MSets.MSets
         MSets.MSetRBT Lists.List omega.Omega Sets.Ensembles Relations.Relations
         Classes.Morphisms.
From CertiCoq.L6 Require Import cps cps_util set_util List_util Ensembles_util functions
        identifiers tactics map_util.

From CertiCoq.L6.Heap Require Import heap heap_defs.

From compcert.lib Require Import Coqlib.

Import ListNotations.

Open Scope Ensembles_scope.

Module HeapEquiv (H : Heap).

  Module Defs := HeapDefs H.

  Import H Defs.HL Defs.

  (** Formalization of heap equivalence *) 
  
  (** Syntactic approximation of results with fuel *)
  Fixpoint res_approx_fuel (n : nat) (r1 : (loc -> loc) * res) (r2 : (loc -> loc) * res) : Prop :=
    let '(b1, (v1, H1)) := r1 in
    let '(b2, (v2, H2)) := r2 in
    match v1, v2 with
      | Loc l1, Loc l2 =>
        b2 l2 = b1 l1 /\
        match get l1 H1 with
          | Some (Constr c vs1) =>
            exists vs2,
              get l2 H2 = Some (Constr c vs2) /\
              forall i, (i < n)%nat ->
                   match n with
                     | 0%nat => True
                     | S n' =>
                       Forall2
                         (fun l1 l2 => res_approx_fuel (n'-(n'-i)) (b1, (l1, H1)) (b2, (l2, H2))) vs1 vs2
                   end
          | Some (Clos v1 v2) =>
            exists v1' v2',
              get l2 H2 = Some (Clos v1' v2') /\
              forall i, (i < n)%nat ->
                   match n with
                     | 0%nat => True
                     | S n' =>
                       res_approx_fuel (n'-(n'-i)) (b1, (v1, H1)) (b2, (v1', H2)) /\
                       res_approx_fuel (n'-(n'-i)) (b1, (v2, H1)) (b2, (v2', H2))
                   end
          | Some (Env rho1) =>
            exists rho2, get l2 H2 = Some (Env rho2) /\
                    (forall x, (exists v1 v2, M.get x rho1 = Some v1 /\
                                    M.get x rho2 = Some v2 /\
                                    (forall i, (i < n)%nat ->
                                          match n with
                                            | 0%nat => True
                                            | S n' => res_approx_fuel (n'-(n'-i)) (b1, (v1, H1)) (b2, (v2, H2))
                                          end)) \/
                          (M.get x rho1 = None /\ M.get x rho2 = None))

          | None => True
        end
      | FunPtr B1 f1, FunPtr B2 f2 => f1 = f2 /\ B1 = B2
      | _, _ => False
    end.
  
  (** Result equivalence. Two results represent the exact same value *)
  Definition res_equiv (r1 : (loc -> loc) * res) (r2 : (loc -> loc) * res) : Prop :=
    forall n, res_approx_fuel n r1 r2 /\ res_approx_fuel n r2 r1.
  
  Notation "r1 ≈_( b1 , b2 ) r2 " := (res_equiv (b1, r1) (b2, r2)) (at level 70, no associativity).
  
  Definition ans_equiv (b1 : loc -> loc) (a1 : ans) (b2 : loc -> loc) (a2 : ans) :=
    match a1, a2 with
      | Res r1, Res r2 => r1 ≈_(b1, b2) r2
      | OOT, OOT => True
      | _, _  => False
    end.
  
  (** Approximation lifted to the environments *)
  Definition heap_env_approx (S : Ensemble var) p1 p2 : Prop :=
    let '(b1, (H1, rho1)) := p1 in
    let '(b2, (H2, rho2)) := p2 in
    forall x l, x \in S ->
           M.get x rho1 = Some l ->
           exists l', M.get x rho2 = Some l' /\
                 (l, H1) ≈_(b1, b2) (l', H2).
  
  (** Equivalence lifted to the environments *)
  Definition heap_env_equiv S p1 p2 : Prop :=
    heap_env_approx S p1 p2 /\
    heap_env_approx S p2 p1.
  
  Notation "S |- p1 ⩪_( b1 , b2 ) p2" := (heap_env_equiv S (b1, p1) (b2, p2))
                                           (at level 70, no associativity).
  
  Definition block_equiv (p1 : (loc -> loc) * heap block * block) (p2 : (loc -> loc) *  heap block * block)  :=
    let '(b1, H1, bl1) := p1 in
    let '(b2, H2, bl2) := p2 in
    match bl1, bl2 with
      | Constr c1 vs1, Constr c2 vs2 =>
        c1 = c2 /\ Forall2 (fun v1 v2 => (v1, H1) ≈_(b1, b2) (v2, H2)) vs1 vs2
      | Clos v1 v2, Clos v1' v2' =>
        (v1, H1) ≈_(b1, b2) (v1', H2) /\ (v2, H1) ≈_(b1, b2) (v2', H2)
      | Env rho1, Env rho2 => Full_set _ |- (H1, rho1) ⩪_(b1, b2) (H2, rho2)
      | _, _ => False
    end.
  
  Definition heap_equiv (S : Ensemble loc) p1 p2 : Prop :=
    let '(b1, H1) := p1 in
    let '(b2, H2) := p2 in
    forall l, l \in S -> (Loc (b2 l), H1)  ≈_( b1 , b2 ) (Loc (b1 l), H2).
      
  Notation  "S |- H1 ≃_( b1 , b2 ) H2" := (heap_equiv S (b1, H1) (b2, H2))
                                            (at level 70, no associativity).


  (** Equivalent definition, unfolding the recursion *)
  Definition res_approx_fuel' (n : nat) r1 r2 : Prop :=
    let '(b1, (v1, H1)) := r1 in
    let '(b2, (v2, H2)) := r2 in
    match v1, v2 with
      | Loc l1, Loc l2 =>
        b1 l1 = b2 l2 /\
        match get l1 H1 with
          | Some (Constr c vs1) =>
            exists vs2, 
              get l2 H2 = Some (Constr c vs2) /\
              forall i, (i < n)%nat ->
                   Forall2 (fun l1 l2 => res_approx_fuel i (b1, (l1, H1)) (b2, (l2, H2))) vs1 vs2
          | Some (Clos v1 v2) =>
            exists v1' v2',
              get l2 H2 = Some (Clos v1' v2') /\
              forall i, (i < n)%nat ->
                   res_approx_fuel i (b1, (v1, H1)) (b2, (v1', H2)) /\
                   res_approx_fuel i (b1, (v2, H1)) (b2, (v2', H2))
          | Some (Env rho1) =>
            exists rho2,
              get l2 H2 = Some (Env rho2) /\
              (forall x, (exists v1 v2, M.get x rho1 = Some v1 /\
                              M.get x rho2 = Some v2 /\
                              (forall i, (i < n)%nat ->
                                    res_approx_fuel i (b1, (v1, H1)) (b2, (v2, H2)))) \/
                    (M.get x rho1 = None /\ M.get x rho2 = None))
          | None => True
        end
      | FunPtr B1 f1, FunPtr B2 f2 => f1 = f2 /\ B1 = B2
      | _, _ => False
    end.
  
  (** Equivalence of the two definitions *)
  Lemma res_approx_fuel_eq n r1 r2 :
    res_approx_fuel n r1 r2 <-> res_approx_fuel' n r1 r2.
  Proof.
    destruct n; destruct r1 as [b1 [[l1 | B1 f1] H1]]; destruct r2 as [b2 [[l2 | B2 f2] H2]]; simpl.
    - destruct (get l1 H1) as [[c1 vs1 | v1 v2 | rho1]|]; [| | | now firstorder ].
      + split.
        * intros [Heq1 [vs [H _ ]]]. split; eauto. eexists. split; eauto.
          intros; omega.
        * intros [Heq1 [vs [H _ ]]]. split; eauto.
      + split.
        * intros [Heq1 [v1' [v2' [H _ ]]]]. split; eauto. eexists. eexists. split; eauto.
          intros; omega.
        * intros [Heq1 [v1' [v2' [H _ ]]]]. split; eauto.
      + split.
        * intros [Heq [vs [H Hb]]]. split; eauto. eexists. split; eauto.
          intros x. destruct (Hb x) as [Hb1 | Hb1]; eauto. 
          destruct Hb1 as [v1 [v2 [Hget1 [Hget2 Ht]]]].
          left. repeat eexists; eauto. intros; omega.
        * intros [Heq [vs [H Hb]]]. split; eauto. eexists. split; eauto.
          intros x. destruct (Hb x) as [Hb1 | Hb1]; eauto. 
          destruct Hb1 as [v1 [v2 [Hget1 [Hget2 Ht]]]].
          left. repeat eexists; eauto.
    - split; eauto.
    - split; eauto.   
    - now firstorder.
    - destruct (get l1 H1) as [[c1 vs1 | v1 v2 | rho1 ]|]; [| | | now firstorder ].
      + split.
        * intros [Heq1 [vs [H Hi]]]. split; eauto. eexists. split; eauto.
          intros i Hlt.
          assert (Heq : (i =  n - (n - i))%nat) by omega. rewrite Heq.
          eauto.
        * intros [Heq1 [vs [H Hin]]]. split; eauto. eexists. split; eauto.
          intros i Hlt.
          assert (Heq : (i =  n - (n - i))%nat) by omega. rewrite <- Heq.
          eauto.
      + split.
        * intros [Heq1 [v1' [v2' [H Hi]]]]. split; eauto.
          eexists. eexists. split; eauto.
          intros i Hlt.
          assert (Heq : (i =  n - (n - i))%nat) by omega. rewrite Heq.
          eauto.
        * intros [Ηeq1 [v1' [v2' [H Hin]]]]. split; eauto. eexists. eexists. split; eauto.
          intros i Hlt.
          assert (Heq : (i =  n - (n - i))%nat) by omega. rewrite <- Heq.
          eauto.
      + split.
        * intros [Heq1 [vs [H Hb ]]]. split; eauto. eexists. split; eauto.
          intros x. destruct (Hb x) as [Hb1 | Hb1]; eauto. 
          destruct Hb1 as [v1 [v2 [Hget1 [Hget2 Ht]]]].
          left. repeat eexists; eauto.
          intros i Hlt.
          assert (Heq : (i =  n - (n - i))%nat) by omega. rewrite Heq.
          eauto.
        * intros [Heq1 [vs [H Hb]]]. split; eauto. eexists. split; eauto.
          intros x. destruct (Hb x) as [Hb1 | Hb1]; eauto. 
          destruct Hb1 as [v1 [v2 [Hget1 [Hget2 Ht]]]].
          left. repeat eexists; eauto.
          intros i Hlt.
          assert (Heq : (i =  n - (n - i))%nat) by omega. rewrite <- Heq.
          eauto.
    - split; eauto.
    - split; eauto.   
    - now firstorder.
  Qed.

  Opaque res_approx_fuel.
  
 (** Equivalent definition for [res_equiv] *)
  Definition res_equiv' r1 r2 : Prop :=
    let '(b1, (v1, H1)) := r1 in
    let '(b2, (v2, H2)) := r2 in
    match v1, v2 with
      | Loc l1, Loc l2 =>
        b1 l1 = b2 l2 /\
        match get l1 H1, get l2 H2 with
          | Some bl1, Some bl2 => block_equiv (b1, H1, bl1) (b2, H2, bl2)
          | None, None => True
          | _, _ => False
        end
      | FunPtr B1 f1, FunPtr B2 f2 =>
        B1 = B2 /\ f1 = f2
      | _, _ => False
    end.
  
  Lemma res_equiv_eq r1 r2 :
    res_equiv r1 r2 <-> res_equiv' r1 r2.
  Proof.
    destruct r1 as [b1 [[l1 | B1 f1] H1]]; destruct r2 as [b2 [[l2 | B2 f2] H2]]; simpl.
    unfold res_equiv. split. 
    - intros H. assert (H0 := H 0%nat).
      rewrite !res_approx_fuel_eq in H0.
      destruct H0 as [Hal Har]. 
      simpl in *. destruct (get l1 H1) as [ v |] eqn:Hget1.
      + destruct v as [c1 vs1 | v1 v2 | rho1 ].
        * destruct Hal as [Heq1 [vs2 [Hget2 Hi]]].
          rewrite Hget2 in Har.
          destruct Har as [Heq2 [vs1' [Hget1' Hi']]]. inv Hget1'. 
          rewrite Hget2. split; eauto. split; eauto.
          eapply Forall2_forall. constructor. exact 0%nat.
          intros n. specialize (H (S n)). rewrite !res_approx_fuel_eq in H. 
          edestruct H as [Hal' Har']. simpl in Hal', Har'.
          rewrite Hget1 in Hal'. rewrite Hget2 in Har'. 
          destruct Hal' as [Heq1' [vs2' [Hget2' Hi2]]]. subst_exp.
          destruct Har' as [Heq2' [vs1 [Hget1' Hi1]]]. subst_exp.
          eapply Forall2_conj.
          eapply Hi2. omega.
          eapply Forall2_flip. eapply Hi1. omega.
        * destruct Hal as [Heq1 [v1' [v2' [Hget2 Hi]]]].
          rewrite Hget2 in Har.
          destruct Har as [Heq2 [v1'' [v2'' [Hget1' Hi']]]]. inv Hget1'. 
          rewrite Hget2.
          split; eauto. split.

          intros n. specialize (H (S n)). rewrite !res_approx_fuel_eq in H.
          edestruct H as [Hal' Har']. simpl in Hal', Har'.
          rewrite Hget1 in Hal'. rewrite Hget2 in Har'. 
          destruct Hal' as [Heq1' [v3 [v4 [Hget2' Hi2]]]]. subst_exp.
          destruct Har' as [Heq2' [v3' [v4' [Hget1' Hi1]]]]. repeat subst_exp.
          split. eapply Hi2. omega. eapply Hi1. omega.
          
          intros n. specialize (H (S n)). rewrite !res_approx_fuel_eq in H.
          edestruct H as [Hal' Har']. simpl in Hal', Har'.
          rewrite Hget1 in Hal'. rewrite Hget2 in Har'. 
          destruct Hal' as [Heq1' [v3 [v4 [Hget2' Hi2]]]]. subst_exp.
          destruct Har' as [Heq2' [v3' [v4' [Hget1' Hi1]]]]. repeat subst_exp.
          split. eapply Hi2. omega. eapply Hi1. omega.

        * destruct Hal as [Heq1 [rho2 [Hget2 Hi1]]].
          rewrite Hget2 in Har.
          destruct Har as [Heq2 [rho1' [Hget1' Hi2]]]. inv Hget1'. 
          rewrite Hget2. split; eauto. split; eauto; intros x l _ Hget.
          { destruct (Hi1 x) as [[v1 [v2 [Hgetv1 [Hgetv2 Hi]]]] | [Hn1 Hn2]]; try congruence.
            subst_exp. eexists; split; eauto.
            intros n.
            specialize (H (S n)). rewrite !res_approx_fuel_eq in H. 
            edestruct H as [Hal' Har']. simpl in Hal', Har'.
            rewrite Hget1 in Hal'. rewrite Hget2 in Har'. 
            destruct Hal' as [Heq1' [rho2' [Hget2' Hin2]]]. subst_exp.
            destruct Har' as [Heq2' [rho1 [Hget1' Hin1]]]. repeat subst_exp.
            destruct (Hin1 x) as [[v1' [v2' [Hgetv1' [Hgetv2' Hi1']]]] | [Hn1 Hn2]]; try congruence.
            repeat subst_exp.
            destruct (Hin2 x) as [[v1'' [v2'' [Hgetv1' [Hgetv2' Hi2']]]] | [Hn1 Hn2]]; try congruence.
            repeat subst_exp. split; eauto. }
          { destruct (Hi1 x) as [[v1 [v2 [Hgetv1 [Hgetv2 Hi]]]] | [Hn1 Hn2]]; try congruence.
            subst_exp. eexists; split; eauto.
            intros n.
            specialize (H (S n)). rewrite !res_approx_fuel_eq in H. 
            edestruct H as [Hal' Har']. simpl in Hal', Har'.
            rewrite Hget1 in Hal'. rewrite Hget2 in Har'.
            destruct Hal' as [Heq1' [rho2' [Hget2' Hin2]]]. subst_exp.
            destruct Har' as [Heq2' [rho1 [Hget1' Hin1]]]. repeat subst_exp.
            destruct (Hin1 x) as [[v1' [v2' [Hgetv1' [Hgetv2' Hi1']]]] | [Hn1 Hn2]]; try congruence.
            repeat subst_exp.
            destruct (Hin2 x) as [[v1'' [v2'' [Hgetv1' [Hgetv2' Hi2']]]] | [Hn1 Hn2]]; try congruence.          
            repeat subst_exp. split; eauto. }
      + destruct (get l2 H2); eauto. 
        destruct b.
        destruct Har as [Heq1 [vs2 [Heq _]]]; discriminate.
        destruct Har as [Heq2 [v1' [v2' [Heq _]]]]; discriminate.
        destruct Har as [Heq2 [vs2 [Heq _]]]; discriminate.
    - destruct (get l1 H1) eqn:Hget1.
      + destruct b as [ c vs1 | v1 v2 | rho1 B1 off1 ].
        * destruct (get l2 H2) eqn:Hget2; try now firstorder.
          destruct b as [c' vs2 | |]; try now firstorder.
          intros [Heq1 [Heq Hall]] n. subst. rewrite !res_approx_fuel_eq.
          simpl. rewrite Hget1, Hget2. split.
          
          split; eauto. eexists. split. reflexivity.
          intros. eapply Forall2_monotonic; [| eassumption ].
          now intros v1 v2 [Hl Hr]; eauto.

          split; eauto.
          eexists. split. reflexivity.
          intros. eapply Forall2_flip. eapply Forall2_monotonic; [| eassumption ].
          now intros v1 v2 [Hl Hr]; eauto.

        * destruct (get l2 H2) eqn:Hget2; try now firstorder.
          destruct b as [ | v1' v2' |]; try now firstorder.
          intros [Heq1 [H1' H2']] n. rewrite !res_approx_fuel_eq.
          simpl. rewrite Hget1, Hget2. split.

          split; eauto.
          eexists. eexists. split. reflexivity.
          intros. split; eauto. eapply H1'. eapply H2'.

          split; eauto.
          eexists. eexists. split. reflexivity.
          intros. split; eauto. eapply H1'. eapply H2'.

        * destruct (get l2 H2) eqn:Hget2; try now firstorder.
          destruct b as [ | | rho2]; try now firstorder.
          intros [Heq' [Hl Hr]] n. rewrite !res_approx_fuel_eq.
          simpl. rewrite Hget1, Hget2. split.
          
          split; eauto.
          eexists. split. reflexivity.
          intros x.
          destruct (M.get x rho1) as [v1|] eqn:Hgetv1.
          edestruct Hl as [v2 [Hgetv2 Hi]]; try eassumption.
          now constructor.
          left; repeat eexists; eauto. intros. now eapply Hi.
          destruct (M.get x rho2) as [v2|] eqn:Hgetv2; eauto.
          edestruct Hr as [v1 [Hgetv1' Hi']]; try eassumption.
          now constructor. congruence.
          
          split; eauto. eexists. split. reflexivity.
          intros x.
          destruct (M.get x rho1) as [v1|] eqn:Hgetv1.
          edestruct Hl as [v2 [Hgetv2 Hi]]; try eassumption.
          now constructor.
          left; repeat eexists; eauto. intros. now eapply Hi.
          destruct (M.get x rho2) as [v2|] eqn:Hgetv2; eauto.
          edestruct Hr as [v1 [Hgetv1' Hi']]; try eassumption.
          now constructor. congruence.
      + destruct (get l2 H2) eqn:Hget2; try now firstorder.
        intros. rewrite !res_approx_fuel_eq. simpl.
        rewrite Hget1, Hget2; eauto. firstorder.
    - split; try contradiction.
      intros Heq. destruct (Heq 0%nat) as [Hl Hr].
      rewrite res_approx_fuel_eq in *. contradiction.
    - split; try contradiction.
      intros Heq. destruct (Heq 0%nat) as [Hl Hr].
      rewrite res_approx_fuel_eq in *. contradiction.
    - split.
      + intros Heq. destruct (Heq 0%nat) as [Hl Hr].
        rewrite res_approx_fuel_eq in *. inv Hl. split; eauto.
      + intros [Hl1 Hr2]; subst.
        split; eauto; rewrite res_approx_fuel_eq; simpl; split; eauto.  
  Qed.

  Lemma res_equiv_locs_eq (S : Ensemble var) (b1 b2 : loc -> loc) (H1 H2 : heap block)
        (l1 l2 : loc):
    (Loc l1, H1) ≈_( b1, b2) (Loc l2, H2) ->
    b1 l1 = b2 l2. 
  Proof.
    intros Heq. rewrite res_equiv_eq in Heq.
    destruct Heq as [Heq _]. eassumption.
  Qed. 



  (** * Lemmas about [res_approx] and [res_equiv] *)

  (** Preorder and equivalence properties of [res_approx] and [res_equiv] *)

  (* 
  Lemma heap_equiv_res_approx (S : Ensemble loc) (β1 β2 : loc -> loc)
        (H1 H2 : heap block)
        (v : value) (n : nat) :
    S |- H1 ≃_(β1, β2) H2  ->
    (val_loc v) \subset S -> 
    res_approx_fuel n (β1, (v, H1)) (β2, (v, H2)).
  Proof.
    intros [Heq1 Heq2] Hin.
    destruct v as [l | B f]; rewrite res_approx_fuel_eq; [| now split; eauto ].
    edestruct Heq1 as [Hbeq Heq1'].
    eapply Hin. reflexivity.
    simpl; destruct (get l H1) eqn:Hget; eauto.
    edestruct Heq1' as [bl2 [Hget2 Heq]]. reflexivity.
    destruct b; destruct bl2; try contradiction.
    - destruct Heq as [Heq Hin2]; subst. split; eauto. eexists; split; eauto. 
      intros. 
      eapply Forall2_monotonic; eauto. simpl.
      intros ? ? [Ha1 Ha2]; eauto.
    - destruct Heq as [Hv1 Hv2]. split; eauto. eexists. eexists.
      split; eauto. intros; split; eauto.
      now eapply Hv1. now eapply Hv2.
    - split; eauto. eexists; split; eauto.
      intros x. destruct Heq as [Hal Har].
      destruct (M.get x e) eqn:Hgetx1; destruct (M.get x e0) eqn:Hgetx2;
      simpl in *; eauto.
      + left. repeat eexists; eauto.
        edestruct Hal as [l' [Hgetx2' Ha]]; eauto.
        now constructor. subst_exp. intros i Hleq; destruct (Ha i); eassumption.
      + edestruct Hal as [l' [Hgetx2' Ha]]; eauto.
        now constructor. congruence.
      + edestruct Har as [l' [Hgetx2' Ha]]; eauto.
        now constructor. congruence.
  Qed.
   *)

  Lemma Preorder_res_approx_fuel i :
    preorder ((loc -> loc) * res) (res_approx_fuel i).
  Proof.
    constructor.
    - induction i as [i IHi] using lt_wf_rec.
      intros [β [v H1]]. rewrite res_approx_fuel_eq. destruct v.
      simpl. destruct (get l H1) eqn:Hgetl; eauto. 
      destruct b as [c vs | vq vw | rho B f]. 
      + split; eauto. eexists; split; eauto.
        intros i' Hlt.
        eapply Forall2_refl; intros l'. eapply IHi in Hlt.
        specialize (Hlt (β, (l', H1))). eassumption.
      + split; eauto. eexists; eexists; split; eauto.
        intros i' Hlt. 
        split. specialize (IHi i' Hlt (β, (vq, H1))). eapply IHi; eauto.
        specialize (IHi i' Hlt (β, (vw, H1))). eapply IHi; eauto.
      + split; eauto. eexists; split; eauto.
        intros x.
        destruct (M.get x rho) eqn:heq; eauto.
        * left. do 2 eexists; repeat split; eauto.
          intros.
          specialize (IHi i0 H (β, (v, H1))). eapply IHi; eauto.
      + split; eauto.
    - induction i as [i IHi]  using lt_wf_rec1.
      intros [β1 [v1 H1]] [β2 [v2 H2]] [β3 [v3 H3]] Hap1 Hap2. rewrite res_approx_fuel_eq in *.
      simpl in *.
      destruct v1 as [l1 | B1 f1]; destruct v2 as [l2 | B2 f2]; destruct v3 as [l3 | B3 f3];
      try contradiction.
      { destruct (get l1 H1) eqn:Hget1; eauto.
        destruct b as [c vs1 | vq  vw | rho1 B f].
        + edestruct Hap1 as [Heq1 [vs2 [Hget2 Hall2]]]. rewrite Hget2 in Hap2.
          destruct Hap2 as [Heq2 [vs3 [Hget3 Hall3]]].
          split; eauto. congruence. eexists; split; eauto.
          intros i' Hlt.
          eapply Forall2_trans_strong; eauto. intros v1 v2 v3 Hv1 Hv2.
          specialize (IHi i' Hlt (β1, (v1, H1)) (β2, (v2, H2)) (β3, (v3, H3))).
          eapply IHi; eauto.
        + edestruct Hap1 as [Heq1 [vq' [vw' [Hget Hall2]]]]. rewrite Hget in Hap2.
          destruct Hap2 as [Heq2 [vq'' [vw'' [Hget' Hall3]]]].
          split. congruence. eexists; eexists; split; eauto.
          intros i' Hlt.
          split; eauto.
          specialize (IHi i' Hlt (β1, (vq, H1)) (β2, (vq', H2)) (β3, (vq'', H3))).
          eapply IHi; eauto. now eapply Hall2; eauto.
          now eapply Hall3; eauto.
          specialize (IHi i' Hlt (β1, (vw, H1)) (β2, (vw', H2)) (β3, (vw'', H3))).
          eapply IHi; eauto. now eapply Hall2; eauto.
          now eapply Hall3; eauto.
        + edestruct Hap1 as [Heq1 [rho2 [Hget2 Hall2]]]. rewrite Hget2 in Hap2.
          destruct Hap2 as [Heq2 [rho33 [Hget3 Hall3]]].
          split. congruence. eexists; split; eauto.
          intros x.
          edestruct Hall2 with (x := x) as [[l1' [l2' [Hgetl1 [Hgetl2 Hi]]]] | [Hn1 Hn2]]; eauto.
          * edestruct Hall3 with (x := x) as [[l2'' [l3' [Hgetl2' [Hgetl3 Hi']]]] | [Hn1 Hn2]]; eauto.
            subst_exp. subst_exp.
            left; repeat eexists; eauto. subst_exp.
            intros.
            specialize (IHi i0 H (β1, (l1', H1)) (β2, (l2'', H2)) (β3, (l3', H3))).
            eapply IHi; eauto.
            congruence.
          * edestruct Hall3 as [[l2'' [l3' [Hgetl2' [Hgetl3 Hi']]]] | [Hn2' Hn3]]; eauto.
            congruence.
        + destruct Hap1; destruct Hap2. split; eauto. congruence. }
      { inv Hap1; inv Hap2. split; eauto. }
  Qed.

  Instance Equivalence_res_equiv : Equivalence res_equiv.
  Proof.
    constructor. 
    - intros res; split; eapply Preorder_res_approx_fuel.
    - intros res res' H n. destruct (H n) as [H1 H2]. split; eauto.
    - intros res1 res2 res3 H1 H2. intros n.
      destruct (H1 n) as [Ht1 Ht2]; destruct (H2 n) as [Ht3 Ht4];
      split.
      now eapply Preorder_res_approx_fuel; eauto.
      now eapply Preorder_res_approx_fuel; eauto.
  Qed.
  
  Instance Equivalence_heap_env_equiv S : Equivalence (heap_env_equiv S).
  Proof.
    constructor.
    - intros [b [H rho]]; split; intros l Hget; eexists; split; eauto; reflexivity.
    - intros [b [H rho]] [b' [H' rho']] H1; split; intros v l Hin Hget;
      eapply H1; eauto.
    - edestruct Equivalence_res_equiv; eauto.
      intros [b [H rho]] [b' [H' rho']] [b'' [H'' rho'']] H1 H2; split; intros v l Hin Hget.
      edestruct H1 as [H1' _]; eauto. edestruct H1' as [v1 [Hget1 Hres1]]; eauto.
      edestruct H2 as [H2' _]; eauto. edestruct H2' as [v2 [Hget2 Hres2]]; eauto.
      edestruct H2 as [_ H2']; eauto. edestruct H2' as [v2 [Hget2 Hres2]]; eauto.
      edestruct H1 as [_ H1']; eauto. edestruct H1' as [v1 [Hget1 Hres1]]; eauto.
  Qed.

  (** * Lemmas about [block_equiv] **)
  
  Instance Reflexive_block_equiv : Reflexive block_equiv.
  Proof.
    intros [[i H] b]. destruct b; simpl; eauto; try reflexivity.
    split; eauto. eapply Forall2_refl; now eauto with typeclass_instances.
    split; reflexivity.
  Qed.
  
  Instance Transitive_block_equiv : Transitive block_equiv.
  Proof.
    intros [[i1 H1] b1] [[i2 H2] b2] [[i3 H3] b3] Hb1 Hb2.
    destruct b1; destruct b2; try contradiction;
    destruct b3; try contradiction.
    - destruct Hb1 as [Heq1 Hb1].
      destruct Hb2 as [Heq2 Hb2].
      subst. split; eauto. 
      eapply Forall2_trans_strong; try eassumption.
      simpl; intros. eapply Equivalence_Transitive; eauto. 
    - destruct Hb1 as [Heq1 Hb1].
      destruct Hb2 as [Heq2 Hb2].
      split; eapply Equivalence_Transitive; eauto.
    - simpl in *.
      eapply Equivalence_Transitive; eauto.
  Qed.
  
  Instance Symmetric_block_equiv : Symmetric block_equiv.
  Proof.
    intros [[i1 H1] b1] [[i2 H2] b2] Hb.
    destruct b1; destruct b2; try contradiction.
    - destruct Hb as [Heq1 Hb1].
      subst. split; eauto. 
      eapply Forall2_symm_strong; try eassumption.
      simpl; intros. symmetry. eauto.
    - destruct Hb as [Heq1 Heq2].
      split; symmetry; eauto.
    - simpl in *. symmetry; eauto.
  Qed.

  (* 
  Instance Equivalence_heap_equiv S : Equivalence (heap_equiv S). 
  Proof.
    constructor.
    - intros [b H].
      split; intros x Hin; split; try reflexivity; intros bl Hget;
      eexists; split; eauto; reflexivity.
    - intros [b1 H1] [b2 H2] [Hs1 Hs2]. 
      split; intros x Hin.
      edestruct Hs1 as [Hbeq1 Hh1]; eauto.
      edestruct Hs2 as [Hbeq2 Hh2]; eauto.
    - intros [b1 H1] [b2 H2] [b3 H3] [Hs1 Hs2] [Hs2' Hs3].
      split; intros x Hin.
      edestruct Hs1 as [Hbeq1 Hh1]; eauto.
      edestruct Hs2' as [Hbeq2 Hh2]; eauto.
      split. congruence. intros bl Hget. 
      edestruct (Hh1 bl Hget) as [bl2 [Hget2 Hh2']]. 
      edestruct (Hh2 bl2 Hget2) as [bl3 [Hget3 Hh3']]. 
      eexists; split; eauto.
      now eapply Transitive_block_equiv; eauto.
      edestruct Hs2 as [Hbeq1 Hh1]; eauto.
      edestruct Hs3 as [Hbeq2 Hh2]; eauto.
      split. congruence. intros bl Hget. 
      edestruct (Hh2 bl Hget) as [bl2 [Hget2 Hh2']]. 
      edestruct (Hh1 bl2 Hget2) as [bl3 [Hget3 Hh3']]. 
      eexists; split; eauto.
      now eapply Transitive_block_equiv; eauto.
  Qed.


  Lemma heap_env_approx_heap_equiv (S : Ensemble var) (H1 H2 : heap block) (b1 b2 : loc -> loc) (rho : env) :
    (env_locs rho S) |- H1 ≃_(b1, b2) H2 -> 
    heap_env_approx S (b2, (H2, rho)) (b1, (H1, rho)).
  Proof.
    intros [Heq1 Heq2] x v Hin Hget.
    eexists; split; eauto.  
    rewrite res_equiv_eq. simpl.
    destruct v as [l | B f]; [| now split; eauto ].
    destruct (get l H1) eqn:Heq.
    - edestruct Heq1 as [Hb2 Heq1'].
      eexists; split; eauto. rewrite Hget. reflexivity.
      split; eauto. edestruct Heq1' as [bl2 [Hget2 Hbl2]]; eauto. rewrite Hget2.
      simpl in Hbl2. destruct b; destruct bl2; try contradiction.
      destruct Hbl2 as [Heqc Hall]; subst; split; eauto.
      eapply Forall2_symm_strong; [| eassumption ].
      simpl; intros.
      now eapply Equivalence.equiv_symmetric; eauto.
      destruct Hbl2 as [Hb'1 Hb'2].
      split; eauto; now symmetry; eauto.
      now symmetry; eauto.
    - edestruct Heq2 as [Hb2 Heq1'].
      eexists; split; eauto. rewrite Hget. reflexivity.
      split; eauto.
      destruct (get l H2) eqn:HgetH2; eauto.
      edestruct Heq1' as [bl2 [Hget2 Hbl2]]; eauto.
      congruence.
  Qed.   
  
  Corollary heap_env_equiv_heap_equiv (S : Ensemble var) (H1 H2 : heap block) (b1 b2 : loc -> loc)
            (rho : env) :
    (env_locs rho S) |- H1 ≃_(b1, b2) H2 -> 
    S |- (H1, rho) ⩪_(b1, b2) (H2, rho).
  Proof.
    intros. split; eapply heap_env_approx_heap_equiv; simpl; try eassumption.
    symmetry. eassumption.
  Qed.

  Lemma heap_equiv_res_equiv (S : Ensemble loc) (H1 H2 : heap block) (b1 b2 : loc -> loc)
        (v : value) :
    S |- H1 ≃_(b1, b2) H2  ->
    (val_loc v) \subset S -> 
    (v, H1) ≈_(b1, b2) (v, H2).
  Proof.
    intros Heq Hin m.
    split. eapply heap_equiv_res_approx; eauto. 
    eapply heap_equiv_res_approx; eauto. symmetry.
    eassumption. 
  Qed.

   *)
  Lemma heap_env_approx_empty S H1 H2 rho2 b1 b2 :
    heap_env_approx S (b1, (H1, M.empty _)) (b2, (H2, rho2)).
  Proof. 
    intros x Hin v Hget. 
    rewrite M.gempty in Hget. congruence. 
  Qed.

  Lemma heap_env_equiv_empty S H1 H2 b1 b2 :
    S |- (H1, M.empty _) ⩪_(b1, b2) (H2, M.empty _).
  Proof. 
    split; eapply heap_env_approx_empty.
  Qed.

  (** Heap equivalences respect functional extensionality *)

  Instance Proper_res_approx_f_eq_l : Proper (eq ==> RelProd f_eq eq ==> eq ==> iff) res_approx_fuel.
  Proof.
    intros j i Heq1 [b1 [r1 H1]] [b1' [r1' H1']] [Heq2 Heq3] [b2 [r2 H2]] [b2' [r2' H2']] Heq4.
    inv Heq3; inv Heq4. split.
    - revert b1 b1' r1' H1' b2' r2' H2' Heq2.
      induction i as [i IHi] using lt_wf_rec; intros b1 b1' r1 H1 b2 r2 H2 Heq2.
      rewrite !res_approx_fuel_eq in *.
      destruct r1 as [ l1 | B1 f1]; destruct r2 as [ l2 | V2 f2]; try contradiction. 
      + simpl. destruct (get l1 H1) as [b | ] eqn:Hgetl1; eauto. 
        destruct b as [c vs | vq vw | rho ].
        * intros [Heqb [vs2 [Hgetl2 Hi]]]. split.
          rewrite <- Heq2. eassumption.
          repeat eexists; eauto.
          intros i' Hlt.
          eapply Forall2_monotonic; [| eapply Hi; eassumption ].
          intros. eapply IHi; eassumption.
        * intros [Heqb [v1 [v2 [Hgetl2 Hi]]]]. split.
          rewrite <- Heq2. eassumption.
          repeat eexists; eauto.

          eapply IHi; try eassumption. eapply Hi. eassumption.

          eapply IHi; try eassumption. eapply Hi. eassumption.
        * intros [Heqb [rho2 [Hgetl2 Hall]]]. split.
          rewrite <- Heq2. eassumption.
          eexists; split; eauto. intros x. destruct (Hall x) as [[v1 [v2 [Hget1 [Hget2 Hs]]]] | Hn]; eauto.
          left. repeat eexists; eauto.
        * intros [Heq _]; split; eauto. rewrite <- Heq2. eauto.
      + simpl; eauto.
    - revert b1 b1' r1' H1' b2' r2' H2' Heq2.
      induction i as [i IHi] using lt_wf_rec; intros b1 b1' r1 H1 b2 r2 H2 Heq2.
      rewrite !res_approx_fuel_eq in *.
      destruct r1 as [ l1 | B1 f1]; destruct r2 as [ l2 | V2 f2]; try contradiction. 
      + simpl. destruct (get l1 H1) as [b | ] eqn:Hgetl1; eauto. 
        destruct b as [c vs | vq vw | rho ].
        * intros [Heqb [vs2 [Hgetl2 Hi]]]. split.
          rewrite Heq2. eassumption.
          repeat eexists; eauto.
          intros i' Hlt.
          eapply Forall2_monotonic; [| eapply Hi; eassumption ].
          intros. eapply IHi; eassumption.
        * intros [Heqb [v1 [v2 [Hgetl2 Hi]]]]. split.
          rewrite Heq2. eassumption.
          repeat eexists; eauto.

          eapply IHi; try eassumption. eapply Hi. eassumption.

          eapply IHi; try eassumption. eapply Hi. eassumption.
        * intros [Heqb [rho2 [Hgetl2 Hall]]]. split.
          rewrite Heq2. eassumption.
          eexists; split; eauto. intros x. destruct (Hall x) as [[v1 [v2 [Hget1 [Hget2 Hs]]]] | Hn]; eauto.
          left. repeat eexists; eauto.
        * intros [Heq _]; split; eauto. rewrite Heq2. eauto.
      + simpl; eauto.
  Qed.
  
  Instance Proper_res_approx_f_eq_r : Proper (eq ==> eq ==> RelProd f_eq eq ==> iff) res_approx_fuel.
  Proof.
    intros j i Heq1 [b1 [r1 H1]] [b1' [r1' H1']] Heq2 [b2 [r2 H2]] [b2' [r2' H2']] [Heq3 Heq4].
    inv Heq2; inv Heq4. split.
    - revert b1' r1' H1' b2 b2' r2' H2' Heq3.
      induction i as [i IHi] using lt_wf_rec; intros b1 r1 H1 b2 b2' r2 H2 Heq2.
      rewrite !res_approx_fuel_eq in *.
      destruct r1 as [ l1 | B1 f1]; destruct r2 as [ l2 | V2 f2]; try contradiction. 
      + simpl. destruct (get l1 H1) as [b | ] eqn:Hgetl1; eauto. 
        destruct b as [c vs | vq vw | rho ].
        * intros [Heqb [vs2 [Hgetl2 Hi]]]. split.
          rewrite <- Heq2. eassumption.
          repeat eexists; eauto.
          intros i' Hlt.
          eapply Forall2_monotonic; [| eapply Hi; eassumption ].
          intros. eapply IHi; eassumption.
        * intros [Heqb [v1 [v2 [Hgetl2 Hi]]]]. split.
          rewrite <- Heq2. eassumption.
          repeat eexists; eauto.

          eapply IHi; try eassumption. eapply Hi. eassumption.

          eapply IHi; try eassumption. eapply Hi. eassumption.
        * intros [Heqb [rho2 [Hgetl2 Hall]]]. split.
          rewrite <- Heq2. eassumption.
          eexists; split; eauto. intros x. destruct (Hall x) as [[v1 [v2 [Hget1 [Hget2 Hs]]]] | Hn]; eauto.
          left. repeat eexists; eauto.
        * intros [Heq _]; split; eauto. rewrite <- Heq2. eauto.      
      + simpl; eauto.
    - revert b1' r1' H1' b2 b2' r2' H2' Heq3.
      induction i as [i IHi] using lt_wf_rec; intros b1 r1 H1 b2 b2' r2 H2 Heq2.
      rewrite !res_approx_fuel_eq in *.
      destruct r1 as [ l1 | B1 f1]; destruct r2 as [ l2 | V2 f2]; try contradiction. 
      + simpl. destruct (get l1 H1) as [b | ] eqn:Hgetl1; eauto. 
        destruct b as [c vs | vq vw | rho ].
        * intros [Heqb [vs2 [Hgetl2 Hi]]]. split.
          rewrite Heq2. eassumption.
          repeat eexists; eauto.
          intros i' Hlt.
          eapply Forall2_monotonic; [| eapply Hi; eassumption ].
          intros. eapply IHi; eassumption.
        * intros [Heqb [v1 [v2 [Hgetl2 Hi]]]]. split.
          rewrite Heq2. eassumption.
          repeat eexists; eauto.

          eapply IHi; try eassumption. eapply Hi. eassumption.

          eapply IHi; try eassumption. eapply Hi. eassumption.
        * intros [Heqb [rho2 [Hgetl2 Hall]]]. split.
          rewrite Heq2. eassumption.
          eexists; split; eauto. intros x. destruct (Hall x) as [[v1 [v2 [Hget1 [Hget2 Hs]]]] | Hn]; eauto.
          left. repeat eexists; eauto.
        * intros [Heq _]; split; eauto. rewrite Heq2. eauto.
      + simpl; eauto.
  Qed.

  Instance Proper_res_equiv_f_eq_l : Proper (RelProd f_eq eq ==> eq ==> iff) res_equiv.
  Proof.
    intros [b1 [r1 H1]] [b1' [r1' H1']] Heq1 [b2 [r2 H2]] [b2' [r2' H2']] Heq2. inv Heq2.
    split; intros H n; specialize (H n).
    rewrite <- !Heq1. eassumption.
    rewrite !Heq1. eassumption.
  Qed.

  Instance Proper_res_equiv_f_eq_r : Proper (eq ==> RelProd f_eq eq ==> iff) res_equiv.
  Proof.
    intros [b1 [r1 H1]] [b1' [r1' H1']] Heq1 [b2 [r2 H2]] [b2' [r2' H2']] Heq2. inv Heq1.
    split; intros H n; specialize (H n).
    rewrite <- !Heq2. eassumption.
    rewrite !Heq2. eassumption.
  Qed.
  
  Instance Proper_heap_env_approx_f_eq_l : Proper (eq ==> RelProd f_eq eq ==> eq ==> iff) heap_env_approx.
  Proof. 
    intros s1 s2 hseq [b1 [H1 rho1]] [b2 [H2 rho2]] [Heq1 Heq2] [b1' [H1' p1']] [b2' [H2' p2']] Heq'.
    inv Heq2; inv Heq'. 
    subst; split; intros Ha x v Hin Hget; edestruct Ha as [v' [Hget' Hres]]; eauto; eexists; split; eauto.
    assert (Heq : (f_eq * eq)%signature (b1, (v, H2)) (b2, (v, H2))) by (split; eauto).
    rewrite Heq in Hres. eassumption.
    assert (Heq : (f_eq * eq)%signature (b1, (v, H2)) (b2, (v, H2))) by (split; eauto).
    rewrite Heq. eassumption.
  Qed.

  Instance Proper_heap_env_approx_f_eq_r : Proper (eq ==> eq ==> RelProd f_eq eq ==> iff) heap_env_approx.
  Proof. 
    intros s1 s2 hseq [b1 [H1 rho1]] [b2 [H2 rho2]] Heq [b1' [H1' p1']] [b2' [H2' p2']] [Heq1 Heq2].
    inv Heq2; inv Heq. 
    subst; split; intros Ha x v Hin Hget; edestruct Ha as [v' [Hget' Hres]]; eauto; eexists; split; eauto.
    assert (Heq : (f_eq * eq)%signature (b1', (v', H2')) (b2', (v', H2'))) by (split; eauto).
    rewrite <- Heq. eassumption.
    assert (Heq : (f_eq * eq)%signature (b1', (v', H2')) (b2', (v', H2'))) by (split; eauto).
    rewrite Heq. eassumption.
  Qed.
  
  Instance Proper_heap_env_equiv_f_eq_l : Proper (eq ==> RelProd f_eq eq ==> eq ==> iff) heap_env_equiv.
  Proof. 
    intros s1 s2 hseq [b1 [H1 rho1]] [b2 [H2 rho2]] [Heq1 Heq2] [b1' [H1' p1']] [b2' [H2' p2']] Heq'.
    inv Heq2; inv Heq'.
    assert (Heq : (f_eq * eq)%signature (b1, (H2, rho2)) (b2, (H2, rho2))) by (split; eauto).
    split; intros [Hh1 Hh2]. split; rewrite <- Heq; eassumption.
    split; rewrite Heq; eassumption.
  Qed.
  
  Instance Proper_heap_env_equiv_f_eq_r : Proper (eq ==> eq ==> RelProd f_eq eq ==> iff) heap_env_equiv.
  Proof. 
    intros s1 s2 hseq [b1 [H1 rho1]] [b2 [H2 rho2]] Heq' [b1' [H1' p1']] [b2' [H2' p2']] [Heq1 Heq2].
    inv Heq2; inv Heq'.
    assert (Heq : (f_eq * eq)%signature (b1', (H2', p2')) (b2', (H2', p2'))) by (split; eauto).
    split; intros [Hh1 Hh2]. split; rewrite <- Heq; eassumption.
    split; rewrite Heq; eassumption.
  Qed.

  Instance Proper_block_equiv_f_eq_l : Proper (RelProd (RelProd f_eq eq) eq ==> eq ==> iff) block_equiv.
  Proof. 
    intros [[b1 H1] bl1] [[b2 H2] bl2] [[Heq1 Heq2] Heq3] [[b1' H1'] bl1'] [[b2' H2'] bl2'] Heq';
    inv Heq'; inv Heq2; inv Heq3; simpl in *; subst.
    destruct bl2 as [c vs | vq vw | rho ]; destruct bl2' as [c' vs' | vq' vw' | rho' ];
    [| now firstorder | now firstorder | now firstorder | | now firstorder | now firstorder | now firstorder | ].
    - split; intros [Heq1' Hres].
      split; eauto.
      eapply Forall2_monotonic; try eassumption. intros v1 v2 Hres'.
      assert (Heq : (f_eq * eq)%signature (b1, (v1, H2)) (b2, (v1, H2))) by (split; eauto).
      rewrite <- Heq. eassumption.
      split; eauto.
      eapply Forall2_monotonic; try eassumption. intros v1 v2 Hres'.
      assert (Heq : (f_eq * eq)%signature (b1, (v1, H2)) (b2, (v1, H2))) by (split; eauto).
      rewrite Heq. eassumption.
    - assert (Heq : (f_eq * eq)%signature (b1, (vq, H2)) (b2, (vq, H2))) by (split; eauto).
      rewrite Heq. 
      assert (Heq' : (f_eq * eq)%signature (b1, (vw, H2)) (b2, (vw, H2))) by (split; eauto).
      rewrite Heq'. reflexivity.
    - assert (Heq : (f_eq * eq)%signature (b1, (H2, rho)) (b2, (H2, rho))) by (split; eauto).
      rewrite Heq. reflexivity.
  Qed.

  Instance Proper_block_equiv_f_eq_r : Proper (eq ==> RelProd (RelProd f_eq eq) eq ==> iff) block_equiv.
  Proof. 
    intros [[b1 H1] bl1] [[b2 H2] bl2] Heq' [[b1' H1'] bl1'] [[b2' H2'] bl2'] [[Heq1 Heq2] Heq3];
    inv Heq'; inv Heq2; inv Heq3; simpl in *; subst.
    destruct bl2 as [c vs | vq vw | rho ]; destruct bl2' as [c' vs' | vq' vw' | rho' ];
    [| now firstorder | now firstorder | now firstorder | | now firstorder | now firstorder | now firstorder | ].
    - split; intros [Heq1' Hres].
      split; eauto.
      eapply Forall2_monotonic; try eassumption. intros v1 v2 Hres'.
      assert (Heq : (f_eq * eq)%signature (b1', (v2, H2')) (b2', (v2, H2'))) by (split; eauto).
      rewrite <- Heq. eassumption.
      split; eauto.
      eapply Forall2_monotonic; try eassumption. intros v1 v2 Hres'.
      assert (Heq : (f_eq * eq)%signature (b1', (v2, H2')) (b2', (v2, H2'))) by (split; eauto).
      rewrite Heq. eassumption.
    - assert (Heq : (f_eq * eq)%signature (b1', (vq', H2')) (b2', (vq', H2'))) by (split; eauto).
      rewrite Heq. 
      assert (Heq' : (f_eq * eq)%signature (b1', (vw', H2')) (b2', (vw', H2'))) by (split; eauto).
      rewrite Heq'. reflexivity.
    - assert (Heq : (f_eq * eq)%signature (b1', (H2', rho')) (b2', (H2', rho'))) by (split; eauto).
      rewrite Heq. reflexivity.
  Qed.
  
  (* Instance Proper_heap_approx_f_eq_l : Proper (eq ==> RelProd f_eq eq ==> eq ==> iff) heap_approx. *)
  (* Proof.  *)
  (*   intros s1 s2 hseq [b1 H1] [b2 H2] [Heq1 Heq2] [b1' H1'] [b2' H2'] Heq'; inv Heq'. *)
  (*   compute in Heq2. subst. *)
  (*   split. *)
  (*   intros Ha bl Hin. edestruct Ha as [Hb Hh]. eassumption. *)
  (*   split; eauto. now rewrite <- Heq1; eauto. intros bl1 Hget1. *)
  (*   edestruct Hh as [bl2 [Hget2 Hbl2]]; eauto. eexists; split; eauto. *)
  (*   assert (Heq : ((f_eq * eq) * eq)%signature ((b1, H2), bl1) ((b2, H2), bl1)) by (split; eauto). *)
  (*   rewrite <- Heq. eassumption. *)
  (*   intros Ha bl Hin. edestruct Ha as [Hb Hh]. eassumption. *)
  (*   split; eauto. now rewrite Heq1; eauto. intros bl1 Hget1. *)
  (*   edestruct Hh as [bl2 [Hget2 Hbl2]]; eauto. eexists; split; eauto. *)
  (*   assert (Heq : ((f_eq * eq) * eq)%signature ((b1, H2), bl1) ((b2, H2), bl1)) by (split; eauto). *)
  (*   rewrite Heq. eassumption. *)
  (* Qed. *)

  (* Instance Proper_heap_approx_f_eq_r : Proper (eq ==> eq ==> RelProd f_eq eq ==> iff) heap_approx. *)
  (* Proof.  *)
  (*   intros s1 s2 hseq [b1 H1] [b2 H2] Heq' [b1' H1'] [b2' H2'] [Heq1 Heq2]; inv Heq'. *)
  (*   compute in Heq2. subst. *)
  (*   split. *)
  (*   intros Ha bl Hin. edestruct Ha as [Hb Hh]. eassumption. *)
  (*   split; eauto. now rewrite <- Heq1; eauto. intros bl1 Hget1. *)
  (*   edestruct Hh as [bl2 [Hget2 Hbl2]]; eauto. eexists; split; eauto. *)
  (*   assert (Heq : ((f_eq * eq) * eq)%signature ((b1', H2'), bl2) ((b2', H2'), bl2)) by (split; eauto). *)
  (*   rewrite <- Heq. eassumption. *)
  (*   intros Ha bl Hin. edestruct Ha as [Hb Hh]. eassumption. *)
  (*   split; eauto. now rewrite  Heq1; eauto. intros bl1 Hget1. *)
  (*   edestruct Hh as [bl2 [Hget2 Hbl2]]; eauto. eexists; split; eauto. *)
  (*   assert (Heq : ((f_eq * eq) * eq)%signature ((b1', H2'), bl2) ((b2', H2'), bl2)) by (split; eauto). *)
  (*   rewrite Heq. eassumption.     *)
  (* Qed. *)

  Instance Proper_heap_equiv_f_eq_r : Proper (eq ==> eq ==> RelProd f_eq eq ==> iff) heap_equiv.
  Proof. 
    intros s1 s2 hseq [b1 H1] [b2 H2] Heq' [b1' H1'] [b2' H2'] Heq. inv Heq'. destruct Heq. inv H0.
    simpl in H1. subst. 
    split; intros Heqh x Hin. 
    assert (Heqp : (f_eq * eq)%signature (b1', (Loc (b2 x), H2')) (b2', (Loc (b2 x), H2')))
      by (split; eauto).
    rewrite <- Heqp, <- H. eapply Heqh. eassumption.
    assert (Heqp : (f_eq * eq)%signature (b1', (Loc (b2 x), H2')) (b2', (Loc (b2 x), H2')))
      by (split; eauto).
    rewrite Heqp, H. eapply Heqh. eassumption.
  Qed. 
  
  Instance Proper_heap_equiv_f_eq_l : Proper (eq ==> RelProd f_eq eq ==> eq ==> iff) heap_equiv.
  Proof.
    intros s1 s2 hseq [b1 H1] [b2 H2] Heq' [b1' H1'] [b2' H2'] Heq. inv Heq'. destruct Heq. inv H0.
    simpl in H3. subst. 
    split; intros Heqh x Hin. rewrite <- H.
    assert (Heqp : (f_eq * eq)%signature (b1, (Loc (b1' x), H2)) (b2, (Loc (b1' x), H2))) by (split; eauto).
    simpl. rewrite <- Heqp. eapply Heqh. eassumption.
    assert (Heqp : (f_eq * eq)%signature (b1, (Loc (b1' x), H2)) (b2, (Loc (b1' x), H2)))
      by (split; eauto).
    simpl. rewrite Heqp, H. simpl. eapply Heqh. eassumption.
  Qed.


  Lemma heap_env_approx_res_approx 
        (S : Ensemble var) (β : loc -> loc)
        (H1 H2 : heap block) (rho1 rho2 : M.t value) l :
    heap_env_approx S (β, (H1, rho1)) (id, (H2, rho2)) ->
    l \in env_locs rho1 S ->
    (Loc l, H1) ≈_(β, id) (Loc (β l), H2).
  Proof.
    intros Henv [x [Heq1 Heq2]].
    destruct (M.get x rho1) as [[l1|] |] eqn:Hget; inv Heq2.
    edestruct Henv as [v2 [Hget2 Hres]]; eauto.
    assert (Hres' := Hres). rewrite res_equiv_eq in Hres.
    destruct v2 as [l2|]; try contradiction. simpl in Hres.
    destruct Hres as [Hres'' _]. unfold id in *; subst.
    eassumption.
  Qed.

  Lemma heap_env_equiv_res_equiv
        (S : Ensemble var) (β : loc -> loc)
        (H1 H2 : heap block) (rho1 rho2 : M.t value) l :
    S |- (H1, rho1) ⩪_(id, β) (H2, rho2) ->
    l \in env_locs rho2 S ->
    (Loc (β l), H1) ≈_(id, β) (Loc l, H2).
  Proof.
    intros Henv Hin.
    symmetry. eapply heap_env_approx_res_approx.
    destruct Henv. eassumption.
    eassumption.
  Qed.

 
  (** Horizontal composition of injections *)

  Lemma res_approx_f_compose_l (β1 β2 β3 β4 : loc -> loc)
        (H1 H2 H3 : heap block)
        (v1 v2 v3 : value) (n : nat) :
    res_approx_fuel' n (β1, (v1, H1)) (β2 ∘ β4, (v2, H2)) ->
    res_approx_fuel' n (β4, (v2, H2)) (β3, (v3, H3)) ->
    res_approx_fuel' n (β1, (v1, H1)) (β2 ∘ β3, (v3, H3)).
  Proof.
    revert v1 v2 v3 H1 H2 H3. induction n as [n IHn] using lt_wf_rec1;
      intros v1 v2 v3 H1 H2 H3 Hres1 Hres2.
    destruct v1 as [l1 | B1 f1]; destruct v2 as [l2 | B2 f2]; destruct v3 as [l3 | B3 f3];
    try now firstorder.
    - simpl in Hres1, Hres2. simpl. destruct (get l1 H1) as [b1 |] eqn:Hget1; eauto.
      destruct b1 as [c1 vs1 | v1 v2 | rho1 ].
      + destruct Hres1 as [Hbs1 [vs2 [Hget2 Hi]]].
        rewrite Hget2 in Hres2. 
        destruct Hres2 as [Hbs2 [vs3 [Hget3 Hj]]].
        simpl. split.
        unfold compose, id in *. congruence.
        eexists; split; eauto. intros i' Hlt.
        eapply Forall2_trans_strong; [| now eapply Hi; eauto | now eapply Hj; eauto ].
        simpl. intros l1' l2' l3' Hr1 Hr2.
        rewrite res_approx_fuel_eq in *. eapply IHn; eauto.
      + destruct Hres1 as [Hbs1 [v1' [v2' [Hget2 Hi]]]].
        rewrite Hget2 in Hres2. 
        destruct Hres2 as [Hbs2 [v1'' [v2'' [Hget3 Hj]]]].
        simpl. split.
        unfold compose, id in *. congruence.
        eexists; eexists; split; eauto. intros i' Hlt.
        rewrite !res_approx_fuel_eq in *.
        split; eapply IHn; try eassumption; rewrite <- !res_approx_fuel_eq.
        now eapply Hi; eauto.
        now eapply Hj; eauto.
        now eapply Hi; eauto.
        now eapply Hj; eauto.
      + destruct Hres1 as [Hbs1 [rho2 [Hget2 Hx]]].
        rewrite Hget2 in Hres2. 
        destruct Hres2 as [Hbs2 [rho3 [Hget3 Hy]]].
        split. unfold compose, id in *. congruence.
        eexists; split; eauto. intros x.
        destruct (Hx x) as [[v1' [v2' [Hgx1 [Hgx2 Hi]]]] | [Hn1 Hn2]];
          destruct (Hy x) as [[v1'' [v2'' [Hgx1' [Hgx2' Hj]]]] | [Hn1' Hn2']];
          try congruence; eauto.
        left. do 2 eexists. split. eassumption. split. eassumption.
        intros j Hlt.
        rewrite !res_approx_fuel_eq in *.
        eapply IHn; eauto; rewrite <- !res_approx_fuel_eq.
        eapply Hi; eauto.
        subst_exp. eapply Hj; eauto.
      + destruct Hres1 as [Hbs1 _].
        destruct Hres2 as [Hbs2 _]. split; eauto. unfold id, compose in *. congruence.
    - firstorder. congruence. congruence.
  Qed.

  Lemma res_approx_f_compose_r (β1 β2 β3 β4 : loc -> loc)
        (H1 H2 H3 : heap block)
        (v1 v2 v3 : value) (n : nat) :
    res_approx_fuel' n (β1, (v1, H1)) (β2, (v2, H2)) ->
    res_approx_fuel' n (β4 ∘ β2, (v2, H2)) (β3, (v3, H3)) ->
    res_approx_fuel' n (β4 ∘ β1, (v1, H1)) (β3, (v3, H3)).
  Proof.
    revert v1 v2 v3 H1 H2 H3. induction n as [n IHn] using lt_wf_rec1; intros v1 v2 v3 H1 H2 H3 Hres1 Hres2.
    destruct v1 as [l1 | B1 f1]; destruct v2 as [l2 | B2 f2]; destruct v3 as [l3 | B3 f3];
    try now firstorder.
    - simpl in Hres1, Hres2. simpl. destruct (get l1 H1) as [b1 |] eqn:Hget1; eauto.
      destruct b1 as [c1 vs1 | v1 v2 | rho1 ].
      + destruct Hres1 as [Hbs1 [vs2 [Hget2 Hi]]].
        rewrite Hget2 in Hres2. 
        destruct Hres2 as [Hbs2 [vs3 [Hget3 Hj]]].
        simpl. split.
        unfold compose, id in *. congruence.
        eexists; split; eauto. intros i' Hlt.
        eapply Forall2_trans_strong; [| now eapply Hi; eauto | now eapply Hj; eauto ].
        simpl. intros l1' l2' l3' Hr1 Hr2.
        rewrite res_approx_fuel_eq in *. eapply IHn; eauto.
      + destruct Hres1 as [Hbs1 [v1' [v2' [Hget2 Hi]]]].
        rewrite Hget2 in Hres2. 
        destruct Hres2 as [Hbs2 [v1'' [v2'' [Hget3 Hj]]]].
        simpl. split.
        unfold compose, id in *. congruence.
        eexists; eexists; split; eauto. intros i' Hlt.
        rewrite !res_approx_fuel_eq in *.
        split; eapply IHn; try eassumption; rewrite <- !res_approx_fuel_eq.
        now eapply Hi; eauto.
        now eapply Hj; eauto.
        now eapply Hi; eauto.
        now eapply Hj; eauto.
      + destruct Hres1 as [Hbs1 [rho2 [Hget2 Hx]]].
        rewrite Hget2 in Hres2. 
        destruct Hres2 as [Hbs2 [rho3 [Hget3 Hy]]].
        split. unfold compose, id in *. congruence.
        eexists; split; eauto. intros x.
        destruct (Hx x) as [[v1' [v2' [Hgx1 [Hgx2 Hi]]]] | [Hn1 Hn2]];
          destruct (Hy x) as [[v1'' [v2'' [Hgx1' [Hgx2' Hj]]]] | [Hn1' Hn2']];
          try congruence; eauto.
        left. do 2 eexists. split. eassumption. split. eassumption.
        intros j Hlt.
        rewrite !res_approx_fuel_eq in *.
        eapply IHn; eauto; rewrite <- !res_approx_fuel_eq.
        eapply Hi; eauto.
        subst_exp. eapply Hj; eauto.
      + destruct Hres1 as [Hbs1 _]. destruct Hres2 as [Hbs2 _].
        split; eauto. unfold compose, id in *. congruence.
    - firstorder. congruence. congruence.
  Qed.
  
  Lemma res_equiv_f_compose (β1 β2 β3 β4 : loc -> loc)
        (H1 H2 H3 : heap block)
        (v1 v2 v3 : value) :
    (v1, H1) ≈_(β1, β2 ∘ β4) (v2, H2) ->
    (v2, H2) ≈_(β4, β3) (v3, H3) ->
    (v1, H1) ≈_(β1, β2 ∘ β3) (v3, H3).
  Proof.
    intros Hres1 Hres2 n. destruct (Hres1 n) as [Hl1 Hr1].
    destruct (Hres2 n) as [Hl2 Hr2].
    split; rewrite !res_approx_fuel_eq in *.
    eapply res_approx_f_compose_l; eassumption.
    eapply res_approx_f_compose_r; eassumption.
  Qed.

      Lemma heap_env_approx_f_compose_l S (β1 β2 β3 β4 : loc -> loc) (H1 H2 H3 : heap block)
          (rho1 rho2 rho3 : M.t value) :
      heap_env_approx S (β1, (H1, rho1)) ((β2 ∘ β4), (H2, rho2)) ->
      heap_env_approx S (β4, (H2, rho2)) (β3, (H3, rho3)) ->
      heap_env_approx S (β1, (H1, rho1)) (β2 ∘ β3, (H3, rho3)).
    Proof.
      intros Heq1 Heq2 x l Hin Hget.
      edestruct Heq1 as [l1' [Hget1 Hres1]]; eauto.
      edestruct Heq2 as [l2' [Hget2 Hres2]]; eauto.
      eexists; split; eauto.
      eapply res_equiv_f_compose. now apply Hres1.
      eassumption.
    Qed.

    Lemma heap_env_approx_f_compose_r
          S (β1 β2 β3 β4 : loc -> loc) (H1 H2 H3 : heap block)
          (rho1 rho2 rho3 : M.t value) :
      heap_env_approx S (β1, (H1, rho1)) (β2, (H2, rho2)) ->
      heap_env_approx S (β4 ∘ β2, (H2, rho2)) (β3, (H3, rho3)) ->
      heap_env_approx S (β4 ∘ β1, (H1, rho1)) (β3, (H3, rho3)).
    Proof.
      intros Heq1 Heq2 x l Hin Hget.
      edestruct Heq1 as [l1' [Hget1 Hres1]]; eauto.
      edestruct Heq2 as [l2' [Hget2 Hres2]]; eauto.
      eexists; split; eauto.
      intros n. destruct (Hres1 n); destruct (Hres2 n).
      split.
      rewrite res_approx_fuel_eq;
      eapply res_approx_f_compose_r;
      rewrite <- res_approx_fuel_eq; eauto.
      rewrite res_approx_fuel_eq;
      eapply res_approx_f_compose_l;
      rewrite <- res_approx_fuel_eq; eauto.
    Qed.
      
    Lemma heap_env_equiv_f_compose S (β1 β2 β3 β4 : loc -> loc) (H1 H2 H3 : heap block)
          (rho1 rho2 rho3 : M.t value) :
      S |- (H1, rho1) ⩪_(β1, β2 ∘ β4) (H2, rho2) ->
      S |- (H2, rho2) ⩪_(β4, β3) (H3, rho3) ->
      S |- (H1, rho1) ⩪_(β1, β2 ∘ β3) (H3, rho3).
    Proof.
      intros [Hyp1 Hyp2] [Hyp1' Hyp2'].
      split.
      eapply heap_env_approx_f_compose_l; try eassumption.
      eapply heap_env_approx_f_compose_r; try eassumption.
    Qed.
    
    Lemma block_equiv_f_compose (β1 β2 β3 β4 : loc -> loc) (H1 H2 H3 : heap block)
          (b1 b2 b3 : block) :
      block_equiv (β1, H1, b1) ((β2 ∘ β4), H2, b2) ->
      block_equiv (β4, H2, b2) (β3, H3, b3) ->
      block_equiv (β1, H1, b1) (β2 ∘ β3, H3, b3).
    Proof.
      intros Hb1 Hb2.
      destruct b1; destruct b2; destruct b3;
      try contradiction; simpl in *.
      - destruct Hb1 as [Heq Hall].
        destruct Hb2 as [Heq' Hall'].
        subst. split; eauto.
        eapply Forall2_vertical_r_strong;
          [| now apply Hall | now apply Hall' ].
        intros x1 x2 x3 Hin1 Hin2 Hin3 Hl1 Hl2.
        eapply res_equiv_f_compose. now apply Hl1.
        now apply Hl2.
      - destruct Hb1 as [Heq1 Heq2].
        destruct Hb2 as [Heq1' Heq2'].
        split; eapply res_equiv_f_compose; eauto.
      - eapply heap_env_equiv_f_compose; eauto.
    Qed.

    (* Lemma heap_equiv_f_compose S (β1 β2 β3 β4 : loc -> loc) (H1 H2 H3 : heap block) : *)
    (*   S |- H1 ≃_(β1, β2 ∘ β4) H2 -> *)
    (*   S |- H2 ≃_(β4, β3) H3 -> *)
    (*   S |- H1 ≃_(β1, β2 ∘ β3) H3. *)
    (* Proof. *)
    (*   intros [Hyp1 Hyp2] [Hyp1' Hyp2']. *)
    (*   split. *)
    (*   - intros x Hin. *)
    (*     destruct (Hyp1 x Hin) as [Heqb1 Hh1]. *)
    (*     destruct (Hyp1' x Hin) as [Heqb1' Hh1']. *)
    (*     split. unfold compose in *. congruence. *)
    (*     intros bl1 Hget. *)
    (*     edestruct Hh1 as [bl2 [Hget2 Heq2]]; eauto. *)
    (*     edestruct Hh1' as [bl2' [Hget2' Heq2']]; eauto. *)
    (*     eexists; split; eauto. *)
    (*     eapply block_equiv_f_compose; eauto. *)
    (*   - intros x Hin. *)
    (*     destruct (Hyp2 x Hin) as [Heqb1 Hh1]. *)
    (*     destruct (Hyp2' x Hin) as [Heqb1' Hh1']. *)
    (*     split. unfold compose in *. congruence. *)
    (*     intros bl1 Hget. *)
    (*     edestruct Hh1' as [bl2' [Hget2' Heq2']]; eauto. *)
    (*     edestruct Hh1 as [bl2 [Hget2 Heq2]]; eauto. *)
    (*     eexists; split; eauto. *)
    (*     symmetry. eapply block_equiv_f_compose; symmetry; eauto. *)
    (* Qed. *)

  (** Proper instances *)
  
  Instance Proper_heap_env_approx : Proper (Same_set _ ==> eq ==> eq ==> iff) heap_env_approx.
  Proof.
    intros s1 s2 hseq [b1 [H1 rho1]] [b2 [H2 rho2]] Heq [b1' [H1' p1']] [b2' [H2' p2']] Heq';
    inv Heq; inv Heq'. 
    subst; split; intros Ha ? ? ?; firstorder.
  Qed.
  
  Instance Proper_heap_env_equiv : Proper (Same_set _ ==> eq ==> eq ==> iff) heap_env_equiv.
  Proof.
    intros s1 s2 hseq [b1 [H1 rho1]] [b2 [H2 rho2]] Heq [b1' [H1' p1']] [b2' [H2' p2']] Heq';
    inv Heq; inv Heq'.
    split; intros [h1 h2]; split; (try now rewrite hseq; eauto);
    rewrite <- hseq; eauto.
  Qed.

  Instance Proper_heap_equiv : Proper (Same_set _ ==> eq ==> eq ==> iff) heap_equiv.
  Proof.
    intros s1 s2 hseq [b1 H1] [b2 H2] Heq [b1' H1'] [b2' H2'] Heq'; inv Heq; inv Heq'.
    split; intros Heqh x Hin; eapply Heqh; eapply hseq; eassumption.
  Qed.
  
  (** Monotonicity properties *)

  Lemma heap_env_equiv_antimon S1 S2 H1 H2 b1 b2 rho1 rho2 :
    S1 |- (H1, rho1) ⩪_(b1, b2) (H2, rho2) ->
    S2 \subset S1 ->
    S2 |- (H1, rho1) ⩪_(b1, b2) (H2, rho2).
  Proof.
    firstorder.
  Qed.
  
  (** Weakening lemmas *)
      
  Lemma res_approx_weakening (S1 S2 : Ensemble loc) β1 β2 (H1 H2 H1' H2' : heap block)
        (v1 v2 : value) (i : nat) :
    closed S1 H1 -> closed S2 H2 ->
    res_approx_fuel' i (β1, (v1, H1)) (β2, (v2, H2)) ->
    H1 ⊑ H1' -> 
    H2 ⊑ H2' ->
    val_loc v1 \subset S1 -> val_loc v2 \subset S2 -> 
    res_approx_fuel' i (β1, (v1, H1')) (β2, (v2, H2')).
  Proof with (now eauto with Ensembles_DB).
    intros Hwf1 Hwf2 Heq Hsub1 Hsub2.
    revert v1 v2 Heq; induction i using lt_wf_rec1;
    intros v1 v2 Heq Hdom1 Hdom2.
    destruct v1 as [ l1 | B1 f1]; destruct v2 as [ l2 | V2 f2]; try contradiction. 
    { edestruct Hwf1 as [b1' [Hget1 Hsub1']].
      eapply Hdom1; reflexivity. 
      edestruct Hwf2 as [b2' [Hget2 Hsub2']].
      eapply Hdom2; reflexivity. 
      specialize (Hsub1 _ _ Hget1).
      specialize (Hsub2 _ _ Hget2).
      simpl in Hget1, Hget2, Hsub1, Heq. 
      simpl.
      rewrite Hsub1. rewrite Hget1 in Heq. destruct b1'.
      - edestruct Heq as [Heq1' [vs2 [Hgetl2 Hall]]]; eauto.
        subst_exp. split; eauto.
        eexists; split; [ now eauto |].
        intros i' Hlt.
        eapply Forall2_monotonic_strong
        with (R :=
                fun l3 l4 =>
                  val_loc l3 \subset S1 ->
                  val_loc l4 \subset S2 -> res_approx_fuel i' (β1, (l3, H1)) (β2, (l4, H2))).
        * intros v1' v2' Hin1 Hin2 Hyp. 
          rewrite res_approx_fuel_eq. eapply H; eauto.
          rewrite <- res_approx_fuel_eq. eapply Hyp; eauto.
          simpl in Hsub1'. eapply Included_trans; [| eassumption].
          eapply In_Union_list. now eapply in_map; eauto.
          simpl in Hsub2'. eapply Included_trans; [| eassumption].
          eapply In_Union_list. now eapply in_map; eauto.
          simpl in Hsub1'. eapply Included_trans; [| eassumption].
          eapply In_Union_list. now eapply in_map; eauto.
          simpl in Hsub2'. eapply Included_trans; [| eassumption].
          eapply In_Union_list. now eapply in_map; eauto.
        * eapply Forall2_monotonic; [| eauto ].
          intros. eassumption.
      - edestruct Heq as [Heq1' [v1' [v2' [Hgetl2 Hall]]]]; eauto.
        subst_exp. split; eauto.
        eexists; eexists; split; [ now eauto |].
        intros i' Hlt.
        rewrite !res_approx_fuel_eq. split; eauto.
        eapply H; eauto. rewrite <- res_approx_fuel_eq.
        now eapply Hall; eauto.
        simpl in Hsub1'. eapply Included_trans; [| eassumption]...
        simpl in Hsub1'. eapply Included_trans; [| eassumption]...
        eapply H; eauto. rewrite <- res_approx_fuel_eq.
        now eapply Hall; eauto.
        simpl in Hsub1'. eapply Included_trans; [| eassumption]...
        simpl in Hsub1'. eapply Included_trans; [| eassumption]...
      - edestruct Heq as [Heq1' [rho2 [Hgetl2 Hall]]]; eauto.
        subst_exp. split; eauto.
        eexists; split; [ now eauto |].
        intros x.
        edestruct Hall as [[v1 [v2 [Hs1 [Hs2 Hi]]]] | Hnone]; eauto.
        left. repeat eexists; eauto. intros i' Hlt.
        rewrite res_approx_fuel_eq. eapply H; eauto.
        rewrite <- res_approx_fuel_eq. eapply Hi. eassumption.
        simpl in Hsub1'. eapply Included_trans; [| eassumption].
        eapply get_In_env_locs; eauto. now constructor.
        simpl in Hsub2'. eapply Included_trans; [| eassumption].
        eapply get_In_env_locs; eauto. now constructor. }
    { simpl in *; eassumption. }
  Qed.
  
  Corollary res_equiv_weakening (S1 S2 : Ensemble loc) β1 β2 (H1 H2 H1' H2' : heap block)
            (v1 v2 : value) :
    closed S1 H1 -> closed S2 H2 ->
    (v1, H1) ≈_(β1, β2) (v2, H2) ->
    H1 ⊑ H1' ->
    H2 ⊑ H2' ->
    val_loc v1 \subset S1 -> val_loc v2 \subset S2 -> 
    (v1, H1') ≈_(β1, β2) (v2, H2').
  Proof.
    intros Hwf1 Hwf2 Heq Hsub1 Hsub2 Hin1 Hin2 n. destruct (Heq n) as [Heq1 He2].
    split; rewrite res_approx_fuel_eq.
    eapply (res_approx_weakening S1 S2 β1 β2 H1 H2 H1' H2'); eauto.
    now rewrite <- res_approx_fuel_eq.
    eapply (res_approx_weakening S2 S1 β2 β1 H2 H1 H2' H1'); eauto.
    now rewrite <- res_approx_fuel_eq. 
  Qed.


  Lemma heap_env_approx_weakening S β1 β2 H1 H2 H1' H2' rho1 rho2 :
    well_formed (reach' H1 (env_locs rho1 S)) H1 ->
    well_formed (reach' H2 (env_locs rho2 S)) H2 ->
    env_locs rho1 S \subset dom H1 ->
    env_locs rho2 S \subset dom H2 ->
    S |- (H1, rho1) ⩪_(β1, β2) (H2, rho2) ->
    H1 ⊑ H1' ->
    H2 ⊑ H2' ->
    heap_env_approx S (β1, (H1', rho1)) (β2, (H2', rho2)).
  Proof.
    intros Hwf1 Hwf2 He1 He2  [Heq1 Heq2] Hal1 Hal2 y l Hin Hget; simpl.
    edestruct Heq1 as [x' [Hget' Heq']]; eauto.
    eexists; split; eauto.
    eapply (res_equiv_weakening _ _ β1 β2 H1 H2).
    eapply reach'_closed. now apply Hwf1. eassumption.
    eapply reach'_closed. now apply Hwf2. eassumption.
    eassumption. eassumption. eassumption.
    eapply Included_trans; [| eapply reach'_extensive ].
    now eapply get_In_env_locs; eauto.
    eapply Included_trans; [| eapply reach'_extensive ].
    now eapply get_In_env_locs; eauto.
  Qed.
  
  Corollary heap_env_equiv_weaking_cor S β1 β2 H1 H2 H1' H2' rho1 rho2 :
    well_formed (reach' H1 (env_locs rho1 S)) H1 ->
    well_formed (reach' H2 (env_locs rho2 S)) H2 ->
    env_locs rho1 S \subset dom H1 ->
    env_locs rho2 S \subset dom H2 ->
    S |- (H1, rho1) ⩪_(β1, β2) (H2, rho2) ->
    H1 ⊑ H1' ->
    H2 ⊑ H2' ->
    S |- (H1', rho1) ⩪_(β1, β2) (H2', rho2).
  Proof.
    intros. split.
    now eapply (heap_env_approx_weakening _ _ _ H1 H2); eauto.
    now eapply (heap_env_approx_weakening _ _ _ H2 H1); eauto; symmetry.
  Qed.
  
  Lemma heap_env_approx_weakening' S S1 S2 β1 β2 H1 H2 H1' H2' rho1 rho2 :
     closed S1 H1 -> closed S2 H2 ->
     env_locs rho1 S \subset S1 ->
     env_locs rho2 S \subset S2 ->
     S |- (H1, rho1) ⩪_(β1, β2) (H2, rho2) ->
     H1 ⊑ H1' ->
     H2 ⊑ H2' ->
     heap_env_approx S (β1, (H1', rho1)) (β2, (H2', rho2)).
  Proof.
     intros Hwf1 Hwf2 He1 He2  [Heq1 Heq2] Hal1 Hal2 y l Hin Hget; simpl.
     edestruct Heq1 as [x' [Hget' Heq']]; eauto.
     eexists; split; eauto.
     eapply (res_equiv_weakening _ _ _ _ H1 H2); eauto.
     eapply Included_trans; [| eassumption ].
     now eapply get_In_env_locs; eauto.
     eapply Included_trans; [| eassumption ].
     now eapply get_In_env_locs; eauto.
  Qed.
  
  Corollary heap_env_equiv_weaking' S S1 S2 β1 β2 H1 H2 H1' H2' rho1 rho2 :
    closed S1 H1 -> closed S2 H2 ->
    env_locs rho1 S \subset S1 ->
    env_locs rho2 S \subset S2 ->
    S |- (H1, rho1) ⩪_(β1, β2) (H2, rho2) ->
    H1 ⊑ H1' ->
    H2 ⊑ H2' ->
    S |- (H1', rho1) ⩪_(β1, β2) (H2', rho2).
  Proof.
     intros. split.
     now eapply (heap_env_approx_weakening' _ _ _ _ _ H1 H2); eauto.
     now eapply (heap_env_approx_weakening' _ _ _ _ _ H2 H1); eauto; symmetry.
  Qed.
  
  Lemma res_approx_weakening_alt (S1 S2 : Ensemble loc) β1 β2 (H1 H2 H1' H2' : heap block)
        (v1 v2 : value) (i : nat) :
    closed S1 H1 -> closed S2 H2 ->
    res_approx_fuel' i (β1, (v1, H1)) (β2, (v2, H2)) ->
    H1 ⊑ H1' -> 
    H2 ⊑ H2' ->
    (val_loc v1) \subset dom H1 ->
    (val_loc v2) \subset dom H2 ->
    post H1 (val_loc v1) \subset S1 ->
    post H2 (val_loc v2) \subset S2 ->
    res_approx_fuel' i (β1, (v1, H1')) (β2, (v2, H2')) .
  Proof with (now eauto with Ensembles_DB).
    intros Hwf1 Hwf2 Heq Hsub1 Hsub2.
    revert v1 v2 Heq; induction i using lt_wf_rec1;
    intros v1 v2 Heq Hdom1 Hdom2 Hpost1 Hpost2.
    destruct v1 as [ l1 | B1 f1]; destruct v2 as [ l2 | V2 f2]; try contradiction. 
    { edestruct Hdom1 as [b1 Hget1]; eauto. reflexivity.
      edestruct Hdom2 as [b2 Hget2]; eauto. reflexivity.
      specialize (Hsub1 _ _ Hget1).
      specialize (Hsub2 _ _ Hget2).
      simpl in Hget1, Hget2, Hsub1, Heq. 
      simpl.
      rewrite Hsub1. rewrite Hget1 in Heq. destruct b1.
      - edestruct Heq as [Heq' [vs2 [Hgetl2 Hall]]]; eauto.
        subst_exp. split; eauto.
        eexists; split; [ now eauto |].
        intros i' Hlt.
        eapply Forall2_monotonic_strong
        with (R :=
                fun l3 l4 =>
                  val_loc l3 \subset dom H1 ->
                  val_loc l4 \subset dom H2 -> res_approx_fuel i' (β1, (l3, H1)) (β2, (l4, H2))).
        * intros v1' v2' Hin1 Hin2 Hyp.
          assert (Hinv1 : val_loc v1' \subset dom H1).
          { eapply Included_trans; [| now eapply in_dom_closed; eauto ].
            eapply Included_trans; [| eassumption ].
            simpl. rewrite post_Singleton; [| eassumption ].
            eapply In_Union_list. eapply in_map. eassumption. }
          assert (Hinv2 : val_loc v2' \subset dom H2).
          { eapply Included_trans; [| now eapply in_dom_closed; eauto ].
            eapply Included_trans; [| eassumption ].
            simpl. rewrite post_Singleton; [| eassumption ].
            eapply In_Union_list. eapply in_map. eassumption. }
          rewrite res_approx_fuel_eq. eapply H; eauto.
          rewrite <- res_approx_fuel_eq. eapply Hyp; eauto.
          eapply Included_trans; [| now eapply closed_reach_in_S; eauto ].
          eapply Included_trans; [| now eapply reach'_set_monotonic; eauto ].
          eapply Included_trans; [| now eapply Included_post_reach'; eauto ].
          eapply post_set_monotonic.
          simpl. rewrite post_Singleton; [| eassumption ].
          eapply In_Union_list. eapply in_map. eassumption.
          eapply Included_trans; [| now eapply closed_reach_in_S; eauto ].
          eapply Included_trans; [| now eapply reach'_set_monotonic; eauto ].
          eapply Included_trans; [| now eapply Included_post_reach'; eauto ].
          eapply post_set_monotonic.
          simpl. rewrite post_Singleton; [| eassumption ].
          eapply In_Union_list. eapply in_map. eassumption.
        * eapply Forall2_monotonic; [| eauto ].
          intros. eassumption.
      - edestruct Heq as [Heq2 [v1' [v2' [Hgetl2 Hall]]]]; eauto.
        subst_exp. split; eauto.
        eexists; eexists; split; [ now eauto |].
        intros i' Hlt.
        split.

        rewrite res_approx_fuel_eq. eapply H; eauto.
        rewrite <- res_approx_fuel_eq. now eapply Hall; eauto.

        eapply Included_trans; [| now eapply in_dom_closed; eauto ].
        eapply Included_trans; [| eassumption ].
        simpl. rewrite post_Singleton; [| eassumption ]...
        eapply Included_trans; [| now eapply in_dom_closed; eauto ].
        eapply Included_trans; [| eassumption ].
        simpl. rewrite post_Singleton; [| eassumption ]...

        eapply Included_trans; [| now eapply closed_reach_in_S; eauto ].
        eapply Included_trans; [| now eapply reach'_set_monotonic; eauto ].
        eapply Included_trans; [| now eapply Included_post_reach'; eauto ].
        eapply post_set_monotonic.
        simpl. rewrite post_Singleton; [| eassumption ]...
        eapply Included_trans; [| now eapply closed_reach_in_S; eauto ].
        eapply Included_trans; [| now eapply reach'_set_monotonic; eauto ].
        eapply Included_trans; [| now eapply Included_post_reach'; eauto ].
        eapply post_set_monotonic.
        simpl. rewrite post_Singleton; [| eassumption ]...

        rewrite res_approx_fuel_eq. eapply H; eauto.
        rewrite <- res_approx_fuel_eq. now eapply Hall; eauto.

        eapply Included_trans; [| now eapply in_dom_closed; eauto ].
        eapply Included_trans; [| eassumption ].
        simpl. rewrite post_Singleton; [| eassumption ]...
        eapply Included_trans; [| now eapply in_dom_closed; eauto ].
        eapply Included_trans; [| eassumption ].
        simpl. rewrite post_Singleton; [| eassumption ]...

        eapply Included_trans; [| now eapply closed_reach_in_S; eauto ].
        eapply Included_trans; [| now eapply reach'_set_monotonic; eauto ].
        eapply Included_trans; [| now eapply Included_post_reach'; eauto ].
        eapply post_set_monotonic.
        simpl. rewrite post_Singleton; [| eassumption ]...
        eapply Included_trans; [| now eapply closed_reach_in_S; eauto ].
        eapply Included_trans; [| now eapply reach'_set_monotonic; eauto ].
        eapply Included_trans; [| now eapply Included_post_reach'; eauto ].
        eapply post_set_monotonic.
        simpl. rewrite post_Singleton; [| eassumption ]...

      - edestruct Heq as [Heq2 [rho2 [Hgetl2 Hall]]]; eauto.
        subst_exp. split; eauto.
        eexists; split; [ now eauto |].
        intros x.
        edestruct Hall as [[v1 [v2 [Hs1 [Hs2 Hi]]]] | Hnone]; eauto.
        left. repeat eexists; eauto. intros i' Hlt.
        rewrite res_approx_fuel_eq. eapply H; eauto.
        + rewrite <- res_approx_fuel_eq. eapply Hi. eassumption.
        + eapply Included_trans; [| now eapply in_dom_closed; eauto ].
          eapply Included_trans; [| eassumption ].
          simpl. rewrite post_Singleton; [| eassumption ].
          eapply get_In_env_locs. now constructor. eassumption. 
        + eapply Included_trans; [| now eapply in_dom_closed; eauto ].
          eapply Included_trans; [| eassumption ].
          simpl. rewrite post_Singleton; [| eassumption ].
          eapply get_In_env_locs. now constructor. eassumption.
        + eapply Included_trans; [| now eapply closed_reach_in_S; eauto ].
          eapply Included_trans; [| now eapply reach'_set_monotonic; eauto ].
          eapply Included_trans; [| now eapply Included_post_reach'; eauto ].
          eapply post_set_monotonic.
          simpl. rewrite post_Singleton; [| eassumption ].
          eapply get_In_env_locs. now constructor. eassumption.
        + eapply Included_trans; [| now eapply closed_reach_in_S; eauto ].
          eapply Included_trans; [| now eapply reach'_set_monotonic; eauto ].
          eapply Included_trans; [| now eapply Included_post_reach'; eauto ].
          eapply post_set_monotonic.
          simpl. rewrite post_Singleton; [| eassumption ].
          eapply get_In_env_locs. now constructor. eassumption. }
    { simpl in *; eassumption. }
  Qed.

  
  Corollary res_equiv_weakening_alt (S1 S2 : Ensemble loc) β1 β2 (H1 H2 H1' H2' : heap block)
            (v1 v2 : value) :
    closed S1 H1 -> closed S2 H2 ->
    (v1, H1) ≈_(β1, β2) (v2, H2) ->
    H1 ⊑ H1' ->
    H2 ⊑ H2' ->
    (val_loc v1) \subset dom H1 ->
    (val_loc v2) \subset dom H2 ->
    post H1 (val_loc v1) \subset S1 ->
    post H2 (val_loc v2) \subset S2 ->
    (v1, H1') ≈_(β1, β2) (v2, H2').
  Proof.
    intros Hwf1 Hwf2 Heq Hsub1 Hsub2 Hp1 Hp2 Hin1 Hin2 n. destruct (Heq n) as [Heq1 He2].
    split; rewrite res_approx_fuel_eq.
    eapply (res_approx_weakening_alt S1 S2 _ _ H1 H2 H1' H2'); eauto.
    now rewrite <- res_approx_fuel_eq.
    eapply (res_approx_weakening_alt S2 S1 _ _ H2 H1 H2' H1'); eauto.
    now rewrite <- res_approx_fuel_eq. 
  Qed.
  
  Lemma heap_env_approx_weakening_alt S S1 S2 β1 β2 H1 H2 H1' H2' rho1 rho2 :
     closed S1 H1 -> closed S2 H2 ->
     env_locs rho1 S \subset dom H1 ->
     env_locs rho2 S \subset dom H2 ->
     post H1 (env_locs rho1 S) \subset S1 ->
     post H2 (env_locs rho2 S) \subset S2 ->
     S |- (H1, rho1) ⩪_(β1, β2) (H2, rho2) ->
     H1 ⊑ H1' ->
     H2 ⊑ H2' ->
     heap_env_approx S (β1, (H1', rho1)) (β2, (H2', rho2)).
  Proof.
    intros Hwf1 Hwf2 He1 He2 Hp1 Hp2 [Heq1 Heq2] Hal1 Hal2 y l Hin Hget; simpl.
    edestruct Heq1 as [x' [Hget' Heq']]; eauto.
    eexists; split; eauto.
    eapply (res_equiv_weakening_alt _ _ _ _ H1 H2); eauto.
    eapply Included_trans; [| eassumption ].
    now eapply get_In_env_locs; eauto.
    eapply Included_trans; [| eassumption ].
    now eapply get_In_env_locs; eauto.
    eapply Included_trans; [| eassumption ].
    eapply post_set_monotonic.
    now eapply get_In_env_locs; eauto.
    eapply Included_trans; [| eassumption ].
    eapply post_set_monotonic.
    now eapply get_In_env_locs; eauto.
  Qed.
  
  Corollary heap_env_equiv_weaking_alt S S1 S2 β1 β2 H1 H2 H1' H2' rho1 rho2 :
    closed S1 H1 -> closed S2 H2 ->
    env_locs rho1 S \subset dom H1 ->
    env_locs rho2 S \subset dom H2 ->
    post H1 (env_locs rho1 S) \subset S1 ->
    post H2 (env_locs rho2 S) \subset S2 ->
    S |- (H1, rho1) ⩪_(β1, β2) (H2, rho2) ->
    H1 ⊑ H1' ->
    H2 ⊑ H2' ->
    S |- (H1', rho1) ⩪_(β1, β2) (H2', rho2).
  Proof.
    intros. split.
    now eapply (heap_env_approx_weakening_alt _ _ _ _ _ H1 H2); eauto.
    now eapply (heap_env_approx_weakening_alt _ _ _ _ _ H2 H1); eauto; symmetry.
  Qed.
  
  (** Preservation under store and heap extension *)
  
  Lemma heap_env_approx_set S β1 β2 H1 H2 x l1 l2 rho1 rho2 :
    heap_env_approx (Setminus _ S (Singleton _ x)) (β1, (H1, rho1)) (β2, (H2, rho2)) ->
    (l1, H1) ≈_(β1, β2) (l2, H2) ->
    heap_env_approx S (β1, (H1, M.set x l1 rho1)) (β2, (H2, M.set x l2 rho2)).
  Proof.
    intros Heq Hreq. intros y l Hin Hget.
    destruct (peq x y); subst; simpl in *. 
    - exists l2. rewrite M.gss in *; inv Hget; eauto.
    - rewrite M.gso in *; eauto. eapply Heq in Hget; eauto.
      constructor; eauto. intros Hc; inv Hc; congruence.
  Qed.

  Lemma heap_env_equiv_set S β1 β2 H1 H2 x l1 l2 rho1 rho2 :
    Setminus _ S (Singleton _ x) |- (H1, rho1) ⩪_(β1, β2) (H2, rho2) ->
    (l1, H1) ≈_(β1, β2) (l2, H2) ->
    S  |- (H1, M.set x l1 rho1) ⩪_(β1, β2) (H2, M.set x l2 rho2).
  Proof.
    intros [Heq1 Heq2] Hreq. split.
    now eapply heap_env_approx_set.
    now eapply heap_env_approx_set; eauto; symmetry.
  Qed.

  (** Renaming extensions *)

  Lemma Included_Intersection_compat {A : Type} (s1 s2 s3 s4 : Ensemble A) :
    s1 \subset s2 ->
    s3 \subset s4 ->
    s1 :&: s3 \subset s2 :&: s4.
  Proof.
    intros H1 H2 x [Hin1 Hin2]. firstorder.
  Qed.

  Lemma Included_Intersection_l {A : Type} (s1 s2 : Ensemble A) :
    s1 :&: s2 \subset s1.
  Proof.
    intros x [Hin1 Hin2]; eauto.
  Qed.

  Lemma Included_Intersection_r {A : Type} (s1 s2 : Ensemble A) :
    s1 :&: s2 \subset s2.
  Proof.
    intros x [Hin1 Hin2]; eauto.
  Qed.

  Lemma res_approx_rename_ext i β1 β1' β2 β2' H1 H2 v1 v2: 
    res_approx_fuel' i (β1, (v1, H1)) (β2, (v2, H2)) ->
    f_eq_subdomain (reach' H1 (val_loc v1)) β1 β1' ->
    f_eq_subdomain (reach' H2 (val_loc v2)) β2 β2' ->
    res_approx_fuel' i (β1', (v1, H1)) (β2', (v2, H2)).
  Proof with (now eauto with Ensembles_DB).
    revert v1 v2.
    induction i as [i IHk] using lt_wf_rec1; intros v1 v2 Hres Hfeq Hfeq'.
    destruct v1 as [l1 | B1 f1]; destruct v2 as [l2 | B2 f2]; try now firstorder.
    destruct Hres as [Heqb Hres].
    simpl in Hres; simpl; destruct (get l1 H1) as [b1 |] eqn:Hget; eauto.
    destruct b1.
    - destruct Hres as [vs2 [Hget2 Hi]].
      split.
      + rewrite <- Hfeq, <- Hfeq'. eassumption.
        now eapply reach'_extensive.
        now eapply reach'_extensive.
      + eexists. split; eauto.
        intros i' Hi'.
        eapply Forall2_monotonic_strong; eauto.
        intros x1 x2 Hl1 Hl2 Hres. simpl in Hres.
        rewrite res_approx_fuel_eq in *. eapply IHk.
        eassumption. eassumption. 

        eapply f_eq_subdomain_antimon; [| eassumption ].
        rewrite (reach_unfold H1 (val_loc (Loc l1))).
        eapply Included_Union_preserv_r. eapply reach'_set_monotonic.
        simpl; rewrite post_Singleton; [| eassumption ]. simpl.
        eapply In_Union_list. eapply in_map. eassumption.

        eapply f_eq_subdomain_antimon; [| eassumption ].
        rewrite (reach_unfold H2 (val_loc (Loc l2))).
        eapply Included_Union_preserv_r. eapply reach'_set_monotonic.
        simpl; rewrite post_Singleton; [| eassumption ]. simpl.
        eapply In_Union_list. eapply in_map. eassumption.
        
    - destruct Hres as [Heqb' [vs2 [Hget2 Hi]]].
      split.
      + rewrite <- Hfeq, <- Hfeq'. eassumption.
        now eapply reach'_extensive.
        now eapply reach'_extensive.
      + do 2 eexists. split. eassumption.
        setoid_rewrite res_approx_fuel_eq in Hi.
        intros i' Hi'. split.
        rewrite res_approx_fuel_eq in *. eapply IHk; try eassumption.
        eapply Hi. eassumption.

        eapply f_eq_subdomain_antimon; [| eassumption ].
        rewrite (reach_unfold H1 (val_loc (Loc l1))).
        eapply Included_Union_preserv_r. eapply reach'_set_monotonic.
        simpl; rewrite post_Singleton; [| eassumption ]...

        eapply f_eq_subdomain_antimon; [| eassumption ].
        rewrite (reach_unfold H2 (val_loc (Loc l2))).
        eapply Included_Union_preserv_r. eapply reach'_set_monotonic.
        simpl; rewrite post_Singleton; [| eassumption ]...

        rewrite res_approx_fuel_eq in *. eapply IHk; try eassumption.
        eapply Hi. eassumption.

        eapply f_eq_subdomain_antimon; [| eassumption ].
        rewrite (reach_unfold H1 (val_loc (Loc l1))).
        eapply Included_Union_preserv_r. eapply reach'_set_monotonic.
        simpl; rewrite post_Singleton; [| eassumption ]...

        eapply f_eq_subdomain_antimon; [| eassumption ].
        rewrite (reach_unfold H2 (val_loc (Loc l2))).
        eapply Included_Union_preserv_r. eapply reach'_set_monotonic.
        simpl; rewrite post_Singleton; [| eassumption ]...

    - destruct Hres as [rho2 [Hget2 Hx]].
      split.
      + rewrite <- Hfeq, <- Hfeq'. eassumption.
        now eapply reach'_extensive.
        now eapply reach'_extensive.
      + eexists. split; eauto. intros x.
        destruct (Hx x) as [[v1 [v2 [Hgetx1 [Hgetx2 Hi]]]] | Hgetx ]; eauto.
        left. repeat eexists; eauto. intros i' Hi'. 
        rewrite res_approx_fuel_eq in *. eapply IHk; try eassumption.
        setoid_rewrite res_approx_fuel_eq in Hi.
        eapply Hi.  eassumption.

        eapply f_eq_subdomain_antimon; [| eassumption ].
        rewrite (reach_unfold H1 (val_loc (Loc l1))).
        eapply Included_Union_preserv_r. eapply reach'_set_monotonic.
        simpl; rewrite post_Singleton; [| eassumption ]. simpl.
        eapply get_In_env_locs; eauto. constructor.

        eapply f_eq_subdomain_antimon; [| eassumption ].
        rewrite (reach_unfold H2 (val_loc (Loc l2))).
        eapply Included_Union_preserv_r. eapply reach'_set_monotonic.
        simpl; rewrite post_Singleton; [| eassumption ]. simpl.
        eapply get_In_env_locs; eauto. constructor.
    - destruct Hres; split; eauto. rewrite <- Hfeq, <- Hfeq'. eassumption.
      now eapply reach'_extensive.
      now eapply reach'_extensive.
  Qed. 


  Lemma res_equiv_rename_ext β1 β1' β2 β2' H1 H2 v1 v2 : 
    (v1, H1) ≈_(β1, β2) (v2, H2) ->
    f_eq_subdomain (reach' H1 (val_loc v1)) β1 β1' ->
    f_eq_subdomain (reach' H2 (val_loc v2)) β2 β2' ->
    (v1, H1) ≈_(β1', β2') (v2, H2).
  Proof.
    intros Heq Hfeq1 Hfeq2 x; split. 
    rewrite res_approx_fuel_eq. eapply res_approx_rename_ext; eauto.
    rewrite <- res_approx_fuel_eq. now eapply Heq; eauto.
    rewrite res_approx_fuel_eq. eapply res_approx_rename_ext; eauto.
    rewrite <- res_approx_fuel_eq. now eapply Heq; eauto.
  Qed.

  Lemma heap_env_approx_rename_ext S β1 β1' β2 β2' H1 H2 rho1 rho2 : 
    heap_env_approx S (β1, (H1, rho1)) (β2, (H2, rho2)) ->
    f_eq_subdomain (reach' H1 (env_locs rho1 S)) β1 β1' ->
    f_eq_subdomain (reach' H2 (env_locs rho2 S)) β2 β2' ->
    heap_env_approx S (β1', (H1, rho1)) (β2', (H2, rho2)).
  Proof.
    intros Hap Heq1 Heq2 x l Hin Hget.  
    edestruct Hap as [l' [Hgetl' Hres]]; eauto.
    eexists; split; eauto.
    eapply res_equiv_rename_ext; eauto.

    eapply f_eq_subdomain_antimon; [| eassumption ].
    eapply reach'_set_monotonic. 
    now eapply get_In_env_locs; eauto.

    eapply f_eq_subdomain_antimon; [| eassumption ].
    eapply reach'_set_monotonic. 
    now eapply get_In_env_locs; eauto.
  Qed.

  Corollary heap_env_equiv_rename_ext S β1 β1' β2 β2' H1 H2 rho1 rho2 : 
    S |- (H1, rho1) ⩪_(β1, β2) (H2, rho2) ->
    f_eq_subdomain (reach' H1 (env_locs rho1 S)) β1 β1' ->
    f_eq_subdomain (reach' H2 (env_locs rho2 S)) β2 β2' ->
    S |- (H1, rho1) ⩪_(β1', β2') (H2, rho2).
  Proof.
    intros [Heq1 Heq2] Hfeq1 Hfeq2; split. 
    now eapply heap_env_approx_rename_ext; eauto.
    now eapply heap_env_approx_rename_ext; eauto.
  Qed.

  Lemma block_equiv_rename_ext β1 β1' β2 β2' H1 H2 b1 b2 : 
    block_equiv (β1, H1, b1) (β2, H2, b2) ->
    f_eq_subdomain (reach' H1 (locs b1)) β1 β1' ->
    f_eq_subdomain (reach' H2 (locs b2)) β2 β2' ->
    block_equiv (β1', H1, b1) (β2', H2, b2).
  Proof with (now eauto with Ensembles_DB) .
    intros Hb1 Hfeq1 Hfeq2.
    destruct b1; destruct b2; try contradiction; simpl in *.
    - destruct Hb1 as [Heq Hall].
      split; eauto.
      eapply Forall2_monotonic_strong; eauto.
      intros x1 x2 Hl1 Hl2 Hres. simpl in Hres.
      eapply res_equiv_rename_ext; eauto.

      eapply f_eq_subdomain_antimon; [| eassumption ].
      eapply reach'_set_monotonic.
      eapply In_Union_list. eapply in_map. eassumption.
      
      eapply f_eq_subdomain_antimon; [| eassumption ].
      eapply reach'_set_monotonic.
      eapply In_Union_list. eapply in_map. eassumption.

    - destruct Hb1 as [Hb1 Hb2]. split.
      
      eapply res_equiv_rename_ext; eauto.

      eapply f_eq_subdomain_antimon; [| eassumption ].
      eapply reach'_set_monotonic...

      eapply f_eq_subdomain_antimon; [| eassumption ].
      eapply reach'_set_monotonic...

      eapply res_equiv_rename_ext; eauto.

      eapply f_eq_subdomain_antimon; [| eassumption ].
      eapply reach'_set_monotonic...

      eapply f_eq_subdomain_antimon; [| eassumption ].
      eapply reach'_set_monotonic...

    - eapply heap_env_equiv_rename_ext; eauto.
  Qed.
  
  (* Lemma heap_approx_rename_ext S β1 β1' β2 β2' H1 H2 : *)
  (*   heap_approx S (β1, H1) (β2, H2) -> *)
  (*   f_eq_subdomain (reach' H1 S) β1 β1' -> *)
  (*   f_eq_subdomain (reach' H2 S) β2 β2' -> *)
  (*   heap_approx S (β1', H1) (β2', H2). *)
  (* Proof. *)
  (*   intros Hap1 Heq1 Heq2 l Hin. *)
  (*   edestruct Hap1 as [Heqb Hap1']; eauto. *)
  (*   split. rewrite <- Heq1, <- Heq2. eassumption.  *)
  (*   now eapply reach'_extensive. *)
  (*   now eapply reach'_extensive. *)
  (*   intros bl1 Hget1. *)
  (*   edestruct Hap1 as [Heqb' [bl2 [Hget2 Hbl]]]; eauto. *)
  (*   eexists; split; eauto. *)
    
  (*   eapply block_equiv_rename_ext; eauto. *)

  (*   eapply f_eq_subdomain_antimon; [| eassumption ]. *)
  (*   rewrite (reach_unfold H1 S). eapply Included_Union_preserv_r. *)
  (*   eapply reach'_set_monotonic. intros x Hin'. now repeat eexists; eauto. *)
    
  (*   eapply f_eq_subdomain_antimon; [| eassumption ]. *)
  (*   rewrite (reach_unfold H2 S). eapply Included_Union_preserv_r. *)
  (*   eapply reach'_set_monotonic. intros x Hin'. now repeat eexists; eauto. *)
  (* Qed.  *)

  
  (** Allocation lemmas *)
  
  Lemma heap_env_approx_alloc S S1 S2 β1 β2 H1 H2 H1' H2' rho1 rho2 l1 l2 b1 b2 x :
    closed S1 H1 -> closed S2 H2 ->
    env_locs rho1 (S \\ [set x]) \subset S1 ->
    env_locs rho2 (S \\ [set x]) \subset S2 ->
    locs b1 \subset S1 -> locs b2 \subset S2 ->
    S \\ [set x] |- (H1, rho1) ⩪_(β1, β2) (H2, rho2) ->
    alloc b1 H1 = (l1, H1') -> 
    alloc b2 H2 = (l2, H2') ->
    β1 l1 = β2 l2 ->
    block_equiv (β1, H1, b1) (β2, H2, b2) ->
    heap_env_approx S (β1, (H1', M.set x (Loc l1) rho1)) (β2, (H2', M.set x (Loc l2) rho2)).
  Proof with (now eauto with Ensembles_DB).
    intros Hc1 Hc2 Hsub1 Hsub2 Hin1 Hin2 Heq Ha1 Ha2 Hbeq Hb y v1 Hin Hget.
    destruct (peq x y); subst.
    - rewrite M.gss in Hget. inv Hget.
      eexists; split. rewrite M.gss. reflexivity.
      rewrite res_equiv_eq. simpl.
      erewrite gas; eauto. erewrite gas; eauto.
      simpl in Hb. destruct b1; destruct b2; try contradiction.
      + destruct Hb as [Heq' Hall]; subst.
        split; eauto. split; eauto.
        eapply Forall2_monotonic_strong; eauto.
        intros. 
        eapply res_equiv_weakening. exact Hc1. exact Hc2.
        eassumption.
        now eapply alloc_subheap; eauto.
        now eapply alloc_subheap; eauto.
        eapply Included_trans; [| eassumption ].
        eapply In_Union_list. now eapply in_map; eauto.
        eapply Included_trans; [| eassumption ].
        eapply In_Union_list. now eapply in_map; eauto.
      + destruct Hb as [Heq1 Heq2]; subst.
        split; eauto. split.
        eapply res_equiv_weakening. exact Hc1. exact Hc2.
        eassumption.
        now eapply alloc_subheap; eauto.
        now eapply alloc_subheap; eauto.
        eapply Included_trans; [| eassumption ]...
        eapply Included_trans; [| eassumption ]...
        eapply res_equiv_weakening. exact Hc1. exact Hc2.
        eassumption.
        now eapply alloc_subheap; eauto.
        now eapply alloc_subheap; eauto.
        eapply Included_trans; [| eassumption ]...
        eapply Included_trans; [| eassumption ]...
      + split; eauto. eapply heap_env_equiv_weaking'.
        exact Hc1. exact Hc2.
        eassumption. eassumption. eassumption.
        now eapply alloc_subheap; eauto.
        now eapply alloc_subheap; eauto.
    - rewrite M.gso in Hget; eauto.
      destruct Heq as [Heq1 Heq2].
      edestruct Heq1 as [v2 [Hget2 Hb']]; eauto.
      constructor; eauto. now intros Hc; inv Hc; eauto.
      eexists.
      rewrite M.gso; eauto. split; eauto.
      eapply res_equiv_weakening. exact Hc1. exact Hc2.
      eassumption.
      now eapply alloc_subheap; eauto.
      now eapply alloc_subheap; eauto.
      eapply Included_trans; [| now apply Hsub1 ].
      eapply get_In_env_locs; eauto.
      constructor; eauto. now intros Hc; inv Hc; eauto.
      eapply Included_trans; [| now apply Hsub2 ].
      eapply get_In_env_locs; eauto.
      constructor; eauto. now intros Hc; inv Hc; eauto.      
  Qed.
  
  Corollary heap_env_equiv_alloc S S1 S2 β1 β2 H1 H2 H1' H2' rho1 rho2 l1 l2 b1 b2 x :
    closed S1 H1 -> closed S2 H2 ->
    env_locs rho1 (S \\ [set x]) \subset S1 ->
    env_locs rho2 (S \\ [set x]) \subset S2 ->
    locs b1 \subset S1 -> locs b2 \subset S2 ->
    S \\ [set x] |- (H1, rho1) ⩪_(β1, β2) (H2, rho2) ->
    alloc b1 H1 = (l1, H1') -> 
    alloc b2 H2 = (l2, H2') ->
    β1 l1 = β2 l2 -> 
    block_equiv (β1, H1, b1) (β2, H2, b2) ->
    S |- (H1', M.set x (Loc l1) rho1) ⩪_(β1, β2) (H2', M.set x (Loc l2) rho2).
  Proof.
    intros. split. now eapply (heap_env_approx_alloc S S1 S2); eauto.
    eapply (heap_env_approx_alloc S S2 S1); eauto; symmetry; eassumption.
  Qed.
  
  Lemma heap_env_approx_alloc_alt S S1 S2 β1 β2 H1 H2 H1' H2' rho1 rho2 l1 l2 b1 b2 x :
    closed S1 H1 -> closed S2 H2 ->
    env_locs rho1 (S \\ [set x]) \subset S1 ->
    env_locs rho2 (S \\ [set x]) \subset S2 ->
    locs b1 \subset dom H1 ->
    locs b2 \subset dom H2 ->
    post H1 (locs b1) \subset S1 ->
    post H2 (locs b2) \subset S2 ->
    S \\ [set x] |- (H1, rho1) ⩪_(β1, β2) (H2, rho2) ->
    alloc b1 H1 = (l1, H1') -> 
    alloc b2 H2 = (l2, H2') ->
    β1 l1 = β2 l2 -> 
    block_equiv (β1, H1, b1) (β2, H2, b2) ->
    heap_env_approx S (β1, (H1', M.set x (Loc l1) rho1)) (β2, (H2', M.set x (Loc l2) rho2)) .
  Proof with (now eauto with Ensembles_DB).
    intros Hc1 Hc2 Hsub1 Hsub2 Hl1 Hl2 Hp1 Hp2 Heq Ha1 Ha2 Hbeq Hb y v1 Hin Hget.
    destruct (peq x y); subst.
    - rewrite M.gss in Hget. inv Hget.
      eexists; split. rewrite M.gss. reflexivity.
      rewrite res_equiv_eq. simpl.
      erewrite gas; eauto. erewrite gas; eauto.
      simpl in Hb. destruct b1; destruct b2; try contradiction.
      + destruct Hb as [Heq' Hall]; subst.
        split; eauto. split; eauto.
        eapply Forall2_monotonic_strong; eauto.
        intros. 
        eapply res_equiv_weakening_alt.
        * exact Hc1.
        * exact Hc2.
        * eassumption.
        * now eapply alloc_subheap; eauto.
        * now eapply alloc_subheap; eauto.
        * eapply Included_trans; [| eassumption ].
          eapply In_Union_list. eapply in_map. eassumption.
        * eapply Included_trans; [| eassumption ].
          eapply In_Union_list. eapply in_map. eassumption.
        * eapply Included_trans; [| eassumption ].
          eapply post_set_monotonic.
          eapply In_Union_list. eapply in_map. eassumption.
        * eapply Included_trans; [| eassumption ].
          eapply post_set_monotonic.
          eapply In_Union_list. eapply in_map. eassumption.
      + destruct Hb as [Hb1 Hb2]; subst.
        split; eauto. split; eauto.
        { eapply res_equiv_weakening_alt.
          * exact Hc1.
          * exact Hc2.
          * eassumption.
          * now eapply alloc_subheap; eauto.
          * now eapply alloc_subheap; eauto.
          * eapply Included_trans; [| eassumption ]...
          * eapply Included_trans; [| eassumption ]...
          * eapply Included_trans; [| eassumption ].
            eapply post_set_monotonic...
          * eapply Included_trans; [| eassumption ].
            eapply post_set_monotonic... }
        { eapply res_equiv_weakening_alt.
          * exact Hc1.
          * exact Hc2.
          * eassumption.
          * now eapply alloc_subheap; eauto.
          * now eapply alloc_subheap; eauto.
          * eapply Included_trans; [| eassumption ]...
          * eapply Included_trans; [| eassumption ]...
          * eapply Included_trans; [| eassumption ].
            eapply post_set_monotonic...
          * eapply Included_trans; [| eassumption ].
            eapply post_set_monotonic... }
      + simpl in *. split; eauto.
        eapply heap_env_equiv_weaking_alt; [ exact Hc1 | exact Hc2 | | | | | | |]; try eassumption.
        now eapply alloc_subheap; eauto.
        now eapply alloc_subheap; eauto.
    - rewrite M.gso in Hget; eauto.
      destruct Heq as [Heq1 Heq2].
      edestruct Heq1 as [v2 [Hget2 Hb']]; eauto.
      constructor; eauto. now intros Hc; inv Hc; eauto.
      eexists.
      rewrite M.gso; eauto. split; eauto.
      eapply res_equiv_weakening_alt.
      + exact Hc1.
      + exact Hc2.
      + eassumption.
      + now eapply alloc_subheap; eauto.
      + now eapply alloc_subheap; eauto.
      + eapply Included_trans; [| now eapply in_dom_closed; eauto ].
        eapply Included_trans; [| now apply Hsub1 ].
        eapply get_In_env_locs; [| eassumption ].
        constructor; eauto. now intros Hc; inv Hc; eauto.
      + eapply Included_trans; [| now eapply in_dom_closed; eauto ].
        eapply Included_trans; [| now apply Hsub2 ].
        eapply get_In_env_locs; [| eassumption ].
        constructor; eauto. now intros Hc; inv Hc; eauto.
      + eapply Included_trans; [| now eapply closed_reach_in_S; eauto ].
        eapply Included_trans; [| now eapply Included_post_reach'; eauto ].
        eapply post_set_monotonic.
        eapply Included_trans; [| now apply Hsub1 ].
        eapply get_In_env_locs; [| eassumption ].
        constructor; eauto. now intros Hc; inv Hc; eauto.
      + eapply Included_trans; [| now eapply closed_reach_in_S; eauto ].
        eapply Included_trans; [| now eapply Included_post_reach'; eauto ].
        eapply post_set_monotonic.
        eapply Included_trans; [| now apply Hsub2 ].
        eapply get_In_env_locs; [| eassumption ].
        constructor; eauto. now intros Hc; inv Hc; eauto.
  Qed.
  
  Corollary heap_env_equiv_alloc_alt S S1 S2 β1 β2 H1 H2 H1' H2' rho1 rho2 l1 l2 b1 b2 x :
    closed S1 H1 -> closed S2 H2 ->
    env_locs rho1 (S \\ [set x]) \subset S1 ->
    env_locs rho2 (S \\ [set x]) \subset S2 ->
    locs b1 \subset dom H1 ->
    locs b2 \subset dom H2 ->
    post H1 (locs b1) \subset S1 ->
    post H2 (locs b2) \subset S2 ->
    S \\ [set x] |- (H1, rho1) ⩪_(β1, β2) (H2, rho2) ->
    alloc b1 H1 = (l1, H1') -> 
    alloc b2 H2 = (l2, H2') ->
    β1 l1 = β2 l2 -> 
    block_equiv (β1, H1, b1) (β2, H2, b2) ->
    S |- (H1', M.set x (Loc l1) rho1) ⩪_(β1, β2) (H2', M.set x (Loc l2) rho2).
  Proof.
    intros. split. now eapply (heap_env_approx_alloc_alt S S1 S2); eauto.
    eapply (heap_env_approx_alloc_alt S S2 S1); eauto; symmetry; eassumption.
  Qed.

  Corollary heap_env_equiv_alloc_alt' S S1 S2 β1 β2 H1 H2 H1' H2' rho1 rho2 l1 l2 b1 b2 x :
    closed S1 H1 -> closed S2 H2 ->
    env_locs rho1 S \subset S1 ->
    env_locs rho2 S \subset S2 ->
    locs b1 \subset dom H1 ->
    locs b2 \subset dom H2 ->
    post H1 (locs b1) \subset S1 ->
    post H2 (locs b2) \subset S2 ->
    S |- (H1, rho1) ⩪_(β1, β2) (H2, rho2) ->
    alloc b1 H1 = (l1, H1') -> 
    alloc b2 H2 = (l2, H2') ->
    β1 l1 = β2 l2 -> 
    block_equiv (β1, H1, b1) (β2, H2, b2) ->
    x |: S |- (H1', M.set x (Loc l1) rho1) ⩪_(β1, β2) (H2', M.set x (Loc l2) rho2).
  Proof with (now eauto with Ensembles_DB).
    intros Hc1 Hc2 Hs1 Hs2 Hl1 Hl2 Hp1 Hp2 He Ha1 Ha2 Heq Hbeq.
    eapply heap_env_equiv_alloc_alt with (H1 := H1) (H2 := H2); try eassumption.
    eapply Included_trans; [|  eapply Hs1 ].
    rewrite Setminus_Union_distr. eapply env_locs_monotonic...
    eapply Included_trans; [|  eapply Hs2 ].
    rewrite Setminus_Union_distr. eapply env_locs_monotonic...

    eapply heap_env_equiv_antimon. eassumption. 
    rewrite Setminus_Union_distr...
  Qed. 

  Lemma heap_env_equiv_set_lists S β1 β2 H1 H2 xs ls1 ls2 rho1 rho2 rho1' rho2' :
    Setminus _ S (FromList xs) |- (H1, rho1) ⩪_(β1, β2) (H2, rho2) ->
    set_lists xs ls1 rho1 = Some rho1' -> set_lists xs ls2 rho2 = Some rho2' ->
    Forall2 (fun l1 l2 => (l1, H1) ≈_(β1, β2) (l2, H2)) ls1 ls2  ->
    S |- (H1, rho1') ⩪_(β1, β2) (H2, rho2').
  Proof with (now eauto with Ensembles_DB).
    revert S rho1' rho2' ls1 ls2; induction xs;
    intros S  rho1' rho2' ls1 ls2 Heq Hs1 Hs2 Hall.
    - destruct ls1; destruct ls2; try discriminate. inv Hs1; inv Hs2; eauto.
      rewrite FromList_nil, Setminus_Empty_set_neut_r in Heq. eassumption.
    - destruct ls1; destruct ls2; try discriminate.
      inv Hall. simpl in Hs1, Hs2.
      destruct (set_lists xs ls1 rho1) eqn:Hset1; try discriminate.
      destruct (set_lists xs ls2 rho2) eqn:Hset2; try discriminate.
      inv Hs1; inv Hs2. eapply heap_env_equiv_set; eauto.
      eapply IHxs; eauto. eapply heap_env_equiv_antimon; eauto.
      rewrite FromList_cons...
  Qed.

  Lemma reach'_alloc_set_alt (S : Ensemble var) (H H' : heap block) (rho : env)
        (x : var) (b : block) (l : loc) :
    locs b \subset reach' H (env_locs rho (S \\ [set x]))->
    alloc b H = (l, H')  ->  
    reach' H' (env_locs (M.set x (Loc l) rho) S) \subset
     l |: reach' H (env_locs rho (S \\ [set x])).
  Proof.
    intros Hsub Hal.
    eapply Included_trans. eapply reach'_set_monotonic.
    eapply env_locs_monotonic. eapply Included_Union_Setminus with (s2 := [set x]).
    now eauto with typeclass_instances.
    eapply reach'_alloc_set; eauto.
  Qed.      


  (* Lemma def_closures_post_reach_alt *)
  (*       (S : Ensemble var) (H H' : heap block) (rho rho' : env) *)
  (*       (B B0 : fundefs) (l : loc) : *)
  (*   def_closures B B0 rho H l = (H', rho') -> *)
  (*   post H [set l] \subset (reach' H (env_locs rho (S \\ (name_in_fundefs B)))) -> *)
  (*   post H' [set l] \subset (reach' H' (env_locs rho' S)). *)
  (* Proof. *)
  (*   revert S rho rho' H H'; induction B; intros S rho rho' H H' Hdef Hsub; simpl. *)
  (*   - simpl in Hdef. *)
  (*     destruct (def_closures B B0 rho H l) as [H'' rho''] eqn:Hdef'. *)
  (*     destruct (alloc _ H'') as [l' H'''] eqn:Hal. inv Hdef. *)
  (*     simpl in Hsub. rewrite <- Setminus_Union in Hsub. *)
  (*     eapply IHB in Hsub; eauto. *)
  (*     intros l1 [l2 [b2 [Hin1 [Hget2 Hin2]]]]. inv Hin1.  *)
  (*     exists 2. split. constructor. *)
  (*     exists l2. eexists. split. simpl. *)
  (*     eexists l'. eexists. split. simpl. *)

  (*     eexists v. split. right. left. reflexivity. *)
  (*     rewrite M.gss. reflexivity. *)
  (*     split. eapply gas; eassumption. *)
  (*     simpl. right. reflexivity. *)
  (*     split; eauto. *)
  (*   - rewrite Union_Empty_set_neut_r. inv Hdef. *)
  (*     eassumption. *)
  (* Qed. *)

  Lemma env_locs_set_superset S rho x v :
    env_locs rho (S \\ [set x]) \subset env_locs (M.set x v rho) S.
  Proof.
    intros l1 [x1 [Hin Hin']].
    destruct (M.get x1 rho) as [v1 |] eqn:Hget1; try now inv Hin'.
    inv Hin. eexists x1.  split; eauto.
    rewrite M.gso. rewrite Hget1. eassumption.
    intros Hc. subst. eauto.
  Qed.
  
  Lemma def_closures_env_locs_subset S H rho H' rho' B B0 l :
    def_closures B B0 rho H l = (H', rho') ->
    env_locs rho (S \\ name_in_fundefs B) \subset env_locs rho' S.
  Proof.
    revert S rho rho' H H'; induction B; intros S rho rho' H H' Hdef.
    - simpl in Hdef. destruct (def_closures B B0 rho H l) as [H'' rho''] eqn:Heqd.
      destruct (alloc (Clos (FunPtr B0 v) l) H'') as [l' H'''] eqn:Heqa.
      inv Hdef. 
      eapply Included_trans.
      simpl. rewrite <- Setminus_Union. eapply IHB.
      eassumption. eapply env_locs_set_superset.
    - rewrite Setminus_Empty_set_neut_r. inv Hdef. reflexivity.
  Qed.
  

  Lemma res_equiv_get_Constr β1 β2 (H1 H2 : heap block)
        (l1 l2 : loc) (c : ctor_tag) (vs1 : list value) :
    (Loc l1, H1) ≈_(β1, β2) (Loc l2, H2) ->
    get l1 H1 = Some (Constr c vs1) ->
    exists vs2,
      get l2 H2 = Some (Constr c vs2) /\
      Forall2 (fun v1 v2 => (v1, H1) ≈_(β1, β2) (v2, H2)) vs1 vs2.
  Proof.
    intros Hres Hget.
    rewrite res_equiv_eq in Hres. simpl in Hres. rewrite Hget in Hres.
    destruct Hres as [Hbeq Hres']. destruct (get l2 H2); try contradiction.
    destruct b; try contradiction. 
    destruct Hres' as [Heq Hb]. subst. eexists; split; eauto. 
  Qed.
  
  Lemma heap_env_equiv_env_get (S : Ensemble var) β1 β2 (H1 H2 : heap block)
        (rho1 rho2 : env) (x : var) (l : value) :
    M.get x rho1 = Some l ->
    S |- (H1, rho1) ⩪_(β1, β2) (H2, rho2) ->
    x \in S ->
    exists l',
      M.get x rho2 = Some l' /\
      (l, H1) ≈_(β1, β2) (l', H2).
  Proof.
    intros Hget Heq Hin.
    eapply Heq in Hget; eassumption.
  Qed.
  
  Lemma heap_env_equiv_env_get_list (S : Ensemble var) β1 β2 (H1 H2 : heap block)
        (rho1 rho2 : env) (xs : list var) (ls : list value) :
    get_list xs rho1 = Some ls ->
    S |- (H1, rho1) ⩪_(β1, β2) (H2, rho2) ->
    (FromList xs) \subset S ->
    exists ls',
      get_list xs rho2 = Some ls' /\
      Forall2 (fun l l' => (l, H1) ≈_(β1, β2) (l', H2)) ls ls'.
  Proof with now eauto with Ensembles_DB.
    revert ls; induction xs; intros ls Hget Heq Hin.
    - inv Hget.
      eexists; split; eauto. reflexivity.
    - simpl in Hget.
      destruct (M.get a rho1) as [l1 | ] eqn:Hgetl1; try discriminate.
      destruct (get_list xs rho1) as [ls1 | ] eqn:Hetls1; try discriminate.
      inv Hget.
      edestruct heap_env_equiv_env_get as [l2 [Hgetl2 Heq']]; eauto.
      eapply Hin. rewrite FromList_cons...
      edestruct IHxs as [ls2 [Hgetls2 Hall2]]; eauto.
      eapply Included_trans; try eassumption. 
      rewrite FromList_cons...
      eexists; split. simpl. rewrite Hgetl2, Hgetls2.
      reflexivity. constructor; eauto.
  Qed.
  

  Lemma heap_env_equiv_get_list_Forall2 S β1 β2 H1 H2 ys vs1 vs2 rho1 rho2 :
    S |- (H1, rho1) ⩪_(β1, β2) (H2, rho2) ->
    FromList ys \subset S ->
    get_list ys rho1 = Some vs1 ->
    get_list ys rho2 = Some vs2 ->
    Forall2 (fun l1 l2 => (l1, H1) ≈_(β1, β2) (l2, H2)) vs1 vs2.
  Proof.
    revert vs1 vs2; induction ys; intros vs1 vs2 Heq Hin Hg1 Hg2;
    destruct vs1; destruct vs2; simpl in *; try discriminate; try now constructor.
    - destruct (M.get a rho1) eqn:Heqa;
      destruct (get_list ys rho1) eqn:Heqys; try discriminate.
    - destruct (M.get a rho2) eqn:Heqa;
      destruct (get_list ys rho2) eqn:Heqys; try discriminate.
    - rewrite FromList_cons in Hin.
      destruct (M.get a rho1) eqn:Heqa;
        destruct (get_list ys rho1) eqn:Heqys; try discriminate. inv Hg1.
      eapply Heq in Heqa. destruct Heqa as [l' [Hget Heq']].
      rewrite Hget in Hg2.
      destruct (get_list ys rho2) eqn:Heqys'; try discriminate. inv Hg2.
      constructor; eauto. eapply IHys; eauto.
      eapply Included_trans; now eauto with Ensembles_DB.
      eapply Included_trans; now eauto with Ensembles_DB.
  Qed.
  
  Lemma block_equiv_Constr β1 β2 (H1 H2 : heap block) (c : ctor_tag) (vs vs' : list value) :
    Forall2 (fun l1 l2 => (l1, H1) ≈_(β1, β2) (l2, H2)) vs vs' ->
    block_equiv (β1, H1, Constr c vs) (β2, H2, Constr c vs').
  Proof.
    simpl; split; eauto.
  Qed.

  Lemma block_equiv_Constr_r β1 β2 (H1 H2 : heap block) (c1 c2 : ctor_tag)
        (vs vs' : list value) :
    block_equiv (β1, H1, Constr c1 vs) (β2, H2, Constr c2 vs') ->
    Forall2 (fun l1 l2 => (l1, H1) ≈_(β1, β2) (l2, H2)) vs vs'.
  Proof.
    intros [Heq Hall]; eauto.
  Qed.
  


  
  Lemma block_equiv_Fun β1 β2 (H1 H2 : heap block) (rho1 rho2 : env) :
    Full_set _ |- (H1, rho1) ⩪_(β1, β2) (H2, rho2) ->
    block_equiv (β1, H1, Env rho1) (β2, H2, Env rho2).
  Proof.
    simpl; eauto.
  Qed.
  
  (** * Image lemmas *)

  Close Scope Z_scope.


  Lemma res_approx_image_post (n : nat) (β1 β2 : loc -> loc)
        (H1 H2 : heap block)
        (v1 v2 : value) :
    res_approx_fuel' n (β1, (v1, H1)) (β2, (v2, H2)) ->
    image β1 ((post H1 ^ n) (val_loc v1)) \subset image β2 ((post H2 ^ n) (val_loc v2)).
  Proof.
    revert v1 v2 H1 H2. induction n as [n IHn] using lt_wf_rec1; intros v1 v2 H1 H2 Hres.
    destruct v1 as [l1 | B1 f1]; destruct v2 as [l2 | B2 f2]; try now firstorder.
    - simpl in Hres.
      destruct (get l1 H1) as [b1 |] eqn:Hget1; eauto.
      destruct b1 as [c1 vs1 | v1 v2 | rho1 ].
      + destruct Hres as [Hbs1 [vs2 [Hget2 Hi]]].
        destruct n.
        * simpl. rewrite !image_Singleton.
          rewrite Hbs1. reflexivity.
        * replace (S n) with (n + 1) by omega.
          rewrite !app_plus. unfold compose. simpl.
          rewrite (proper_post_n H1);
            [| rewrite !post_Singleton; try eassumption; reflexivity ].
          rewrite (proper_post_n H2);
            [| rewrite !post_Singleton; try eassumption; reflexivity ].
          specialize (Hi n (Nat.lt_succ_diag_r n)).
          clear Hget1 Hget2. induction Hi; simpl.
          rewrite !post_n_Empty_set. rewrite !image_Empty_set. reflexivity.
          rewrite !post_n_Union, !image_Union.
          eapply Included_Union_compat. eapply IHn. omega.
          rewrite <- res_approx_fuel_eq. eassumption.
          eapply IHHi; eauto. 
      + destruct Hres as [Hbs1 [v1' [v2' [Hget2 Hi]]]].
        destruct n.
        * simpl. rewrite !image_Singleton.
          rewrite Hbs1. reflexivity.
        * replace (S n) with (n + 1) by omega.
          rewrite !app_plus. unfold compose. simpl.
          rewrite (proper_post_n H1);
            [| rewrite !post_Singleton; try eassumption; reflexivity ].
          rewrite (proper_post_n H2);
            [| rewrite !post_Singleton; try eassumption; reflexivity ].
          simpl. rewrite !post_n_Union, !image_Union.
          eapply Included_Union_compat.
          eapply IHn. omega.
          rewrite <- res_approx_fuel_eq. eapply Hi. omega.
          eapply IHn. omega.
          rewrite <- res_approx_fuel_eq. eapply Hi. omega.
      + destruct Hres as [Hbs1 [rho [Hgetr Hx]]].
        destruct n.
        * simpl. rewrite !image_Singleton.
          rewrite Hbs1. reflexivity.
        * replace (S n) with (n + 1) by omega.
          rewrite !app_plus. unfold compose. simpl.
          rewrite (proper_post_n H1);
            [| rewrite !post_Singleton; try eassumption; reflexivity ].
          rewrite (proper_post_n H2);
            [| rewrite !post_Singleton; try eassumption; reflexivity ].
          simpl.
          { clear Hget1 Hgetr.
            assert (Hlem : forall S1 S2,
                             (forall l1, l1 \in S1 ->
                                           exists l2, l2 \in S2 /\ res_approx_fuel n (β1, (Loc l1, H1)) (β2, (Loc l2, H2))) ->
                             (forall l2, l2 \in S2 ->
                                           exists l1, l1 \in S1 /\ res_approx_fuel n (β1, (Loc l1, H1)) (β2, (Loc l2, H2))) ->
                             image β1 ((post H1 ^ n) S1) \subset image β2 ((post H2 ^ n) S2)
                   ).
            { clear -IHn. intros S1 S2 HS1 HS2.
              intros l2' [l1' [Hin Hbeq]]. edestruct post_n_exists_Singleton as [l1 [Hinl1 Hpost1]]; eauto.
              edestruct HS1 as [l2 [Hinl2 Hres]]; eauto.
              eapply image_monotonic. eapply post_n_set_monotonic with (S1 := [set l2]). eapply Singleton_Included.
              eassumption.
              rewrite res_approx_fuel_eq in Hres.
              specialize (IHn n (Nat.lt_succ_diag_r n) _ _ _ _ Hres).
              eapply IHn. eexists; split; eauto. }
            eapply Hlem.
            - intros l3 [z [_ Hin]].
              destruct (M.get z rho1) as [v1 | ] eqn:Hgetz; [| now inv Hin ].
              destruct v1 as [l1' |]; try now inv Hin. inv Hin.
              destruct (Hx z) as [ [v1' [v2' [Hget1 [Hget2 Hi' ]]]] | [Hn1 Hn2] ]; [| congruence ].
              subst_exp. specialize (Hi' n (Nat.lt_succ_diag_r n)).
              rewrite res_approx_fuel_eq in Hi'.
              destruct v2' as [l4 |]; try contradiction. eexists. split.
              eexists. split. now constructor. rewrite Hget2. reflexivity.
              rewrite res_approx_fuel_eq. eassumption.
            - intros l3 [z [_ Hin]].
              destruct (M.get z rho) as [v1 | ] eqn:Hgetz; [| now inv Hin ].
              destruct v1 as [l1' |]; try now inv Hin. inv Hin.
              destruct (Hx z) as [ [v1' [v2' [Hget1 [Hget2 Hi' ]]]] | [Hn1 Hn2] ]; [| congruence ].
              subst_exp. specialize (Hi' n (Nat.lt_succ_diag_r n)).
              rewrite res_approx_fuel_eq in Hi'.
              destruct v1' as [l4 |]; try contradiction. eexists. split.
              eexists. split. now constructor. rewrite Hget1. reflexivity.
              rewrite res_approx_fuel_eq. eassumption.
          }
      + simpl. destruct Hres as [Heqb _].
        destruct n.
        * simpl. rewrite !image_Singleton, Heqb. reflexivity.
        * rewrite post_n_Singleton_None; eauto.
          rewrite image_Empty_set. now eauto with Ensembles_DB.
    - simpl. rewrite !post_n_Empty_set, !image_Empty_set. reflexivity.
  Qed.
  
  Lemma res_equiv_image_reach (β1 β2 : loc -> loc)
        (H1 H2 : heap block)
        (v1 v2 : value) :
    res_equiv (β1, (v1, H1)) (β2, (v2, H2)) ->
    image β1 (reach' H1 (val_loc v1)) <--> image β2 (reach' H2 (val_loc v2)).
  Proof.
    intros Heq. split.
    - intros l' [l [[n [_ Hr]] Hin]].
      destruct (Heq n) as [Heq1 Heq2].
      rewrite res_approx_fuel_eq in *. eapply res_approx_image_post in Heq1.
      edestruct Heq1 as [l1 [Hp1 Hin1]].
      eexists; split; eauto.
      eexists; split; eauto. eexists; split. now constructor. 
      eassumption.
    - intros l' [l [[n [_ Hr]] Hin]].
      destruct (Heq n) as [Heq1 Heq2].
      rewrite res_approx_fuel_eq in *. eapply res_approx_image_post in Heq2.
      edestruct Heq2 as [l1 [Hp1 Hin1]].
      eexists; split; eauto.
      eexists; split; eauto. eexists; split. now constructor. 
      eassumption.
  Qed.

  Lemma res_equiv_image_reach_n (n : nat) (β1 β2 : loc -> loc)
        (H1 H2 : heap block)
        (v1 v2 : value) :
    res_equiv (β1, (v1, H1)) (β2, (v2, H2)) ->
    image β1 (reach_n H1 n (val_loc v1)) <--> image β2 (reach_n H2 n (val_loc v2)).
  Proof.
    intros Heq. split.
    - intros l' [l [[m [Hm Hr]] Hin]].
      destruct (Heq m) as [Heq1 Heq2].
      rewrite res_approx_fuel_eq in *.
      eapply res_approx_image_post in Heq1.
      edestruct Heq1 as [l1 [Hp1 Hin1]].
      eexists; split; eauto.
      eexists; split; eauto. eexists; split; eauto.
    - intros l' [l [[m [Hm Hr]] Hin]].
      destruct (Heq m) as [Heq1 Heq2].
      rewrite res_approx_fuel_eq in *. eapply res_approx_image_post in Heq2.
      edestruct Heq2 as [l1 [Hp1 Hin1]].
      eexists; split; eauto.
      eexists; split; eauto. eexists; split; eauto.
  Qed.

  Lemma res_equiv_image_post (β1 β2 : loc -> loc)
        (i : nat) (H1 H2 : heap block)
        (v1 v2 : value) :
    res_equiv (β1, (v1, H1)) (β2, (v2, H2)) ->
    image β1 ((post H1 ^ i) (val_loc v1)) <--> image β2 ((post H2 ^ i) (val_loc v2)).
  Proof.
    intros [Heq1 Heq2]. rewrite res_approx_fuel_eq in *. split; eapply res_approx_image_post; eauto.
  Qed.

  
  Lemma heap_env_equiv_image_reach (S : Ensemble var) (β1 β2 : loc -> loc)
        (H1 H2 : heap block)
        (rho1 rho2 : env) :
    S |- (H1, rho1) ⩪_( β1, β2) (H2, rho2) ->
    image β1 (reach' H1 (env_locs rho1 S)) <--> image β2 (reach' H2 (env_locs rho2 S)).
  Proof.
    intros Heq. split.
    - intros l1 [l2 [[n [_ Him1]] Heq']]. 
      edestruct post_n_exists_Singleton as [l [Hin Hpost]]; [ eassumption |].
      destruct Hin as [x [Hin Hget]].
      destruct (M.get x rho1) as [[l1'|] |] eqn:Hget1; try now inv Hget.
      inv Hget. 
      edestruct heap_env_equiv_env_get as [v2 [Hget2 Heqv]]; try eassumption. 
      destruct v2 as [l2' |].
      + eapply res_equiv_image_post with (i := n) in Heqv. try contradiction.
        assert (Him : (image β1 ((post H1 ^ n) (val_loc (Loc l)))) (β1 l2)).
        { eexists; split; eauto. }
        eapply Heqv in Him. edestruct Him as [l3 [Hp Heq'']].
        eexists; split; eauto.
        eexists; split; eauto. now constructor.
        eapply post_n_set_monotonic; [| eassumption ].
        eapply Singleton_Included. eexists; split; eauto. rewrite Hget2.
        reflexivity. 
      + rewrite res_equiv_eq in Heqv. contradiction.
    - intros l1 [l2 [[n [_ Him1]] Heq']]. 
      edestruct post_n_exists_Singleton as [l [Hin Hpost]]; [ eassumption |].
      destruct Hin as [x [Hin Hget]].
      destruct (M.get x rho2) as [[l1'|] |] eqn:Hget1; try now inv Hget.
      inv Hget. 
      edestruct heap_env_equiv_env_get as [v2 [Hget2 Heqv]];
        try (symmetry; eassumption); try eassumption.
      edestruct v2 as [l2' |].
      + eapply res_equiv_image_post with (i := n) in Heqv. try contradiction.
        assert (Him : (image β2 ((post H2 ^ n) (val_loc (Loc l)))) (β2 l2)).
        { eexists; split; eauto. }
        eapply Heqv in Him. edestruct Him as [l3 [Hp Heq'']].
        eexists; split; eauto.
        eexists; split; eauto. now constructor.
        eapply post_n_set_monotonic; [| eassumption ].
        eapply Singleton_Included. eexists; split; eauto. rewrite Hget2.
        reflexivity. 
      + rewrite res_equiv_eq in Heqv. contradiction.
  Qed.

    Lemma heap_env_equiv_image_post_n (S : Ensemble var) (β1 β2 : loc -> loc)
        (H1 H2 : heap block)
        (rho1 rho2 : env) (n :nat) :
    S |- (H1, rho1) ⩪_( β1, β2) (H2, rho2) ->
    image β1 ((post H1 ^ n) (env_locs rho1 S)) <-->
    image β2 ((post H2 ^ n) (env_locs rho2 S)).
  Proof.
    intros Heq. split.
    - intros l1 [l2 [Him Heq']]. 
      edestruct post_n_exists_Singleton as [l [Hin Hpost]]; [ eassumption |].
      destruct Hin as [x [Hin Hget]].
      destruct (M.get x rho1) as [[l1'|] |] eqn:Hget1; try now inv Hget.
      inv Hget. 
      edestruct heap_env_equiv_env_get as [v2 [Hget2 Heqv]]; try eassumption. 
      destruct v2 as [l2' |].
      + eapply res_equiv_image_post with (i := n) in Heqv. try contradiction.
        assert (Him' : (image β1 ((post H1 ^ n) (val_loc (Loc l)))) (β1 l2)).
        { eexists; split; eauto. }
        eapply Heqv in Him'. edestruct Him' as [l3 [Hp Heq'']].
        eexists; split; eauto.
        eapply post_n_set_monotonic; [| eassumption ].
        eapply Singleton_Included. eexists; split; eauto. rewrite Hget2.
        reflexivity. 
      + rewrite res_equiv_eq in Heqv. contradiction.
    - intros l1 [l2 [Him1 Heq']]. 
      edestruct post_n_exists_Singleton as [l [Hin Hpost]]; [ eassumption |].
      destruct Hin as [x [Hin Hget]].
      destruct (M.get x rho2) as [[l1'|] |] eqn:Hget1; try now inv Hget.
      inv Hget. 
      edestruct heap_env_equiv_env_get as [v2 [Hget2 Heqv]];
        try (symmetry; eassumption); try eassumption.
      edestruct v2 as [l2' |].
      + eapply res_equiv_image_post with (i := n) in Heqv. try contradiction.
        assert (Him : (image β2 ((post H2 ^ n) (val_loc (Loc l)))) (β2 l2)).
        { eexists; split; eauto. }
        eapply Heqv in Him. edestruct Him as [l3 [Hp Heq'']].
        eexists; split; eauto.
        eapply post_n_set_monotonic; [| eassumption ].
        eapply Singleton_Included. eexists; split; eauto. rewrite Hget2.
        reflexivity. 
      + rewrite res_equiv_eq in Heqv. contradiction.
  Qed.

    Lemma heap_env_equiv_image_root (S : Ensemble var) (β1 β2 : loc -> loc)
        (H1 H2 : heap block) (rho1 rho2 : env) :
    S |- (H1, rho1) ⩪_( β1, β2) (H2, rho2) ->
    image β1 (env_locs rho1 S) <--> image β2 (env_locs rho2 S).
  Proof.     
    intros Heq. split.
    - intros l1 [l2 [[x [Hin1 Hin2]] Heq']]. 
      destruct (M.get x rho1) as [[ l1' |] |] eqn:Hget1; try now inv Hin2.
      inv Hin2.
      edestruct heap_env_equiv_env_get as [v2 [Hget2 Heqv]]; try eassumption. 
      rewrite res_equiv_eq in Heqv. destruct v2 as [l2' |]; try contradiction.
      destruct Heqv as [Heq1 _]. rewrite Heq1.
      eexists; split; eauto.
      eexists; split; eauto. rewrite Hget2; reflexivity.
    - intros l1 [l2 [[x [Hin1 Hin2]] Heq']]. 
      destruct (M.get x rho2) as [[ l1' |] |] eqn:Hget1; try now inv Hin2.
      inv Hin2.
      edestruct heap_env_equiv_env_get as [v2 [Hget2 Heqv]]; try eassumption.
      symmetry. eassumption.
      rewrite res_equiv_eq in Heqv. destruct v2 as [l2' |]; try contradiction.
      destruct Heqv as [Heq1 _]. rewrite Heq1.
      eexists; split; eauto.
      eexists; split; eauto. rewrite Hget2; reflexivity.
  Qed.


  Lemma heap_env_approx_heap_equiv (S : Ensemble var) (H1 H2 : heap block)
        (b2 : loc -> loc) (rho1 rho2 : env) :
    S |- (H1, rho1) ⩪_(id, b2) (H2, rho2) ->
    env_locs rho2 S |- H1 ≃_(id, b2) H2.
  Proof.
    intros Heq x [z [Hin Hget]].
    destruct (M.get z rho2) as [[l | ]|] eqn:Hgetz; try contradiction.
    destruct Heq as [Heq1 Heq2].
    edestruct Heq2 as [l' [Hget' Hres]]; try eassumption.
    inv Hget. 
    symmetry. assert (Hres' := Hres).
    rewrite res_equiv_eq in Hres. destruct l'; try contradiction.
    destruct Hres as [Heqbs _]. unfold id in *. subst.
    eassumption.
  Qed.

  Lemma heap_env_approx_heap_equiv_r (S : Ensemble var) (H1 H2 : heap block)
        (b2 : loc -> loc) (rho1 rho2 : env) :
    S |- (H1, rho1) ⩪_(b2, id) (H2, rho2) ->
    env_locs rho1 S |- H1 ≃_(b2, id) H2.
  Proof.
    intros Heq x [z [Hin Hget]].
    destruct (M.get z rho1) as [[l | ]|] eqn:Hgetz; try contradiction.
    destruct Heq as [Heq1 Heq2].
    edestruct Heq1 as [l' [Hget' Hres]]; try eassumption.
    inv Hget. 
    symmetry. assert (Hres' := Hres).
    rewrite res_equiv_eq in Hres. destruct l'; try contradiction.
    destruct Hres as [Heqbs _]. unfold id in *. subst.
    symmetry. eassumption.
  Qed.

  Lemma heap_equiv_post_n (S : Ensemble var) (H1 H2  : heap block)
        (b1  : loc -> loc) n :
    S |- H1 ≃_(b1, id) H2 ->
    (post H1 ^ n) S |- H1 ≃_(b1, id) H2.
  Proof.
    revert S; induction n; intros S Heq.
    - eassumption.
    - replace ((post H1 ^ Datatypes.S n) S)
      with ((post H1 ^ n) (post H1 S)).

      { eapply IHn.
        intros l [l' [b' [Hin [Hgetl Hinl]]]].
        assert (Hin' := Hin). eapply Heq in Hin'.
        rewrite res_equiv_eq in Hin'.
        destruct Hin' as  [Hb Hres]. unfold id in *; subst.
        rewrite Hgetl in Hres.
        destruct (get (b1 l') H2) as [b |] eqn:Hetb; try contradiction.
        destruct b' as [c vs | | rho ];
          destruct b as [c' vs' | | rho' ]; try contradiction.
        
        simpl in Hres. destruct Hres as [Heqc Hall].
        simpl in Hinl.
        edestruct (@Union_lists_exists loc) as [S' [Hin3 Hin2]]. eassumption.
        edestruct (list_in_map_inv _ _ _ Hin3) as [l3' [Heql Hinl']]; subst.
        destruct l3' as [l3' |]; inv Hin2.
        edestruct (Forall2_exists _ vs vs' (Loc l) Hinl' Hall)
          as [x' [Hin2 Hres']].
        assert (Hres := Hres').
        rewrite res_equiv_eq  in Hres'.
        destruct x'; try contradiction. destruct Hres' as [Heq' _].
        subst. eassumption.
        
        destruct Hres as [Hres1 Hres2]. inv Hinl.
        destruct v; try contradiction. inv H. 
        assert (Hres1' := Hres1). 
        rewrite res_equiv_eq in Hres1. destruct v1; try contradiction.
        simpl in Hres1. destruct Hres1 as [Heq' _].
        subst. eassumption.

        destruct v0; try contradiction. inv H. 
        assert (Hres2' := Hres2). 
        rewrite res_equiv_eq in Hres2. destruct v2; try contradiction.
        simpl in Hres2. destruct Hres2 as [Heq' _].
        subst. eassumption.

        eapply heap_env_approx_heap_equiv_r. 
        eassumption. eassumption. }
      replace (Datatypes.S n) with (n + 1) by omega.
      rewrite app_plus. reflexivity.
  Qed.

   Lemma heap_equiv_reach (S : Ensemble var) (H1 H2  : heap block)
        (b1  : loc -> loc)  :
    S |- H1 ≃_(b1, id) H2 ->
    reach' H1 S |- H1 ≃_(b1, id) H2.
  Proof.
    intros Heq x  [ n [Heq' Hin]]. 
    eapply heap_equiv_post_n.  eassumption.
    eassumption.
  Qed.

  Lemma heap_equiv_symm (S : Ensemble var) (H1 H2 : heap block)
         (b d : loc -> loc)  :
    S |- H1 ≃_(b, d) H2 ->
    S |- H2 ≃_(d, b) H1.
  Proof.
    intros Heq x Hin.
    subst. symmetry. eauto.
  Qed.


  Lemma heap_equiv_post_n_r (S : Ensemble var) (H1 H2  : heap block)
        (b1  : loc -> loc) n :
    S |- H1 ≃_(id, b1) H2 ->
    (post H2 ^ n) S |- H1 ≃_(id, b1) H2.
  Proof.
    intros Heq. eapply heap_equiv_symm. eapply heap_equiv_post_n.
    eapply heap_equiv_symm. eassumption.
  Qed. 

  

   Lemma heap_equiv_reach_r (S : Ensemble var) (H1 H2  : heap block)
        (b1  : loc -> loc)  :
    S |- H1 ≃_(id, b1) H2 ->
    reach' H2 S |- H1 ≃_(id, b1) H2.
  Proof.
    intros Heq x  [ n [Heq' Hin]]. 
    eapply heap_equiv_post_n_r.  eassumption.
    eassumption.
  Qed.

  Lemma heap_equiv_compose_r (S : Ensemble var) (H1 H2 H3 : heap block)
        (b1 b2 : loc -> loc) :
    image b2 S |- H1 ≃_(id, b1) H2 ->
    S |- H2 ≃_(id, b2) H3 ->
    S |- H1 ≃_(id, b1 ∘ b2) H3.
  Proof.
    intros Heq1 Heq2 x Hin.
    unfold compose at 1. eapply Equivalence_Transitive.
    eapply Heq1. eexists. split; eauto.
    unfold id. eapply res_equiv_f_compose with (β4 := id).
    rewrite compose_id_neut_r. reflexivity.
    eapply Heq2. eassumption.
  Qed.

  Lemma heap_equiv_post_n_eq S H1 H2 b1 n :
    S |- H1 ≃_(b1, id) H2 ->
    (image b1 ((post H1 ^ n) S)) <--> (post H2 ^ n) (image b1 S).
  Proof.
    intros Heq; split.
    - intros x [y [Hbeq Hin]]. subst.
      edestruct post_n_exists_Singleton as [l [Hin1 Hin2]].
      eassumption. assert (Hin1' := Hin1). eapply Heq in Hin1.
      eapply res_equiv_image_post with (i := n) in Hin1.
      rewrite image_id in Hin1.
      eapply post_n_set_monotonic; [| eapply Hin1 ].
      eapply Singleton_Included. eexists; split; eauto.
      eexists; split; eauto.
    - intros x Hin. subst.
      edestruct post_n_exists_Singleton as [l [Hin1 Hin2]].
      eassumption. assert (Hin1' := Hin1).
      destruct Hin1' as [y [Hbeq Hiny]]. subst.
      assert (Hin2' := Hbeq). eapply Heq in Hbeq.
      eapply res_equiv_image_post with (i := n) in Hbeq.
      rewrite image_id in Hbeq. eapply Hbeq in Hin2.
      unfold id in *.
      eapply image_monotonic; [| eassumption ].
      eapply post_n_set_monotonic. eapply Singleton_Included.
      eassumption.
  Qed. 

  Lemma heap_equiv_reach_eq S H1 H2 b1 :
    S |- H1 ≃_(b1, id) H2 ->
    (image b1 (reach' H1 S)) <--> reach' H2 (image b1 S).
  Proof.
    intros Hq. split.
    intros  x [y [[n [_ HP]] Hn]]. subst.
    eexists; split; eauto. now constructor.
    eapply heap_equiv_post_n_eq. eassumption.
    eexists; split; eauto; eassumption.

    intros x [n [_ HP]]. subst.
    eapply heap_equiv_post_n_eq in HP.
    eapply image_monotonic; [| eassumption ].
    intros y Hin. eexists; split; eauto.
    constructor. eassumption.
  Qed. 
    
  
  Lemma val_loc_in_dom β1 β2 (H1 H2 : heap block) (v1 v2 : value) :
    (v1, H1) ≈_(β1, β2) (v2, H2) ->
    val_loc v1 \subset dom H1 ->
    val_loc v2 \subset dom H2.
  Proof.
    intros Heq Hin.
    rewrite res_equiv_eq in Heq.
    destruct v1; destruct v2; try contradiction.
    - destruct (Hin l) as [b Hb].
      reflexivity. simpl in Heq. destruct Heq as [Hbs Heq']. rewrite Hb in Heq'. 
      eapply Singleton_Included.
      destruct b.
      + destruct (get l0 H2) eqn:Heq''; try contradiction. 
       now eexists; eauto.
      + destruct (get l0 H2) eqn:Heq''; try contradiction. 
        now eexists; eauto.
      + destruct (get l0 H2) eqn:Heq''; try contradiction. 
        now eexists; eauto.
    - simpl; now eauto with Ensembles_DB. 
  Qed.
  
  Lemma env_locs_in_dom S β1 β2 (H1 H2 : heap block) (rho1 rho2 : env) :
    S |- (H1, rho1) ⩪_(β1, β2) (H2, rho2) ->
    env_locs rho1 S \subset dom H1 ->
    env_locs rho2 S \subset dom H2.
  Proof.
    intros Heq Hsub l [y [Hin Hget]].
    destruct (M.get y rho2) as [v |] eqn:Hget1; try now inv Hget.
    edestruct Heq as [_ [v' [Hget2 Heqv]]]; eauto. 
    symmetry in Heqv. eapply val_loc_in_dom; eauto.
    eapply Included_trans; [| eassumption ].
    eapply get_In_env_locs; eauto.
  Qed.     
  
  Lemma locs_in_dom β1 β2 (H1 H2 : heap block) (b1 b2 : block) :
    block_equiv (β1, H1, b1) (β2, H2, b2) ->
    locs b1 \subset dom H1 ->
    locs b2 \subset dom H2.
  Proof.
    intros Hb Hin.
    destruct b1; destruct b2; try contradiction.
    - simpl in *. destruct Hb as [Heq Hall]; subst.
      (* yikes. maybe write lemma? *)
      induction Hall; try now eauto with Ensembles_DB.
      simpl in *. eapply Union_Included.
       eapply val_loc_in_dom; eauto.
       now eapply Union_Included_l; eauto. 
       eapply IHHall. now eapply Union_Included_r; eauto.
    - destruct Hb as [Hb1 Hb2]. simpl.
      eapply Union_Included; eapply val_loc_in_dom; eauto.
      now eapply Union_Included_l; eauto. 
      now eapply Union_Included_r; eauto. 
     - simpl in *. eapply env_locs_in_dom; eauto.
  Qed.

  Lemma res_equiv_exists_loc β1 β2 H1 H2 v1 v2 l1 :
    (v1, H1) ≈_(β1, β2) (v2, H2) ->
    l1 \in val_loc v1 ->
    exists l2, l2 \in val_loc v2 /\ (Loc l1, H1) ≈_(β1, β2) (Loc l2, H2).
  Proof.
    intros Heq Hin. rewrite res_equiv_eq in Heq.
    destruct v1; destruct v2; try contradiction; inv Hin.
    eexists; split. reflexivity. rewrite res_equiv_eq.
    eassumption.
  Qed.

  Lemma heap_env_equiv_exists_loc S β1 β2 H1 H2 rho1 rho2 l1 :
    S |- (H1, rho1) ⩪_(β1, β2) (H2, rho2) ->
    l1 \in env_locs rho1 S ->
    exists l2, l2 \in env_locs rho2 S /\ (Loc l1, H1) ≈_(β1, β2) (Loc l2, H2).
  Proof.
    intros Heq Hin. edestruct Hin as [x [Hin' Hget]].
    destruct (M.get x rho1) as [v1 |] eqn:Hget1; [| now inv Hget].
    edestruct Heq as [[v2 [Hget2 Heq']] _]; eauto.
    destruct v1; [| now inv Hget].
    destruct v2; [| rewrite res_equiv_eq in Heq'; contradiction ].
    inv Hget. eexists; split; eauto.
    eapply get_In_env_locs; eauto. reflexivity.
  Qed.

  Lemma block_equiv_exists_loc β1 β2 H1 H2 b1 b2 l1 :
    block_equiv (β1, H1, b1) (β2, H2, b2) ->
    l1 \in locs b1 ->
    exists l2, l2 \in locs b2 /\ (Loc l1, H1) ≈_(β1, β2) (Loc l2, H2).
  Proof.
    intros Hb Hin.
    destruct b1; destruct b2; try contradiction; simpl in Hin.
    - destruct Hb as [Heq Hall]. subst. 
      induction Hall. now inv Hin.
      simpl in Hin.
      inv Hin.
      + edestruct res_equiv_exists_loc as [l2 [Hl2in Heq]]; eauto.
        eexists. split; eauto. left. eassumption.
      + edestruct IHHall as [l2 [Hl2in Heq]]; eauto.
        eexists. split; eauto. right. eassumption.
    - destruct Hb as [Hb1 Hb2].
      inv Hin.
      + edestruct res_equiv_exists_loc with (v1 := v) as [l2 [Hl2in Heq]]; eauto.
        eexists. split; eauto. left. eassumption.
      + edestruct res_equiv_exists_loc with (v1 := v0) as [l2 [Hl2in Heq]]; eauto.
        eexists l2. split; eauto. right. eassumption.
    - eapply heap_env_equiv_exists_loc; eauto.
  Qed.

  Lemma heap_env_equiv_post S β1 β2 H1 H2 rho1 rho2 l1 n b1 :
    S |- (H1, rho1) ⩪_(β1, β2) (H2, rho2) ->
    In _ ((post H1 ^ n) (env_locs rho1 S)) l1 ->
    get l1 H1 = Some b1 ->
    exists l2 b2, In _ ((post H2 ^ n) (env_locs rho2 S)) l2 /\ get l2 H2 = Some b2 /\
             block_equiv (β1, H1, b1) (β2, H2, b2).
  Proof.
    intros Heq.
    revert l1 b1. induction n as [| n IHn]; intros l1 b1 Hin Hget.
    - simpl in Hin. 
      destruct Hin as [x [Hin Hgetx]].
      destruct (M.get x rho1) eqn:Heqx; try now inv Hgetx.
      edestruct Heq as [[v' [Heqx' Heqv]] H1']; eauto.
      destruct v; inv Hgetx.
      rewrite res_equiv_eq in Heqv.
      simpl in Heqv. destruct v'; try contradiction.
      rewrite Hget in Heqv. destruct Heqv as [Hbs Heqv].
      destruct (get l H2) eqn:Hgetl; try contradiction.
      do 2 eexists. split.
      eexists. split; eauto. rewrite Heqx'.
      reflexivity. split; eauto.
    - simpl in Hin.
      destruct Hin as [l1' [b1' [Hin [Hget' Hin']]]]. 
      edestruct IHn as [l2' [b2' [Hpost [Hget2 Heqb]]]]; eauto.
      simpl in Heqb.
      edestruct block_equiv_exists_loc as [l2 [Hl2in Hleq]]; eauto.
      rewrite res_equiv_eq in Hleq. simpl in Hleq. rewrite Hget in Hleq.
      destruct Hleq as [Hbs' Heqv'].
      destruct (get l2 H2) as [b2 |] eqn:Hgetl2; try contradiction.
      exists l2, b2. split; [| split; now eauto ].
      eexists. eexists. split; eauto.
  Qed.
  
  Lemma well_formed_respects_heap_env_equiv S β1 β2 H1 H2 rho1 rho2 :
    well_formed (reach' H1 (env_locs rho1 S)) H1 ->
    S |- (H1, rho1) ⩪_(β1, β2) (H2, rho2) ->
    well_formed (reach' H2 (env_locs rho2 S)) H2.
  Proof.
    intros Hwf Heq l2 b2 [n [_ Hin]] Heq2.
    symmetry in Heq. 
    edestruct heap_env_equiv_post as [l1 [b1 [Hpost1 [Hget1 Heq1]]]]; eauto.
    eapply Hwf in Hget1; [| eexists; split; [ now constructor | now eauto ]].
    eapply locs_in_dom; eauto. symmetry; eassumption.
  Qed.

  Lemma heap_env_equiv_preserves_closed S H1 H2 rho1 rho2 b1 b2 :
    S |- (H1, rho1) ⩪_(b1, b2) (H2, rho2) ->
    closed (reach' H1 (env_locs rho1 S)) H1 ->
    closed (reach' H2 (env_locs rho2 S)) H2. 
  Proof.
    intros Heq Hclo.
    eapply reach'_closed. 
    - eapply well_formed_respects_heap_env_equiv. 
      eapply well_formed'_closed. eassumption.
      eassumption. 
    - eapply env_locs_in_dom. eassumption.
      eapply Included_trans. eapply reach'_extensive. eapply env_locs_closed.
      eassumption. 
  Qed.
  
  Lemma heap_env_approx_restrict_env S S' β1 β2 H1 H2 rho1 rho1' rho2 rho2' :
    heap_env_approx S (β1, (H1, rho1)) (β2, (H2, rho2)) ->
    S' \subset S ->
    Restrict_env S' rho1 rho1' ->
    Restrict_env S' rho2 rho2' ->
    heap_env_approx (Full_set _) (β1, (H1, rho1')) (β2, (H2, rho2')).
  Proof. 
    intros Ha Hsub [Heq1 [Hsub1 Hk1]] [Heq2 [Hsub2 Hk2]] x l Hin Hget.
    edestruct Ha as [l' [Hget' Heq]].
    eapply Hsub. eapply Hk1. unfold key_set, In. now rewrite Hget; eauto.
    eapply Hsub1. eassumption.
    eexists. split; eauto.
    rewrite <- Heq2. eassumption. eapply Hk1.
    unfold key_set, In. now rewrite Hget; eauto.
  Qed.

  Corollary heap_env_equiv_restrict_env S S' β1 β2 H1 H2 rho1 rho1' rho2 rho2' :
    S |- (H1, rho1) ⩪_(β1, β2) (H2, rho2) ->
    S' \subset S ->
    Restrict_env S' rho1 rho1' ->
    Restrict_env S' rho2 rho2' ->
    Full_set var |- (H1, rho1') ⩪_(β1, β2) (H2, rho2').
  Proof.
    intros [? ?] ? ? ?.
    split; now eapply heap_env_approx_restrict_env; eauto.
  Qed.


  Lemma subheap_res_approx_l (k : nat) β (H H' : heap block) (v : value) :
    H ⊑ H' ->
    res_approx_fuel k (β, (v, H)) (β, (v, H')).
  Proof.
    revert v. induction k as [k IHk] using lt_wf_rec1.
    intros v Hsub.
    rewrite res_approx_fuel_eq.
    destruct v as [l|]; simpl; eauto.
    destruct (get l H) as [b|] eqn:Hget; eauto.
    destruct b as [c vs1 | v1 v2 | rho1].
    + split; eauto. eexists. split.
      eapply Hsub. eassumption.
      intros.
      eapply Forall2_refl. 
      intros v. eapply IHk; eauto. 
    + split; eauto. do 2 eexists. split.
      eapply Hsub. eassumption.
      intros. split; eapply IHk; eauto. 
    + split; eauto. eexists. split.
      eapply Hsub. eassumption.
      intros. destruct (M.get x rho1); eauto.
      left. do 2 eexists. split. reflexivity.
      split. reflexivity.
      intros i Hlt. eapply IHk; eauto.
  Qed.

  Lemma Forall2_refl_strong (A : Type) (R : A -> A -> Prop) (l : list A) :
    (forall x : A, List.In x l -> R x x) ->
    Forall2 R l l.
  Proof.
    intros Hyp. induction l; eauto.
    constructor.
    eapply Hyp. now constructor.
    eapply IHl. intros x Hin. 
    eapply Hyp. now constructor 2.
  Qed.
  
  Lemma subheap_res_approx_r (k : nat) β (S : Ensemble loc) (H H' : heap block) (v : value) :
    well_formed (reach' H S) H ->
    S \subset dom H ->
    val_loc v \subset (reach' H S) ->
    H ⊑ H' ->
    res_approx_fuel k (β, (v, H')) (β, (v, H)).
  Proof with now eauto with Ensembles_DB.
    revert v. induction k as [k IHk] using lt_wf_rec1.
    intros v Hwf Hin1 Hin2 Hsub.
    rewrite res_approx_fuel_eq.
    destruct v as [l|]; simpl; eauto.
    assert (Hin2':= Hin2).
    eapply reachable_in_dom in Hin2;[ | eassumption | eassumption | reflexivity ].
    destruct Hin2 as [b Hget].
    assert ( Hget' := Hget). eapply Hsub in Hget'.
    rewrite Hget'.
    eapply Singleton_Included_r in Hin2'.
    destruct b as [c vs1 | v1 v2 | rho1].
    + split; eauto. eexists. split. eassumption.
      intros.
      eapply Forall2_refl_strong. 
      intros v. intros Hin. eapply IHk; eauto.
      eapply Included_trans; [| eapply reachable_closed; try eassumption ].
      simpl. eapply In_Union_list.
      eapply in_map. eassumption.
    + split; eauto. do 2 eexists. split. eassumption. 
      intros i Hlt.
      split; eapply IHk; eauto.
      eapply Included_trans; [| eapply reachable_closed; try eassumption ]...
      eapply Included_trans; [| eapply reachable_closed; try eassumption ]...
    + split; eauto. eexists. split. eassumption.
      intros. destruct (M.get x rho1) eqn:Hgetx; eauto.
      left. do 2 eexists. split. reflexivity.
      split. reflexivity.
      intros i Hlt. eapply IHk; eauto.
      eapply Included_trans; [| eapply reachable_closed; try eassumption ].
      eapply get_In_env_locs; [| eassumption ]. 
      now constructor. 
  Qed.
  
  Lemma subheap_res_equiv (S : Ensemble loc) β (H H' : heap block) (v : value) :
    well_formed (reach' H S) H ->
    S \subset dom H ->
    val_loc v \subset (reach' H S) ->
    H ⊑ H' ->
    (v, H) ≈_(β, β) (v, H').
  Proof with now eauto with Ensembles_DB.
    intros. 
    split.
    eapply subheap_res_approx_l; eauto.
    eapply subheap_res_approx_r; eauto.
  Qed.
  
  Lemma subheap_heap_env_approx_l (S : Ensemble loc) S' β
        (H H' : heap block) (rho : env) :
    well_formed (reach' H S) H ->
    S \subset dom H ->
    env_locs rho S' \subset (reach' H S) ->
    H ⊑ H' ->
    heap_env_approx S' (β, (H, rho)) (β, (H', rho)).
  Proof with now eauto with Ensembles_DB.
    intros Hwf Hin1 Hin2 Hsub x l Hin Hget. 
    eexists. split; eauto. 
    eapply subheap_res_equiv; eauto.
    eapply Included_trans; [ | eassumption ].
    eapply get_In_env_locs; [| eassumption ]. 
    eassumption.
  Qed.
  
  Lemma subheap_heap_env_approx_r (S : Ensemble loc) S' β (H H' : heap block) (rho : env) :
    well_formed (reach' H S) H ->
    S \subset dom H ->
    env_locs rho S' \subset (reach' H S) ->
    H ⊑ H' ->
    heap_env_approx S' (β, (H', rho)) (β, (H, rho)).
  Proof with now eauto with Ensembles_DB.
    intros Hwf Hin1 Hin2 Hsub x l Hin Hget. 
    eexists. split; eauto. 
    symmetry. eapply subheap_res_equiv; eauto.
    eapply Included_trans; [ | eassumption ].
    eapply get_In_env_locs; [| eassumption ]. 
    eassumption.
  Qed.
  
  Lemma subheap_heap_env_equiv (S : Ensemble loc) S' β (H H' : heap block) (rho : env) :
    well_formed (reach' H S) H ->
    S \subset dom H ->
    env_locs rho S' \subset (reach' H S) ->
    H ⊑ H' ->
    S' |- (H, rho) ⩪_(β, β) (H', rho).
  Proof with now eauto with Ensembles_DB.
    intros Hwf Hin1 Hin2 Hsub. split.
    now eapply subheap_heap_env_approx_l; eauto.
    now eapply subheap_heap_env_approx_r; eauto.
  Qed.
  
  Lemma subheap_block_equiv (S : Ensemble loc) β (H H' : heap block) (b : block) :
    well_formed (reach' H S) H ->
    S \subset dom H ->
    locs b \subset (reach' H S) ->
    H ⊑ H' ->
    block_equiv (β, H, b) (β, H', b).
  Proof with now eauto with Ensembles_DB.
    intros Hwf Hin1 Hin2 Hsub. 
    destruct b as [c vs | v1 v2 | rho ] .
    + split; eauto.
      eapply Forall2_refl_strong. 
      intros v Hin.
      eapply subheap_res_equiv; try eassumption.
      eapply Included_trans; [| eassumption ].
      simpl. eapply In_Union_list.
      eapply in_map. eassumption.
    + simpl. split; eapply subheap_res_equiv; try eassumption.
      eapply Included_trans; [| eassumption ]...
      eapply Included_trans; [| eassumption ]...       
    + simpl. simpl in Hin2.
      eapply subheap_heap_env_equiv; eassumption.
  Qed.
  
  (* Lemma subheap_heap_approx_l S β (H H' : heap block) (rho : env) : *)
  (*   well_formed (reach' H S) H -> *)
  (*   S \subset dom H -> *)
  (*   H ⊑ H' -> *)
  (*   heap_approx S (β, H) (β, H'). *)
  (* Proof. *)
  (*   intros Hwf Hs Hsub l Hin. split. reflexivity. intros bl Hget. *)
  (*   eapply Hsub in Hget. *)
  (*   eexists; split; eauto. *)
  (*   eapply subheap_block_equiv; eauto. *)
  (*   eapply Included_trans; [| eapply Included_post_reach' ]. *)
  (*   intros l' Hin'. repeat eexists; eauto. *)
  (*   edestruct reachable_in_dom as [b' Hgetb']; try eassumption. *)
  (*   eapply reach'_extensive. eassumption. *)
  (*   rewrite Hgetb'. eapply Hsub in Hgetb'. congruence. *)
  (* Qed. *)
  
  (* Lemma subheap_heap_approx_r S β (H H' : heap block) (rho : env) : *)
  (*   well_formed (reach' H S) H -> *)
  (*   S \subset dom H -> *)
  (*   H ⊑ H' -> *)
  (*   heap_approx S (β, H') (β, H). *)
  (* Proof. *)
  (*   intros Hwf Hs Hsub l Hin. split. reflexivity. intros bl Hget. *)
  (*   edestruct reachable_in_dom as [b' Hgetb']; try eassumption. *)
  (*   eapply reach'_extensive. eassumption. *)
  (*   eexists; split; eauto. *)
  (*   assert (Hgetb := Hgetb'). *)
  (*   eapply Hsub in Hgetb'. subst_exp. *)
  (*   symmetry. eapply subheap_block_equiv; eauto. *)
  (*   eapply Included_trans; [| eapply Included_post_reach' ]. *)
  (*   intros l' Hin'. repeat eexists; eauto. *)
  (* Qed. *)
  
  (* Lemma subheap_heap_equiv S β (H H' : heap block) (rho : env) : *)
  (*    well_formed (reach' H S) H -> *)
  (*    S \subset dom H -> *)
  (*    H ⊑ H' -> *)
  (*    S |- H ≃_(β, β) H'. *)
  (* Proof. *)
  (*   intros Hwf Hs Hsub. *)
  (*   split.  *)
  (*   now eapply subheap_heap_approx_l; eauto. *)
  (*   now eapply subheap_heap_approx_r; eauto. *)
  (* Qed. *)

      (** Inversion of renamings *)

  Lemma res_approx_inverse_subdomain_l H1 H2 b1 b2 b1' v1 v2 n :
    inverse_subdomain (reach' H1 (val_loc v1)) b1 b1' ->
    res_approx_fuel n (b1, (v1, H1)) (b2, (v2, H2)) ->
    res_approx_fuel n (id, (v1, H1)) (b1' ∘ b2, (v2, H2)).
  Proof.
    revert v1 v2. 
    induction n as [n IHn] using lt_wf_rec1; intros v1 v2 Hinv Heq1.
    destruct n. 
    - destruct v1 as [l1 | f1 B1]; destruct v2 as [l2 | f2 B2 ];
        simpl in *; eauto.
      destruct Heq1 as [Heq1 Heq2]. split.
      + unfold id, compose. rewrite Heq1.
        replace (b1' (b1 l1)) with ((b1' ∘ b1) l1) by (unfold compose; reflexivity). 
        destruct Hinv as [Heql Heqr]. rewrite Heqr. reflexivity.
        eapply reach'_extensive. reflexivity.
      + destruct (get l1 H1) eqn:Hget1; eauto. 
    - destruct v1 as [l1 | f1 B1]; destruct v2 as [l2 | f2 B2 ]; simpl in *; eauto.
      destruct Heq1 as [Heq1 Heq2]. simpl. split.
      + unfold id, compose. rewrite Heq1.
        replace (b1' (b1 l1)) with ((b1' ∘ b1) l1) by (unfold compose; reflexivity). 
        destruct Hinv as [Heql Heqr]. rewrite Heqr. reflexivity.
        eapply reach'_extensive. reflexivity.
      + destruct (get l1 H1) eqn:Hget1; eauto. 
        destruct b as [ c1 vs1 | v1 v1' | rho1 ]; simpl.
        * edestruct Heq2 as [vs2 [Hget2 Hi]].
          eexists; split; eauto. intros i Hlt. 

          eapply Forall2_monotonic_strong; [| eapply Hi; eassumption ]. 
          intros x1 x2 Hin1 Hin2. simpl. intros. eapply IHn. omega.

          eapply inverse_subdomain_antimon. eassumption.
          rewrite (reach_unfold H1 [set l1]). eapply Included_Union_preserv_r.
          eapply reach'_set_monotonic. rewrite post_Singleton; eauto.
          eapply In_Union_list. eapply in_map. eassumption.

          eassumption. 

        * edestruct Heq2 as (v3 & v4 & Hget3 & Hi).
          do 2 eexists; split; eauto.

          intros i Hlt; split; eapply IHn.

          omega.
          eapply inverse_subdomain_antimon. eassumption.
          rewrite (reach_unfold H1 [set l1]). eapply Included_Union_preserv_r.
          eapply reach'_set_monotonic. rewrite post_Singleton; eauto.
          now eauto with Ensembles_DB.
          now eapply Hi; eauto.

          omega.
          eapply inverse_subdomain_antimon. eassumption.
          rewrite (reach_unfold H1 [set l1]). eapply Included_Union_preserv_r.
          eapply reach'_set_monotonic. rewrite post_Singleton; eauto.
          now eauto with Ensembles_DB.
          now eapply Hi; eauto.

        * edestruct Heq2 as (rho2 & Hgetl2 & Henv). 
          eexists; split; eauto. 

          intros x. edestruct (Henv x); eauto.
          left. edestruct H as (v3 & v4 & Hget3 & Hget4 & Hi). 
          do 2 eexists; repeat split; eauto.
          intros i Hlt. eapply IHn.
          omega.
          eapply inverse_subdomain_antimon. eassumption.
          rewrite (reach_unfold H1 [set l1]). eapply Included_Union_preserv_r.
          eapply reach'_set_monotonic. rewrite post_Singleton; eauto.
          eapply get_In_env_locs. now constructor. eassumption.
          eapply Hi. omega. 
  Qed.       


  Lemma res_approx_inverse_subdomain_r H1 H2 b1 b2 b2' v1 v2 n :
    inverse_subdomain (reach' H2 (val_loc v2)) b2 b2' ->
    res_approx_fuel n (b1, (v1, H1)) (b2, (v2, H2)) ->
    res_approx_fuel n (b2' ∘ b1, (v1, H1)) (id, (v2, H2)).
  Proof.
    revert v1 v2. 
    induction n as [n IHn] using lt_wf_rec1; intros v1 v2 Hinv Heq1.
    destruct n. 
    - destruct v1 as [l1 | f1 B1]; destruct v2 as [l2 | f2 B2 ];
        simpl in *; eauto.
      destruct Heq1 as [Heq1 Heq2]. split.
      + unfold id, compose. rewrite <- Heq1.
        replace (b2' (b2 l2)) with ((b2' ∘ b2) l2) by (unfold compose; reflexivity). 
        destruct Hinv as [Heql Heqr]. rewrite Heqr. reflexivity.
        eapply reach'_extensive. reflexivity.
      + destruct (get l1 H1) eqn:Hget1; eauto. 
    - destruct v1 as [l1 | f1 B1]; destruct v2 as [l2 | f2 B2 ]; simpl in *; eauto.
      destruct Heq1 as [Heq1 Heq2]. simpl. split.
      + unfold id, compose. rewrite <- Heq1.
        replace (b2' (b2 l2)) with ((b2' ∘ b2) l2) by (unfold compose; reflexivity). 
        destruct Hinv as [Heql Heqr]. rewrite Heqr. reflexivity.
        eapply reach'_extensive. reflexivity.
      + destruct (get l1 H1) eqn:Hget1; eauto. 
        destruct b as [ c1 vs1 | v1 v1' | rho1 ]; simpl.
        * edestruct Heq2 as [vs2 [Hget2 Hi]].
          eexists; split; eauto. intros i Hlt. 

          eapply Forall2_monotonic_strong; [| eapply Hi; eassumption ]. 
          intros x1 x2 Hin1 Hin2. simpl. intros. eapply IHn. omega.

          eapply inverse_subdomain_antimon. eassumption.
          rewrite (reach_unfold H2 [set l2]). eapply Included_Union_preserv_r.
          eapply reach'_set_monotonic. rewrite post_Singleton; eauto.
          eapply In_Union_list. eapply in_map. eassumption.

          eassumption. 

        * edestruct Heq2 as (v3 & v4 & Hget3 & Hi).
          do 2 eexists; split; eauto.

          intros i Hlt; split; eapply IHn.

          omega.
          eapply inverse_subdomain_antimon. eassumption.
          rewrite (reach_unfold H2 [set l2]). eapply Included_Union_preserv_r.
          eapply reach'_set_monotonic. rewrite post_Singleton; eauto.
          now eauto with Ensembles_DB.
          now eapply Hi; eauto.

          omega.
          eapply inverse_subdomain_antimon. eassumption.
          rewrite (reach_unfold H2 [set l2]). eapply Included_Union_preserv_r.
          eapply reach'_set_monotonic. rewrite post_Singleton; eauto.
          now eauto with Ensembles_DB.
          now eapply Hi; eauto.

        * edestruct Heq2 as (rho2 & Hgetl2 & Henv). 
          eexists; split; eauto. 

          intros x. edestruct (Henv x); eauto.
          left. edestruct H as (v3 & v4 & Hget3 & Hget4 & Hi). 
          do 2 eexists; repeat split; eauto.
          intros i Hlt. eapply IHn.
          omega.
          eapply inverse_subdomain_antimon. eassumption.
          rewrite (reach_unfold H2 [set l2]). eapply Included_Union_preserv_r.
          eapply reach'_set_monotonic. rewrite post_Singleton; eauto.
          eapply get_In_env_locs. now constructor. eassumption. 
          eapply Hi. omega.
  Qed.       

  Lemma res_equiv_inverse_subdomain H1 H2 v1 v2 b1 b2 b1' :
    inverse_subdomain (reach' H1 (val_loc v1)) b1 b1' ->
    (v1, H1) ≈_(b1, b2) (v2, H2) ->
    (v1, H1) ≈_(id, b1' ∘ b2) (v2, H2).
  Proof.
    intros Hinv Heq n. edestruct (Heq n) as [Hl Hr].  
    split. 
    eapply res_approx_inverse_subdomain_l. eassumption.
    eassumption. 
    eapply res_approx_inverse_subdomain_r. eassumption.
    eassumption. 
  Qed.

  Lemma heap_equiv_inverse_subdomain S H1 H2 b1 b1' :
    inverse_subdomain (reach' H1 S) b1 b1' ->
    S |- H1 ≃_(b1, id) H2  ->
    image b1 S |- H1 ≃_(id, b1') H2.
  Proof.
    intros Hinv Heq l [l' [Hin Heq']]; subst.
    replace (b1' (b1 l')) with l' in *.

    assert (Hin' := Hin). 
    eapply Heq in Hin. unfold id in *.

    eapply res_equiv_inverse_subdomain.  

    + simpl. eapply inverse_subdomain_antimon. eassumption.
      eapply reach'_set_monotonic. eapply Singleton_Included. 
      eassumption.

    + eassumption.

    + destruct Hinv as [Hinv1 Hinv2]. 
      replace (b1' (b1 l')) with ((b1' ∘ b1) l') by reflexivity.
      rewrite Hinv2. reflexivity. eapply reach'_extensive. eassumption. 
  Qed.


    Lemma heap_env_approx_inverse_subdomain_l
        (S : Ensemble var) (b1 b2 b2' : loc -> loc) (H1 H2 : heap block) 
        (rho1 rho2 : M.t value) :
    inverse_subdomain (reach' H2 (env_locs rho2 S)) b2 b2' -> 
    heap_env_approx S (b1, (H1, rho1)) (b2, (H2, rho2)) ->
    heap_env_approx S (b2' ∘ b1, (H1, rho1)) (id, (H2, rho2)). 
  Proof.
    intros Hinv Heq x v Hin Hget. 
    edestruct Heq as [l' [Hget2 Heq2]]. eassumption. eassumption.
    eexists. split. eassumption.
    symmetry in Heq2. 
    eapply res_equiv_inverse_subdomain in Heq2. 
    symmetry in Heq2. eassumption. 
    eapply inverse_subdomain_antimon. 
    eassumption. eapply reach'_set_monotonic.
    eapply get_In_env_locs; eassumption.
  Qed.
  
  Lemma heap_env_approx_inverse_subdomain_r
        (S : Ensemble var) (b1 b1' b2 : loc -> loc) (H1 H2 : heap block) 
        (rho1 rho2 : M.t value) :
    inverse_subdomain (reach' H1 (env_locs rho1 S)) b1 b1' -> 
    heap_env_approx S (b1, (H1, rho1)) (b2, (H2, rho2)) ->
    heap_env_approx S (id, (H1, rho1)) (b1' ∘ b2, (H2, rho2)). 
  Proof.
    intros Hinv Heq x v Hin Hget. 
    edestruct Heq as [l' [Hget2 Heq2]]. eassumption. eassumption.
    eexists. split. eassumption.
    eapply res_equiv_inverse_subdomain in Heq2. 
    eassumption. 
    eapply inverse_subdomain_antimon. 
    eassumption. eapply reach'_set_monotonic.
    eapply get_In_env_locs; eassumption.
  Qed.
  
  Lemma heap_env_equiv_inverse_subdomain
        (S : Ensemble var) (b1 b2 b2' : loc -> loc) (H1 H2 : heap block) 
        (rho1 rho2 : M.t value) :
    inverse_subdomain (reach' H2 (env_locs rho2 S)) b2 b2' -> 
    S |- (H1, rho1) ⩪_(b1, b2) (H2, rho2) ->
    S |- (H1, rho1) ⩪_(b2' ∘ b1, id) (H2, rho2). 
  Proof.
    intros Hinv [Heq1 Heq2]. split.
    eapply heap_env_approx_inverse_subdomain_l; eassumption.
    eapply heap_env_approx_inverse_subdomain_r; eassumption. 
  Qed.


  (** * Closure definitions preserves things *)

  Lemma heap_env_equiv_def_funs_strong S β1 H1 H2 rho1 rho2 clo_rho1 clo_rho2 B B0 l1 l2 :
    well_formed (reach' H1 (env_locs rho1 (Setminus _ S (name_in_fundefs B)))) H1 ->
    well_formed (reach' H2 (env_locs rho2 (Setminus _ S (name_in_fundefs B)))) H2 ->

    (env_locs rho1 (Setminus _ S (name_in_fundefs B))) \subset dom H1 ->
    (env_locs rho2 (Setminus _ S (name_in_fundefs B))) \subset dom H2 ->

    get l1 H1 = Some (Env clo_rho1) ->
    get l2 H2 = Some (Env clo_rho2) ->

    env_locs clo_rho1 (Full_set _) \subset (reach' H1 (env_locs rho1 (Setminus _ S (name_in_fundefs B)))) ->
    env_locs clo_rho2 (Full_set _) \subset (reach' H2 (env_locs rho2 (Setminus _ S (name_in_fundefs B)))) ->

    (occurs_free_fundefs B0) \subset (Setminus _ S (name_in_fundefs B)) ->

    (Loc l1, H1) ≈_(id, β1) (Loc l2, H2) ->

    injective_subdomain (l2 |: reach' H2 (env_locs rho2 (Setminus _ S (name_in_fundefs B)))) β1 ->

    S \\ (name_in_fundefs B) |- (H1, rho1) ⩪_(id, β1) (H2, rho2) ->

    (exists β1', S |- (def_closures B B0 rho1 H1 (Loc l1)) ⩪_(id, β1') (def_closures B B0 rho2 H2 (Loc l2)) /\
            f_eq_subdomain (dom H2) β1 β1' /\
            let '(H1', rho1') := (def_closures B B0 rho1 H1 (Loc l1)) in
            let '(H2', rho2') := (def_closures B B0 rho2 H2 (Loc l2)) in
            well_formed (reach' H1' (env_locs rho1' S)) H1' /\
            well_formed (reach' H2' (env_locs rho2' S)) H2' /\
            env_locs rho1' S \subset dom H1' /\
            env_locs rho2' S \subset dom H2' /\
            injective_subdomain (l2 |: reach' H2' (env_locs rho2' S)) β1').
  Proof with (now eauto with Ensembles_DB).
    revert S rho1 rho2; induction B;
    intros S rho1 rho2 Hc1 Hc2 Hdom1 Hdom2 He1 He2 Hg1 Hg2 Hsub Hloc Hinj Heq; simpl; eauto.
    - destruct (def_closures B B0 rho1 H1 (Loc l1)) as [H1' rho1'] eqn:Hd1.
      destruct (def_closures B B0 rho2 H2 (Loc l2)) as [H2' rho2'] eqn:Hd2.
      destruct (alloc (Clos (FunPtr B0 v) (Loc l1)) _) as [l1' H1''] eqn:Ha1.
      destruct (alloc (Clos (FunPtr B0 v) (Loc l2)) _) as [l2' H2''] eqn:Ha2.
      
      edestruct IHB with (S := S \\ [set v]) as [β1' [HBs [Heqf Hinj']]]; try eassumption.
      + eapply well_formed_antimon; [| eassumption ].
        eapply reach'_set_monotonic. eapply env_locs_monotonic. simpl.
        rewrite <- !Setminus_Union...
      + eapply well_formed_antimon; [| eassumption ].
        eapply reach'_set_monotonic. eapply env_locs_monotonic. simpl.
        rewrite <- !Setminus_Union...
      + eapply Included_trans; [| eassumption ].
        eapply env_locs_monotonic. simpl. rewrite <- !Setminus_Union...
      + eapply Included_trans; [| eassumption ].
        eapply env_locs_monotonic. simpl. rewrite <- !Setminus_Union...
      + eapply Included_trans. eassumption.
        eapply reach'_set_monotonic. eapply env_locs_monotonic. simpl.
        rewrite <- !Setminus_Union...
      + eapply Included_trans. eassumption.
        eapply reach'_set_monotonic. eapply env_locs_monotonic. simpl.
        rewrite <- !Setminus_Union...
      + eapply Included_trans. eassumption.
        simpl. rewrite <- !Setminus_Union...
      + eapply injective_subdomain_antimon. eassumption.
        eapply Included_Union_compat. reflexivity.
        eapply reach'_set_monotonic. eapply env_locs_monotonic. simpl.
        rewrite <- !Setminus_Union...
      + eapply heap_env_equiv_antimon. eassumption.
        simpl. rewrite <- !Setminus_Union...
      + rewrite Hd1, Hd2 in Hinj'. destruct Hinj' as [Hwf1' [Hwf2' [Henv1 [Henv2 Hinj']]]].
        eexists (β1' {l2' ~> l1'}). split; [| split; [| split; [| split; [| split; [| split ]] ]]].
        { eapply heap_env_equiv_alloc_alt; (try now apply Ha1); (try now apply Ha2).
          + eapply reach'_closed. eassumption. eassumption.
          + eapply reach'_closed. eassumption. eassumption.
          + eapply reach'_extensive.
          + eapply reach'_extensive.
          + simpl. 
            eapply Included_trans; [| eapply dom_subheap; eapply def_funs_subheap; now eauto ].
            rewrite Union_Empty_set_neut_l. eapply Singleton_Included.
            eexists; eauto.
          + simpl. 
            eapply Included_trans; [| eapply dom_subheap; eapply def_funs_subheap; now eauto ].
            rewrite Union_Empty_set_neut_l. eapply Singleton_Included.
            eexists; eauto.
          + simpl. rewrite Union_Empty_set_neut_l.
            rewrite post_Singleton; [| erewrite def_funs_subheap; eauto ].
            simpl. eapply Included_trans. eassumption.
            simpl. rewrite <- Setminus_Union. eapply Included_trans.
            eapply reach'_heap_monotonic. eapply def_funs_subheap; eauto.
            eapply reach'_set_monotonic. eapply def_closures_env_locs_subset.  eassumption.
          + simpl. rewrite Union_Empty_set_neut_l.
            rewrite post_Singleton; [| erewrite def_funs_subheap; eauto ].
            simpl. eapply Included_trans. eassumption.
            simpl. rewrite <- Setminus_Union. eapply Included_trans.
            eapply reach'_heap_monotonic. eapply def_funs_subheap; eauto.
            eapply reach'_set_monotonic. eapply def_closures_env_locs_subset. eassumption.
          + eapply heap_env_equiv_rename_ext.
            rewrite Hd1, Hd2 in HBs. eassumption.
            reflexivity. apply f_eq_subdomain_extend_not_In_S_r. intros Hc.
            eapply reachable_in_dom in Hc. destruct Hc as [v1' Hget'].
            erewrite alloc_fresh in Hget'; try eassumption.
            discriminate.
            eassumption.
            eassumption.
            reflexivity.
          + rewrite extend_gss. reflexivity. 
          + simpl. split. rewrite res_equiv_eq; now eauto.
            eapply res_equiv_weakening_alt.
            eapply reach'_closed. now apply Hc1. eassumption.
            eapply reach'_closed. now apply Hc2. eassumption.
            eapply res_equiv_rename_ext. eassumption.
            reflexivity. 
            eapply f_eq_subdomain_extend_not_In_S_r. intros Hc.
            eapply reachable_in_dom in Hc.
            eapply dom_subheap in Hc; [| eapply def_funs_subheap; now eauto ]. 
            destruct Hc as [v1' Hget'].
            erewrite alloc_fresh in Hget'; try eassumption.
            discriminate.
            rewrite reach_unfold. simpl.
            eapply well_formed_Union.
            intros l3 b Heq' Hget. inv Heq'. subst_exp. simpl. 
            eapply Included_trans. eassumption. eapply reachable_in_dom.
            eassumption.  eassumption.
            rewrite post_Singleton; try eassumption. eapply well_formed_antimon; try eassumption.
            eapply Included_trans. eapply reach'_set_monotonic. eassumption.
            rewrite <- reach'_idempotent. reflexivity.
            eapply Singleton_Included. now eexists; eauto.
            eapply f_eq_subdomain_antimon; [| eassumption ].
            rewrite reach_unfold. simpl.
            rewrite post_Singleton;  [ | eassumption ].
            eapply Union_Included.
            eapply Singleton_Included. now eexists; eauto.
            eapply reachable_in_dom. eapply well_formed_antimon; [| eassumption ].
            eapply Included_trans. eapply reach'_set_monotonic. eassumption.
            rewrite <- reach'_idempotent. reflexivity.
            eapply Included_trans. eassumption.
            eapply reachable_in_dom. eassumption.
            eassumption.
            eapply def_funs_subheap; now eauto.
            eapply def_funs_subheap; now eauto.
            eapply Singleton_Included. now eexists; eauto.
            eapply Singleton_Included. now eexists; eauto.
            simpl. rewrite post_Singleton; [ | eassumption ].
            eapply Included_trans. eassumption. reflexivity.
            simpl. rewrite post_Singleton; [ | eassumption ].
            eapply Included_trans. eassumption. reflexivity. }
        { eapply f_eq_subdomain_extend_not_In_S_r. intros Hc.
          eapply dom_subheap in Hc; [| eapply def_funs_subheap; now eauto ]. 
          destruct Hc as [v1' Hget'].
          erewrite alloc_fresh in Hget'; try eassumption.
          discriminate. eassumption. }
        { eapply well_formed_antimon with
          (S2 := reach' H1'' (env_locs (M.set v (Loc l1') rho1') (S \\ [set v] :|: [set v]))).
          eapply reach'_set_monotonic. eapply env_locs_monotonic.
          now eauto with Ensembles_DB typeclass_instances.
          eapply well_formed_reach_alloc_in_dom; try eassumption.
          simpl. rewrite Union_Empty_set_neut_l.
          rewrite post_Singleton; [| erewrite def_funs_subheap; eauto ].
          simpl. eapply Included_trans. eassumption.
          simpl. rewrite <- Setminus_Union. eapply Included_trans.
          eapply reach'_heap_monotonic. eapply def_funs_subheap; eauto.
          eapply reach'_set_monotonic. eapply def_closures_env_locs_subset. eassumption.
          simpl.
          rewrite Union_Empty_set_neut_l. eapply Singleton_Included.
          eexists. erewrite def_funs_subheap; eauto. }
        { eapply well_formed_antimon with
          (S2 := reach' H2'' (env_locs (M.set v (Loc l2') rho2') (S \\ [set v] :|: [set v]))).
          eapply reach'_set_monotonic. eapply env_locs_monotonic.
          now eauto with Ensembles_DB typeclass_instances.
          eapply well_formed_reach_alloc_in_dom; try eassumption.
          simpl. rewrite Union_Empty_set_neut_l.
          rewrite post_Singleton; [| erewrite def_funs_subheap; eauto ].
          simpl. eapply Included_trans. eassumption.
          simpl. rewrite <- Setminus_Union. eapply Included_trans.
          eapply reach'_heap_monotonic. eapply def_funs_subheap; eauto.
          eapply reach'_set_monotonic. eapply def_closures_env_locs_subset. eassumption.
          simpl.
          rewrite Union_Empty_set_neut_l. eapply Singleton_Included.
          eexists. erewrite def_funs_subheap; eauto. }
        { eapply Included_trans. eapply env_locs_set_Inlcuded'.
          eapply Union_Included. eapply Singleton_Included.
          eexists. erewrite gas; eauto.
          eapply Included_trans. eassumption.
          eapply dom_subheap. eapply alloc_subheap. eassumption. }
        { eapply Included_trans. eapply env_locs_set_Inlcuded'.
          eapply Union_Included. eapply Singleton_Included.
          eexists. erewrite gas; eauto.
          eapply Included_trans. eassumption.
          eapply dom_subheap. eapply alloc_subheap. eassumption. }        
        { eapply injective_subdomain_antimon;
          [| eapply Included_Union_compat;
             [ reflexivity |  now eapply reach'_set_monotonic; eapply env_locs_set_Inlcuded' ] ]. 
          rewrite reach'_Union. rewrite reach_unfold. simpl. 
          rewrite post_Singleton; [| erewrite gas; eauto ]. simpl.
          rewrite Union_Empty_set_neut_l. rewrite reach_unfold.
          rewrite post_Singleton;
            [| erewrite alloc_subheap; eauto;
               now erewrite def_funs_subheap; eauto ].
          rewrite <- !Union_assoc. rewrite (Union_Same_set (reach' H2'' (locs (Env clo_rho2)))). 
          rewrite <- well_formed_reach_alloc_same; try eassumption.
          rewrite (Union_Same_set [set l2]); [| now eauto with Ensembles_DB ].

          eapply injective_subdomain_extend. eassumption.

          intros Hc. rewrite Setminus_Union_distr in Hc.
          eapply image_Union in Hc. inv Hc.
          apply image_monotonic with (S' := [set l2]) in H; try now eauto with Ensembles_DB.
          eapply image_f_eq_subdomain in H; [| eapply f_eq_subdomain_antimon; try eassumption ].
          rewrite image_Singleton in H. inv H.
          eapply alloc_fresh in Ha1. 
          rewrite res_equiv_eq in Hloc. destruct Hloc as [Heqb Hloc].
          unfold id in Heqb; subst. erewrite def_funs_subheap in Ha1; now eauto.

          eapply Singleton_Included. now eexists; eauto.

          rewrite Hd1, Hd2 in HBs. 
          eapply heap_env_equiv_image_reach in HBs.
          assert (Hin : reach' H1' (env_locs rho1' (S \\ [set v])) l1').
          { rewrite image_id in HBs. eapply HBs.
            eapply image_monotonic; try eassumption... }
          eapply reachable_in_dom in Hin; try eassumption.
          destruct Hin as [v1' Hget1']. erewrite alloc_fresh in Hget1'; eauto.
          discriminate.

          eapply Included_trans. eapply reach'_set_monotonic. eassumption.
          eapply Included_trans. eapply reach'_set_monotonic.
          eapply reach'_heap_monotonic. eapply subheap_trans.
          eapply def_funs_subheap. now eauto.
          eapply alloc_subheap. now eauto.
          rewrite <- reach'_idempotent.
          eapply reach'_set_monotonic. simpl.          
          rewrite <- Setminus_Union.
          eapply def_closures_env_locs_subset. eassumption. }
    - eexists. simpl in *.
      rewrite Setminus_Empty_set_neut_r in Hinj, Heq, Hc1, Hc2, Hdom1, Hdom2.
      repeat (split; eauto).
  Qed.

  
     
  Lemma heap_env_equiv_def_funs_strong_left S {Hs : ToMSet S} b1 H1 H2 rho1 rho2 clo_rho1 clo_rho2 B B0 l1 l2 :
    well_formed (reach' H1 (env_locs rho1 (S \\ (name_in_fundefs B)))) H1 ->
    env_locs rho1 (S \\ (name_in_fundefs B)) \subset dom H1 ->
    
    get l1 H1 = Some (Env clo_rho1) ->
    get l2 H2 = Some (Env clo_rho2) ->

    env_locs clo_rho1 (Full_set _) \subset (reach' H1 (env_locs rho1 (S \\ (name_in_fundefs B)))) ->
    env_locs clo_rho2 (Full_set _) \subset (reach' H2 (env_locs rho2 (S \\ (name_in_fundefs B)))) ->

    (occurs_free_fundefs B0) \subset (S \\ (name_in_fundefs B)) ->

    (Loc l1, H1) ≈_(b1, id) (Loc l2, H2) ->

    injective_subdomain (l1 |: reach' H1 (env_locs rho1 (S \\ (name_in_fundefs B)))) b1 ->

    S \\ (name_in_fundefs B) |- (H1, rho1) ⩪_(b1, id) (H2, rho2) ->

    (exists b1', S |- (def_closures B B0 rho1 H1 (Loc l1)) ⩪_(b1', id) (def_closures B B0 rho2 H2 (Loc l2)) /\
            (* f_eq_subdomain (dom H1) b1 b1' /\ *)
            let '(H1', rho1') := (def_closures B B0 rho1 H1 (Loc l1)) in
            let '(H2', rho2') := (def_closures B B0 rho2 H2 (Loc l2)) in
            well_formed (reach' H1' (env_locs rho1' S)) H1' /\
            well_formed (reach' H2' (env_locs rho2' S)) H2' /\
            env_locs rho1' S \subset dom H1' /\
            env_locs rho2' S \subset dom H2' /\
            injective_subdomain (l1 |: reach' H1' (env_locs rho1' S)) b1').
  Proof with (now eauto with Ensembles_DB).
    intros Hwf1 Hl1 Hg1 Hg2 Hr1 Hr2 Hsub Heq Hinj Heqenv. 
    edestruct inverse_exists with (b := b1) as [d [Hinji Hinvi]]; [| eassumption |]. 
    now tci.
    
    edestruct heap_env_equiv_def_funs_strong as (b1' & Hequiv' & Hfeq1' & Hlet ). 
    - eassumption.
    - eapply well_formed_respects_heap_env_equiv. eassumption.
      eassumption.
    - eassumption.
    - eapply env_locs_in_dom. eassumption. eassumption.
    - eassumption.
    - eassumption.
    - eassumption.
    - eassumption.
    - eassumption. 
    - eapply res_equiv_inverse_subdomain; [| eassumption ].
      eapply inverse_subdomain_antimon. eassumption.
      simpl. rewrite (reach_unfold H1 [set l1]).
      simpl. rewrite post_Singleton; eauto. eapply Included_Union_compat.
      reflexivity.
      simpl. rewrite (reach'_idempotent H1 (env_locs rho1 _)). eapply reach'_set_monotonic. 
      eassumption.
    - rewrite compose_id_neut_r.
      eapply injective_subdomain_antimon. eassumption.
      rewrite image_Union, image_Singleton. eapply Included_Union_compat.

      rewrite res_equiv_eq in Heq. destruct Heq as [Heq _].
      unfold id in *. subst. reflexivity. 
      
      rewrite heap_env_equiv_image_reach; [| eassumption ]. 
      rewrite image_id. reflexivity. 

    - rewrite compose_id_neut_r.
      symmetry in Heqenv.
      eapply heap_env_equiv_inverse_subdomain in Heqenv; [| eapply inverse_subdomain_antimon; try eassumption ].
      symmetry in Heqenv. eassumption. now eauto with Ensembles_DB.
    - destruct (def_closures B B0 rho1 H1 (Loc l1)) as [H1' rho1'] eqn:Hdefs1.
      destruct (def_closures B B0 rho2 H2 (Loc l2)) as [H2' rho2'] eqn:Hdefs2.
      destruct Hlet as (Hwf1' & Hwf2' & Hl1' & Hl2' & Hinjd).
      
      edestruct inverse_exists with (b := b1') as [d' [Hinji' Hinvi']]; [| eassumption |]. 
      now tci.

      eexists d'. split; [| split; [| split; [| split; [| split ]]]]. 
      
      + eapply heap_env_equiv_inverse_subdomain in Hequiv'. 
        rewrite compose_id_neut_r in Hequiv'. eassumption. 
        eapply inverse_subdomain_antimon; [ eassumption |]... 

      + eassumption.
      + eassumption.
      + eassumption.
      + eassumption.
      + eapply injective_subdomain_antimon. eassumption.
        rewrite image_Union, image_Singleton. eapply Included_Union_compat.
        
        rewrite res_equiv_eq in Heq. destruct Heq as [Heq _].
        unfold id in *. subst. eapply Singleton_Included.
        destruct Hinvi as [Hfeq1 Hfeq2]. rewrite <- Hfeq1'.
        unfold compose; simpl.
        replace (d (b1 l1)) with ((d ∘ b1) l1). 
        rewrite Hfeq2. reflexivity. now left.
        reflexivity. 
        now eexists; eauto. 
        rewrite <- heap_env_equiv_image_reach; [| eassumption ]. 
        rewrite image_id. reflexivity. 
  Qed.
  
  
  Lemma heap_env_equiv_def_funs_strong_left_alt S b1 H1 H2 rho1 rho2 clo_rho1 clo_rho2 B B0 l1 l2 :
    well_formed (reach' H1 (env_locs rho1 S)) H1 ->
    env_locs rho1 S \subset dom H1 ->
    
    get l1 H1 = Some (Env clo_rho1) ->
    get l2 H2 = Some (Env clo_rho2) ->

    env_locs clo_rho1 (Full_set _) \subset (reach' H1 (env_locs rho1 S)) ->
    env_locs clo_rho2 (Full_set _) \subset (reach' H2 (env_locs rho2 S)) ->

    (occurs_free_fundefs B0) \subset S ->

    (Loc l1, H1) ≈_(b1, id) (Loc l2, H2) ->

    injective_subdomain (l1 |: reach' H1 (env_locs rho1 S)) b1 ->

    S |- (H1, rho1) ⩪_(b1, id) (H2, rho2) ->

   (exists b1', name_in_fundefs B :|: S |- (def_closures B B0 rho1 H1 (Loc l1)) ⩪_(b1', id) (def_closures B B0 rho2 H2 (Loc l2)) /\
           let '(H1', rho1') := (def_closures B B0 rho1 H1 (Loc l1)) in
           let '(H2', rho2') := (def_closures B B0 rho2 H2 (Loc l2)) in
           f_eq_subdomain (dom H1) b1 b1' /\
           well_formed (reach' H1' (env_locs rho1' (name_in_fundefs B :|: S))) H1' /\
           well_formed (reach' H2' (env_locs rho2' (name_in_fundefs B :|: S))) H2' /\
           env_locs rho1' (name_in_fundefs B :|: S) \subset dom H1' /\
           env_locs rho2' (name_in_fundefs B :|: S) \subset dom H2' /\
           injective_subdomain (l1 |: reach' H1' (env_locs rho1' (name_in_fundefs B :|: S))) b1').
  Proof with (now eauto with Ensembles_DB).
    revert S rho1 rho2; induction B;
      intros S rho1 rho2 Hc1 Hdom1 He1 He2 Hg1 Hg2 Hsub Hloc Hinj Heq; simpl; eauto.
    - destruct (def_closures B B0 rho1 H1 (Loc l1)) as [H1' rho1'] eqn:Hd1.
      destruct (def_closures B B0 rho2 H2 (Loc l2)) as [H2' rho2'] eqn:Hd2.
      destruct (alloc (Clos (FunPtr B0 v) (Loc l1)) _) as [l1' H1''] eqn:Ha1.
      destruct (alloc (Clos (FunPtr B0 v) (Loc l2)) _) as [l2' H2''] eqn:Ha2.
      
      edestruct IHB with (S := S) as [b1' [HBs Hlet]]; try eassumption; tci.
      + rewrite Hd1, Hd2 in Hlet, HBs. destruct Hlet as [Hdom2 [Hwf1' [Hwf2' [Henv1 [Henv2 Hinj']]]]].
        eexists (b1' {l1' ~> l2'}). split; [| split; [| split; [| split; [| split; [| split ]] ]]].
        { rewrite <- Union_assoc.
          eapply heap_env_equiv_alloc_alt'; (try now apply Ha1); (try now apply Ha2).
          + eapply reach'_closed. eassumption. eassumption.
          + eapply heap_env_equiv_preserves_closed. eassumption. 
            eapply reach'_closed. eassumption. eassumption.
          + eapply Included_trans; [| eapply reach'_extensive ]...
          + eapply reach'_extensive.
          + simpl. 
            rewrite Union_Empty_set_neut_l. eapply Singleton_Included.
            eapply dom_subheap. eapply def_funs_subheap; now eauto.
            eexists; eauto.
          + simpl. 
            rewrite Union_Empty_set_neut_l. eapply Singleton_Included.
            eapply dom_subheap. eapply def_funs_subheap; now eauto.
            eexists; eauto.
          + simpl. rewrite Union_Empty_set_neut_l.
            rewrite Union_commut. eapply def_closures_env_locs_post_reach with (cenv := Loc l1).
            eassumption.
            simpl. rewrite post_Singleton; [| eassumption ].
            eassumption.
          + simpl. rewrite Union_Empty_set_neut_l.
            rewrite Union_commut. eapply def_closures_env_locs_post_reach with (cenv := Loc l2).
            eassumption.
            simpl. rewrite post_Singleton; [| eassumption ].
            eassumption.
          + eapply heap_env_equiv_rename_ext.
            eassumption.
            apply f_eq_subdomain_extend_not_In_S_r. intros Hc'.
            eapply reachable_in_dom in Hc'. destruct Hc' as [v1' Hget'].
            erewrite alloc_fresh in Hget'; try eassumption.
            discriminate.
            eassumption.
            eassumption. reflexivity. 
            reflexivity.
          + rewrite extend_gss. reflexivity. 
          + simpl. split. rewrite res_equiv_eq; now eauto.
            eapply res_equiv_weakening_alt.
            eapply reach'_closed. now apply Hc1. eassumption.
            eapply heap_env_equiv_preserves_closed. eapply Heq.
            eapply reach'_closed. now apply Hc1. eassumption.
            eapply res_equiv_rename_ext. eassumption.

            eapply f_eq_subdomain_extend_not_In_S_r. intros Hc'.
            eapply reachable_in_dom in Hc'.
            eapply dom_subheap in Hc'; [| eapply def_funs_subheap; now eauto ]. 
            destruct Hc' as [v1' Hget'].
            erewrite alloc_fresh in Hget'; try eassumption.
            discriminate.
            rewrite reach_unfold. simpl.
            eapply well_formed_Union.
            intros l3 b Heq' Hget. inv Heq'. subst_exp. simpl. 
            eapply Included_trans. eassumption. eapply reachable_in_dom.
            eassumption.  eassumption.
            rewrite post_Singleton; try eassumption. eapply well_formed_antimon; try eassumption.
            eapply Included_trans. eapply reach'_set_monotonic. eassumption.
            rewrite <- reach'_idempotent. reflexivity.
            eapply Singleton_Included. now eexists; eauto.
            eapply f_eq_subdomain_antimon; [| eassumption ].
            rewrite reach_unfold. simpl.
            rewrite post_Singleton;  [ | eassumption ].
            eapply Union_Included.
            eapply Singleton_Included. now eexists; eauto.
            eapply reachable_in_dom. eapply well_formed_antimon; [| eassumption ].
            eapply Included_trans. eapply reach'_set_monotonic. eassumption.
            rewrite <- reach'_idempotent. reflexivity.
            eapply Included_trans. eassumption.
            eapply reachable_in_dom. eassumption.
            eassumption. reflexivity. 
            eapply def_funs_subheap; now eauto.
            eapply def_funs_subheap; now eauto.
            eapply Singleton_Included. now eexists; eauto.
            eapply Singleton_Included. now eexists; eauto.
            simpl. rewrite post_Singleton; [ | eassumption ].
            eapply Included_trans. eassumption. reflexivity.
            simpl. rewrite post_Singleton; [ | eassumption ].
            eapply Included_trans. eassumption. reflexivity. }
        { eapply f_eq_subdomain_extend_not_In_S_r. intros Hc'.
          eapply dom_subheap in Hc'; [| eapply def_funs_subheap; now eauto ]. 
          destruct Hc' as [v1' Hget'].
          erewrite alloc_fresh in Hget'; try eassumption.
          discriminate. eassumption. }
        { rewrite <- Union_assoc. rewrite Union_commut.
          eapply well_formed_reach_alloc_in_dom; try eassumption. 
          simpl. rewrite Union_Empty_set_neut_l.
          rewrite Union_commut. eapply def_closures_env_locs_post_reach with (cenv := Loc l1).
          eassumption.
          simpl. rewrite post_Singleton; [| eassumption ].
          eassumption.
          simpl.
          rewrite Union_Empty_set_neut_l. eapply Singleton_Included.
          eexists. erewrite def_funs_subheap; eauto. }
        { rewrite <- Union_assoc. rewrite Union_commut.
          eapply well_formed_reach_alloc_in_dom; try eassumption.
          simpl. rewrite Union_Empty_set_neut_l.
          rewrite Union_commut. eapply def_closures_env_locs_post_reach with (cenv := Loc l2).
          eassumption.
          simpl. rewrite post_Singleton; [| eassumption ].
          eassumption.
          simpl.
          rewrite Union_Empty_set_neut_l. eapply Singleton_Included.
          eexists. erewrite def_funs_subheap; eauto. }
        { eapply Included_trans. eapply env_locs_set_Inlcuded'.
          eapply Union_Included. eapply Singleton_Included.
          eexists. erewrite gas; eauto.
          eapply Included_trans; [| eapply dom_subheap; eapply alloc_subheap; eassumption ].
          eapply Included_trans; [| eassumption ]. 
          eapply env_locs_monotonic. rewrite !Setminus_Union_distr... }
        { eapply Included_trans. eapply env_locs_set_Inlcuded'.
          eapply Union_Included. eapply Singleton_Included.
          eexists. erewrite gas; eauto.
          eapply Included_trans; [| eapply dom_subheap; eapply alloc_subheap; eassumption ].
          eapply Included_trans; [| eassumption ]. 
          eapply env_locs_monotonic. rewrite !Setminus_Union_distr... }
        { eapply injective_subdomain_antimon;
            [| eapply Included_Union_compat;
               [ reflexivity |  now eapply reach'_set_monotonic; eapply env_locs_set_Inlcuded' ] ].
          rewrite <- Union_assoc.
          rewrite Setminus_Union_distr, Setminus_Same_set_Empty_set, Union_Empty_set_neut_l. 
          eapply injective_subdomain_antimon; [| eapply Included_Union_compat;
                                                 [ reflexivity |
                                                   eapply reach'_set_monotonic;
                                                   eapply Included_Union_compat; [ reflexivity |];
                                                   eapply env_locs_monotonic; eapply Setminus_Included ]].
          assert (Hreq : reach' H1' (l1 |: env_locs rho1' (name_in_fundefs B :|: S)) <-->
                         l1 |: reach' H1' (env_locs rho1' (name_in_fundefs B :|: S))). 
          { rewrite reach'_Union. rewrite reach_unfold. rewrite <- Union_assoc. 
            rewrite (Union_Same_set (reach' H1' (post H1' [set l1]))).
            reflexivity. rewrite (reach'_idempotent H1' (env_locs rho1' (name_in_fundefs B :|: S))). 
            eapply reach'_set_monotonic.
            rewrite Union_commut. 
            eapply def_closures_env_locs_post_reach with (cenv := Loc l1). 
            eassumption. simpl. rewrite post_Singleton; eauto. eassumption. }

          rewrite reach'_Union. rewrite reach_unfold. simpl. 
          rewrite post_Singleton; [| erewrite gas; eauto ]. simpl.
          rewrite Union_Empty_set_neut_l, <- !Union_assoc. rewrite <- reach'_Union. 
          rewrite (Union_Same_set [set l1]); [| eapply Included_Union_preserv_r;
                                                eapply Included_trans; [| eapply reach'_extensive ];
                                                now eauto with Ensembles_DB ].
          rewrite <- well_formed_reach_alloc_same; try eassumption.
          
          rewrite Hreq.
          eapply injective_subdomain_extend. eassumption. 
          
          intros Hc'. rewrite !Setminus_Union_distr in Hc'.
          eapply image_Union in Hc'. inv Hc'.
          
          - apply image_monotonic with (S' := [set l1]) in H; try now eauto with Ensembles_DB.
            eapply image_f_eq_subdomain in H; [| eapply f_eq_subdomain_antimon; try eassumption ].
            rewrite image_Singleton in H. inv H.
            eapply alloc_fresh in Ha2. 
            rewrite res_equiv_eq in Hloc. destruct Hloc as [Heqb Hloc].
            unfold id in Heqb; subst. erewrite def_funs_subheap in Ha2. congruence.
            now eauto. eassumption. 
            
            eapply Singleton_Included. now eexists; eauto.
          - eapply heap_env_equiv_image_reach in HBs.
            assert (Hin : (reach' H2' (env_locs rho2' (name_in_fundefs B :|: S))) l2').
            { rewrite image_id in HBs. eapply HBs.
              eapply image_monotonic; try eassumption.
              eapply Included_trans. eapply Setminus_Included. 
              eapply reach'_set_monotonic. eapply env_locs_monotonic... }
            eapply reachable_in_dom in Hin; try eassumption.
            destruct Hin as [v1' Hget1']. erewrite alloc_fresh in Hget1'; eauto.
            discriminate.
          - rewrite Hreq. eapply well_formed_Union; [| eassumption ].
            
            eapply well_formed_subheap; [ | now eapply Singleton_Included; eexists; eauto
                                          | eapply def_funs_subheap; now eauto ].

            intros l1'' b1'' Hin1 Hgetl1. inv Hin1. repeat subst_exp.

            
            eapply Included_trans; [| eapply reachable_in_dom ]; eassumption.
          - eapply Union_Included.

            eapply Singleton_Included.
            eexists. eapply def_funs_subheap. now eauto. eassumption. 
            eassumption. }
    - eexists. simpl in *.
      rewrite !Union_Empty_set_neut_l.
      repeat (split; eauto).
      eapply well_formed'_closed. eapply heap_env_equiv_preserves_closed.
      eassumption.
      eapply reach'_closed; eassumption.

      eapply Included_trans. eapply reach'_extensive. eapply in_dom_closed.
      eapply heap_env_equiv_preserves_closed.
      eassumption.
      eapply reach'_closed; eassumption.
  Qed.


  Lemma heap_env_equiv_def_funs' (S : Ensemble var) (β1 β2 : loc -> loc) (H1 H2 : heap block) 
        (rho1 rho2 : M.t value) (B B' : fundefs) : 
    S \\ (name_in_fundefs B) |- (H1, rho1) ⩪_(β1, β2) (H2, rho2) ->
    S |- (H1, def_funs B B' rho1) ⩪_(β1, β2) (H2, def_funs B B' rho2).
  Proof with now eauto with Ensembles_DB.
    revert S. induction B; simpl; intros S Heq.
    - eapply heap_env_equiv_set.
      + eapply IHB. eapply heap_env_equiv_antimon...
      + rewrite res_equiv_eq. simpl. split; eauto.
    - eapply heap_env_equiv_antimon...
  Qed.
  
  Lemma def_funs_env_loc S rho B B' :
    env_locs (def_funs B B' rho) S \subset env_locs rho (S \\ name_in_fundefs B).
  Proof.
    revert S; induction B; intros S.
    - simpl. eapply Included_trans.
      eapply env_locs_set_Inlcuded'.
      simpl. rewrite Union_Empty_set_neut_l.
      rewrite <- Setminus_Union.
      eapply IHB.
    - simpl. rewrite Setminus_Empty_set_neut_r. reflexivity.
  Qed.

  
    Lemma heap_equiv_compose_l
          (S : Ensemble var) (H1 H2 H3 : heap block) (b1 b2 : loc -> loc) :
       S |- H1 ≃_(b1, id ) H2 ->
       image b1 S |- H2 ≃_( b2, id) H3 ->
       S |- H1 ≃_(b2 ∘ b1, id) H3.
    Proof.
      intros Heq1 Heq2 x Hin.
      unfold compose at 2. simpl.
      unfold id.
      symmetry.
      eapply res_equiv_f_compose with (β4 := id); [| now symmetry; eauto ].
      rewrite compose_id_neut_r.
      symmetry. eapply Heq2. eexists; split; eauto.
    Qed.

    
    Lemma heap_equiv_antimon (S1 S2 : Ensemble var) (H1 H2 : heap block)
          (b1 b2 : loc -> loc) :
      S1 |- H1 ≃_( b1, b2) H2 ->
           S2 \subset S1 ->
           S2 |- H1 ≃_( b1, b2) H2.
    Proof.
      intros Heq Hsub x Hin; eauto.
    Qed. 
    
    Lemma subst_env_image S rho b :
      env_locs (subst_env b rho) S <--> image b (env_locs rho S).
    Proof.
      split; intros x [y [Heq Hin]]; subst.
      - destruct (M.get y _) as [ [l'|] |] eqn:Hget; try contradiction.
        inv Hin. unfold subst_env in *. rewrite M.gmap in Hget.
        destruct (M.get y _) as [ [|] |] eqn:Hget'; try contradiction.
        simpl in Hget. inv Hget. eexists; split; eauto.
        eexists; split; eauto.
        rewrite Hget'. reflexivity.
        simpl in Hget. inv Hget.
        inv Hget. 
      - destruct Heq as [z [Hin Hgetz]].
        destruct (M.get z _) as [ [l'|] |] eqn:Hget; try contradiction.
        inv Hgetz. eexists; split. eauto.
        unfold subst_env. rewrite M.gmap.
        rewrite Hget. reflexivity.
    Qed.

    Lemma heap_env_equiv_heap_equiv_l S rho1 H1 H2 b :
      env_locs rho1 S |- H1 ≃_(b, id) H2 ->
      S |- (H1, rho1) ⩪_(b, id) (H2, subst_env b rho1).
    Proof.
      intros Heq; split; intros x v Hin Hget.
      +  eexists; split; eauto.
         unfold subst_env. rewrite M.gmap. rewrite Hget.  reflexivity.
         destruct v. simpl. eapply Heq.
         eexists; split; eauto. rewrite Hget. reflexivity.
         simpl. rewrite res_equiv_eq. split; eauto.
      + unfold subst_env in *. rewrite M.gmap in Hget.  
        destruct (M.get x rho1) as [[ | ] | ] eqn:Hgetx; inv Hget.
        eexists; split; eauto.
        eapply heap_equiv_symm. eassumption.
        eexists; split; eauto. rewrite Hgetx.
        reflexivity. 
        eexists; split; eauto.
        rewrite res_equiv_eq. split; eauto.
    Qed.


    Lemma heap_env_equiv_respects_f_eq_l rho1 rho2 H1 H2 b d S e e' :

      S |- (H1, subst_env b rho1) ⩪_(e, e') (H2, rho2) ->
      f_eq_subdomain (env_locs rho1 S) b d ->
      S |- (H1, subst_env d rho1) ⩪_(e, e') (H2, rho2).
    Proof. 
      intros Heq; split; intros x v Hin Hget.
      + unfold subst_env in *. rewrite M.gmap in Hget.
        edestruct Heq as [Heq1 Heq2].
         
        destruct (M.get x rho1) as [[ | ] | ] eqn:Hgetx; inv Hget.

        edestruct Heq1 as [z [Hget' Hres]]; try eassumption.
        
        unfold subst_env. rewrite M.gmap. rewrite Hgetx. reflexivity. 
        simpl in *. 
        eexists; split; eauto.
        assert (Hres' := Hres). rewrite res_equiv_eq in Hres.
        destruct z; try contradiction. destruct Hres as [Heq1' _].
        unfold id in *; subst. rewrite <- H. eassumption.
        eexists; split; eauto.
        rewrite Hgetx. reflexivity.

        edestruct Heq1 as [z [Hget' Hres]]; try eassumption.
        unfold subst_env. rewrite M.gmap. rewrite Hgetx. reflexivity. 
        eexists; split; eauto.
      + edestruct Heq as [Heq1 Heq2].
        edestruct Heq2 as [z [Hget' Hres]]; try eassumption.
        unfold subst_env in *. rewrite M.gmap in *.
        destruct (M.get x rho1) as [[ | ] | ] eqn:Hgetx; inv Hget'.
        
        eexists; split. reflexivity.
        simpl. rewrite <- H. eassumption. 
        eexists; split; eauto. rewrite Hgetx. reflexivity.

        edestruct Heq2 as [z [Hget' Hres']]; try eassumption.
        unfold subst_env in *. rewrite M.gmap in *.
        rewrite Hgetx in Hget'. 
        eexists; split; eauto.
    Qed.

    Lemma heap_env_equiv_respects_id rho1 rho2 H1 H2 S e e' :
      S |- (H1, subst_env id rho1) ⩪_(e, e') (H2, rho2) ->
      S |- (H1, rho1) ⩪_(e, e') (H2, rho2).
    Proof. 
      intros Heq; split; intros x v Hin Hget.
      + unfold subst_env in *. eapply Heq. eassumption.
        rewrite M.gmap. rewrite Hget. unfold id, subst_env.
        destruct v; reflexivity.
      + edestruct Heq as [Heq1 Heq2].
        edestruct Heq2 as [z [Hget' Hres]]; try eassumption.
        unfold subst_env in *. rewrite M.gmap in *.
        destruct (M.get x rho1) as [[ | ] | ] eqn:Hgetx; inv Hget'.
        
        eexists; split. reflexivity.
        simpl. eassumption.
        
        edestruct Heq2 as [z [Hget' Hres']]; try eassumption.
        unfold subst_env in *. rewrite M.gmap in *.
        rewrite Hgetx in Hget'. 
        eexists; split; eauto.
    Qed.

    Lemma heap_env_equiv_respects_id_r rho1 rho2 H1 H2 S e e' :
      S |- (H1, rho1) ⩪_(e, e') (H2, rho2) ->
      S |- (H1, subst_env id rho1) ⩪_(e, e') (H2, rho2).
    Proof. 
      intros Heq; split; intros x v Hin Hget.
      + unfold subst_env in *. eapply Heq. eassumption.
        rewrite M.gmap in *.
        destruct (M.get x rho1) as [[ | ] | ] eqn:Hgetx; inv Hget;
        reflexivity. 
      + edestruct Heq as [Heq1 Heq2].
        edestruct Heq2 as [z [Hget' Hres]]; try eassumption.
        unfold subst_env in *. rewrite M.gmap in *.
        
        eexists; split. rewrite Hget'; reflexivity.
        destruct z; eassumption.
    Qed.

    Lemma heap_env_equiv_respects_compose rho1 rho2 H1 H2 S e e' f g :
      S |- (H1, subst_env g (subst_env f rho1)) ⩪_(e, e') (H2, rho2) ->
      S |- (H1, subst_env (g ∘ f) rho1) ⩪_(e, e') (H2, rho2). 
    Proof.
      intros Heq; split; intros x v Hin Hget.
      + unfold subst_env in *. eapply Heq. eassumption.
        rewrite !M.gmap in *.
        destruct (M.get x rho1) as [[ | ] | ] eqn:Hgetx.
        inv Hget. reflexivity. 
        inv Hget. reflexivity. 
        inv Hget.
      + edestruct Heq as [Heq1 Heq2].
        edestruct Heq2 as [z [Hget' Hres]]; try eassumption.
        eexists; split; eauto.
        unfold subst_env in *. rewrite !M.gmap in *.
        destruct (M.get x rho1) as [[ | ] | ] eqn:Hgetx.
        inv Hget'. reflexivity. 
        inv Hget'. reflexivity. 
        inv Hget'.
    Qed.

    Lemma heap_env_equiv_heap_equiv_r S rho1 H1 H2 b d :
      image d (env_locs rho1 S) |- H1 ≃_(b, id) H2 ->
      S |- (H1, subst_env d rho1) ⩪_(b, id) (H2, subst_env (b ∘ d) rho1).
    Proof.
      intros Heq; split; intros x v Hin Hget.
      + unfold subst_env in *. rewrite M.gmap in Hget.
        destruct (M.get x rho1) as [[ | ] | ] eqn:Hgetx; inv Hget.
        
        eexists; split. unfold subst_env in *. rewrite M.gmap.  
        rewrite Hgetx. reflexivity.
        simpl. unfold compose. eapply Heq. eexists; split; eauto.
        eexists; split; eauto. rewrite Hgetx. reflexivity.
        simpl.
        eexists. unfold subst_env in *. rewrite M.gmap.  
        rewrite Hgetx. simpl. split. reflexivity.
        rewrite res_equiv_eq. split; eauto.
      + unfold subst_env in *. rewrite M.gmap in *. 
        destruct (M.get x rho1) as [[ | ] | ] eqn:Hgetx; inv Hget.
        eexists; split; eauto.
        reflexivity.
        simpl. unfold compose. symmetry. eapply Heq.
        eexists. split; eauto. eexists; split; eauto.
        rewrite Hgetx. reflexivity.
        eexists; split; eauto. split; reflexivity.
        rewrite res_equiv_eq. split; eauto.
    Qed.

    Lemma res_equiv_subheap S H1 H1' v :
      well_formed (reach' H1 S) H1 ->
      S \subset dom H1 ->
      val_loc v \subset reach' H1 S ->
      H1 ⊑ H1' ->
      (v, H1) ≈_(id, id) (v, H1').
    Proof.
      intros Hwf Hsub1 Hsub2 Hsub3.
      eapply res_equiv_weakening; try eassumption.
      eapply reach'_closed; eassumption.
      eapply reach'_closed; eassumption.
      reflexivity.
      eapply HL.subheap_refl.
    Qed.

    Lemma heap_env_approx_key_set b1 H1 rho1 b2 H2 rho2 : 
      heap_env_approx (Full_set _) (b1, (H1, rho1)) (b2, (H2, rho2)) ->
      key_set rho1 \subset key_set rho2.
    Proof.
      intros Hap x Hiny. unfold key_set in *.
      unfold In in *. simpl in *. destruct (M.get x rho1) eqn:Hget1; try contradiction.
      edestruct Hap as [l1' [Hr2 Hres1]]; eauto. now constructor.
      now rewrite Hr2.
    Qed.

    Lemma heap_env_equiv_key_set b1 H1 rho1 b2 H2 rho2 : 
      Full_set _ |- (H1, rho1) ⩪_( b1, b2) (H2, rho2) ->
                   key_set rho1 <--> key_set rho2.
    Proof.
      intros [Henv1 Henn2]; split;
        eapply heap_env_approx_key_set; eauto.
    Qed. 

    
End HeapEquiv.

(* Heap equivalence definitions for L6. Part of the CertiCoq project.
 * Author: Zoe Paraskevopoulou, 2016
 *)

From Coq Require Import NArith.BinNat Relations.Relations MSets.MSets
         MSets.MSetRBT Lists.List omega.Omega Sets.Ensembles Relations.Relations
         Classes.Morphisms.
From ExtLib Require Import Structures.Monad Data.Monads.OptionMonad Core.Type.
From CertiCoq.L6 Require Import cps cps_util set_util eval List_util Ensembles_util functions
        identifiers Heap.heap tactics Heap.heap_defs.
Require Import compcert.lib.Coqlib.

Import ListNotations.

Open Scope Ensembles_scope.

Module HeapEquiv (H : Heap).

  Module Defs := HeapDefs H.

  Import H Defs.HL Defs.

  (** Syntactic approximation of results with fuel *)
  Fixpoint res_approx_fuel (n : nat) (r1 : (loc -> loc) * res) (r2 : (loc -> loc) * res) : Prop :=
    let '(b1, (v1, H1)) := r1 in
    let '(b2, (v2, H2)) := r2 in
    match v1, v2 with
      | Loc l1, Loc l2 =>
        match get l1 H1 with
          | Some (Constr c vs1) =>
            b2 l2 = b1 l1 /\
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
            b2 l2 = b1 l1 /\
            exists v1' v2',
              get l2 H2 = Some (Clos v1' v2') /\
              forall i, (i < n)%nat ->
                   match n with
                     | 0%nat => True
                     | S n' =>
                       res_approx_fuel (n' - (n'-i)) (b1, (v1, H1)) (b2, (v1', H2)) /\
                       res_approx_fuel (n' - (n'-i)) (b1, (v2, H1)) (b2, (v2', H2))
                   end
          | Some (Env rho1) =>
            b2 l2 = b1 l1 /\
            exists rho2,
              get l2 H2 = Some (Env rho2) /\
              (forall x,  (exists v1 v2, M.get x rho1 = Some v1 /\
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
  
  Definition heap_approx (S : Ensemble loc) p1 p2 : Prop :=
    let '(b1, H1) := p1 in
    let '(b2, H2) := p2 in
    forall bl1 l, l \in S -> get l H1 = Some bl1 ->
             b1 l = b2 l /\ 
             exists bl2, get l H2 = Some bl2 /\ block_equiv (b1, H1, bl1) (b2, H2, bl2).
  
  Definition heap_equiv (S : Ensemble loc) p1 p2 : Prop :=
    heap_approx S p1 p2 /\ heap_approx S p2 p1. 
  
  Notation  "S |- H1 ≃_( b1 , b2 ) H2" := (heap_equiv S (b1, H1) (b2, H2))
                                            (at level 70, no associativity).
  
  (** Equivalent definition, unfolding the recursion *)
  Definition res_approx_fuel' (n : nat) r1 r2 : Prop :=
    let '(b1, (v1, H1)) := r1 in
    let '(b2, (v2, H2)) := r2 in
    match v1, v2 with
      | Loc l1, Loc l2 =>
        match get l1 H1 with
          | Some (Constr c vs1) =>
            b1 l1 = b2 l2 /\
            exists vs2, 
              get l2 H2 = Some (Constr c vs2) /\
              forall i, (i < n)%nat ->
                   Forall2 (fun l1 l2 => res_approx_fuel i (b1, (l1, H1)) (b2, (l2, H2))) vs1 vs2
          | Some (Clos v1 v2) =>
            b1 l1 = b2 l2 /\
            exists v1' v2',
              get l2 H2 = Some (Clos v1' v2') /\
              forall i, (i < n)%nat ->
                   res_approx_fuel i (b1, (v1, H1)) (b2, (v1', H2)) /\
                   res_approx_fuel i (b1, (v2, H1)) (b2, (v2', H2))
          | Some (Env rho1) =>
            b1 l1 = b2 l2 /\
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
        match get l1 H1, get l2 H2 with
          | Some bl1, Some bl2 => b1 l1 = b2 l2 /\ 
                                 block_equiv (b1, H1, bl1) (b2, H2, bl2)
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
        rewrite Hget1, Hget2; eauto.
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


  (** Using S as the set of roots, garbage collect H1 *) 
  Definition collect (S : Ensemble loc) (H1 H2 : heap block) : Prop :=
    size_heap H2 <= size_heap H1 /\
    exists β,
      S |- H1 ≃_(β, id) H2 /\ (* locations outside S might be renamed! *)
      injective_subdomain (reach' H1 S) β.
  
  (** [live S H1 H2] iff H2 is the live portion of H1, using S as roots *)
  Definition live (S : Ensemble loc) {_ : ToMSet S} (H1 H2 : heap block) : Prop :=
    size_heap H2 = size_reachable S H1 /\ (* maybe could be derived? *)
    exists β,
      S |- H1 ≃_(β, id) H2 /\ (* locations outside S might be renamed! *)
      injective_subdomain (reach' H1 S) β.
  
  (** * Lemmas about [collect] *)
  
  (** The reachable part of the heap before and after collection are the same *)
  Lemma collect_heap_eq S H1 H2 :
    collect S H1 H2 ->
    exists β,
      S |- H1 ≃_(β, id) H2 /\
      injective_subdomain (reach' H1 S) β.
  Proof.
    firstorder.
  Qed.
  
  Lemma collect_size S H1 H2 :
    collect S H1 H2 ->
    size_heap H2 <= size_heap H1.
  Proof.
    now firstorder.
  Qed.
  

  (** * Lemmas about [reach_size] *)

(*
  Lemma size_reach_heap_eq (S : Ensemble loc) (H1 H1' : heap block) (m : nat) :
    reach' H1 S |- H1 ≡ H1' ->
    size_reach H1 S m ->
    size_reach H1' S m.
  Proof.
    intros Heq Hs H2 Hl. eapply Hs.
    eapply live_heap_eq; eauto. rewrite <- reach'_heap_eq; eauto.
    now symmetry.
  Qed.
 *)

  (** * Lemmas about [res_approx] and [res_equiv] *)

  (** Preorder and equivalence properties of [res_approx] and [res_equiv] *)

  Lemma heap_equiv_res_approx (S : Ensemble loc) (β1 β2 : loc -> loc)
        (H1 H2 : heap block)
        (v : value) (n : nat) :
    S |- H1 ≃_(β1, β2) H2  ->
    (val_loc v) \subset S -> 
    res_approx_fuel n (β1, (v, H1)) (β2, (v, H2)).
  Proof.
    intros [Heq1 Heq2] Hin.
    destruct v as [l | B f]; rewrite res_approx_fuel_eq; [| now split; eauto ].
    simpl; destruct (get l H1) eqn:Hget; eauto.
    assert (Hget' := Hget). eapply Heq1 in Hget; eauto.
    destruct Hget as [Heqb [b2 [Hget2 Heq]]].
    destruct b; destruct b2; try contradiction.
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
    - eapply Hin. reflexivity.
  Qed.
  
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
            congruence. }
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
  
  Instance Equivalence_heap_equiv S : Equivalence (heap_equiv S). 
  Proof.
    constructor.
    - intros [b H].
      split; intros x l Hin Hget;
      split; eexists; split; eauto; reflexivity.
    - intros [b1 H1] [b2 H2] [Hs1 Hs2].
      split; intros x l Hin Hget. 
      edestruct (Hs2 x l Hin Hget) as [Heq1' [b1' [Hget1 Heq1]]]. 
      split; eauto.
      edestruct (Hs1 x l Hin Hget) as [Heq2' [b1' [Hget1 Heq1]]]. 
      split; eauto.
    - intros [b1 H1] [b2 H2] [b3 H3] [Hs1 Hs2] [Hs2' Hs3].
      split; intros x l Hin Hget. 
      edestruct (Hs1 x l Hin Hget) as [Heq1' [b1' [Hget1 Heq1]]]. 
      edestruct (Hs2' _ _ Hin Hget1) as [Heq2' [b2' [Hget2 Heq2]]].
      split. congruence. eexists; split; eauto.
      now eapply Transitive_block_equiv; eauto.
      edestruct (Hs3 x l Hin Hget) as [Heq1' [b1' [Hget1 Heq1]]]. 
      edestruct (Hs2 _ _ Hin Hget1) as [Heq2' [b2' [Hget2 Heq2]]].
      split. congruence. eexists; split; eauto. eapply Transitive_block_equiv; eauto.
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
    - eapply Heq1 in Heq.
      destruct Heq as [Heq1' [b2' [Hb2 Heqb]]]. rewrite Hb2.
      simpl in Heqb. destruct b; destruct b2'; try contradiction.
      destruct Heqb as [Heqc Hall]; subst; split; eauto; split; eauto.
      eapply Forall2_symm_strong; [| eassumption ].
      simpl; intros.
      now eapply Equivalence.equiv_symmetric; eauto.
      destruct Heqb as [Hb'1 Hb'2].
      split; eauto. split; now symmetry; eauto.
      split; eauto. now symmetry; eauto.
      eapply get_In_env_locs; eauto.
      reflexivity.
    - destruct (get l H2) eqn:HgetH2; eauto.
      eapply Heq2 in HgetH2.
      destruct HgetH2 as [_ [b2' [Hgetb2 _]]].
      congruence.
      eexists; split; eauto. rewrite Hget; eauto. reflexivity.
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


  (** Heap equivalences respect function extensionality *)

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
      + simpl; eauto.
    -  revert b1 b1' r1' H1' b2' r2' H2' Heq2.
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
  
  Instance Proper_heap_approx_f_eq_l : Proper (eq ==> RelProd f_eq eq ==> eq ==> iff) heap_approx.
  Proof. 
    intros s1 s2 hseq [b1 H1] [b2 H2] [Heq1 Heq2] [b1' H1'] [b2' H2'] Heq'; inv Heq'.
    compute in Heq2. subst.
    split.
    intros Ha bl l Hin Hget. edestruct Ha as [Heqb [bl2 [Hget2 Hbeq]]]; eauto.
    split; eauto. rewrite <- Heq1. eassumption.
    eexists; split; eauto.
    assert (Heq : ((f_eq * eq) * eq)%signature ((b1, H2), bl) ((b2, H2), bl)) by (split; eauto).
    rewrite <- Heq. eassumption.
    intros Ha bl l Hin Hget. edestruct Ha as [Heqb [bl2 [Hget2 Hbeq]]]; eauto.
    split; eauto. rewrite Heq1. eassumption.
    eexists; split; eauto.
    assert (Heq : ((f_eq * eq) * eq)%signature ((b1, H2), bl) ((b2, H2), bl)) by (split; eauto).
    rewrite Heq. eassumption.
  Qed.

  Instance Proper_heap_approx_f_eq_r : Proper (eq ==> eq ==> RelProd f_eq eq ==> iff) heap_approx.
  Proof. 
    intros s1 s2 hseq [b1 H1] [b2 H2] Heq' [b1' H1'] [b2' H2'] [Heq1 Heq2]; inv Heq'.
    compute in Heq2. subst.
    split.
    intros Ha bl l Hin Hget. edestruct Ha as [Heqb [bl2 [Hget2 Hbeq]]]; eauto.
    split; eauto. rewrite <- Heq1. eassumption.
    eexists; split; eauto.
    assert (Heq : ((f_eq * eq) * eq)%signature ((b1', H2'), bl2) ((b2', H2'), bl2)) by (split; eauto).
    rewrite  <- Heq. eassumption.
    intros Ha bl l Hin Hget. edestruct Ha as [Heqb [bl2 [Hget2 Hbeq]]]; eauto.
    split; eauto. rewrite Heq1. eassumption.
    eexists; split; eauto.
    assert (Heq : ((f_eq * eq) * eq)%signature ((b1', H2'), bl2) ((b2', H2'), bl2)) by (split; eauto).
    rewrite Heq. eassumption.
  Qed.

  Instance Proper_heap_equiv_f_eq_r : Proper (eq ==> eq ==> RelProd f_eq eq ==> iff) heap_equiv.
  Proof. 
    intros s1 s2 hseq [b1 H1] [b2 H2] Heq' [b1' H1'] [b2' H2'] Heq. inv Heq'.
    split. intros [Ha1 Ha2]. split; rewrite <- Heq; eassumption.
    intros [Ha1 Ha2]. split; rewrite Heq; eassumption.
  Qed.

  Instance Proper_heap_equiv_f_eq_l : Proper (eq ==> RelProd f_eq eq ==> eq ==> iff) heap_equiv.
  Proof. 
    intros s1 s2 hseq [b1 H1] [b2 H2] Heq' [b1' H1'] [b2' H2'] Heq. inv Heq.
    split. intros [Ha1 Ha2]. split; rewrite <- Heq'; eassumption.
    intros [Ha1 Ha2]. split; rewrite Heq'; eassumption.
  Qed.

  (** Horizontal composition of injections *)
  
  Lemma res_approx (S : Ensemble loc) (β1 β2 β1' β2' : loc -> loc)
        (H1 H2 : heap block)
        (v : value) (n : nat) :
    S |- H1 ≃_(β1, β2) H2  ->
    (val_loc v) \subset S -> 
    res_approx_fuel n (β1, (v, H1)) (β2, (v, H2)).
  Proof.
    intros [Heq1 Heq2] Hin.
    destruct v as [l | B f]; rewrite res_approx_fuel_eq; [| now split; eauto ].
    simpl; destruct (get l H1) eqn:Hget; eauto.
    assert (Hget' := Hget). eapply Heq1 in Hget; eauto.
    destruct Hget as [Heqb [b2 [Hget2 Heq]]].
    destruct b; destruct b2; try contradiction.
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
    - eapply Hin. reflexivity.
  Qed.
    
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
    split; intros [h1 h2].
    split; intros b l HIn; eauto; [eapply h1 | eapply h2]; eapply hseq; eassumption.
    split; intros b l HIn; eauto; [eapply h1 | eapply h2]; eapply hseq; eassumption.
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

  (* TODO move *)
  Lemma In_Union_list {A} (l : list (Ensemble A)) s:
    List.In s l ->
    s \subset Union_list l.
  Proof.
    intros Hin. induction l. 
    - now inv Hin.
    - inv Hin. now eapply Included_Union_l.
      simpl. eapply Included_Union_preserv_r.
      eapply IHl; eauto.
  Qed.

      
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
    f_eq_subdomain (dom H1 :&: reach' H1 (val_loc v1)) β1 β1' ->
    f_eq_subdomain (dom H2 :&: reach' H2 (val_loc v2)) β2 β2' ->
    res_approx_fuel' i (β1', (v1, H1)) (β2', (v2, H2)).
  Proof with (now eauto with Ensembles_DB).
    revert v1 v2.
    induction i as [i IHk] using lt_wf_rec1; intros v1 v2 Hres Hfeq Hfeq'.
    destruct v1 as [l1 | B1 f1]; destruct v2 as [l2 | B2 f2].
    simpl in Hres; simpl; destruct (get l1 H1) as [b1 |] eqn:Hget; eauto.
    destruct b1.
    - destruct Hres as [Heqb [vs2 [Hget2 Hi]]].
      split.
      + rewrite <- Hfeq, <- Hfeq'. eassumption.
        split. now eexists; eauto.
        now eapply reach'_extensive.
        split. now eexists; eauto.
        now eapply reach'_extensive.
      + eexists. split; eauto.
        intros i' Hi'.
        eapply Forall2_monotonic_strong; eauto.
        intros x1 x2 Hl1 Hl2 Hres. simpl in Hres.
        rewrite res_approx_fuel_eq in *. eapply IHk.
        eassumption. eassumption. 

        eapply f_eq_subdomain_antimon; [| eassumption ].
        eapply Included_Intersection_compat. reflexivity.
        rewrite (reach_unfold H1 (val_loc (Loc l1))).
        eapply Included_Union_preserv_r. eapply reach'_set_monotonic.
        simpl; rewrite post_Singleton; [| eassumption ]. simpl.
        eapply In_Union_list. eapply in_map. eassumption.

        eapply f_eq_subdomain_antimon; [| eassumption ].
        eapply Included_Intersection_compat. reflexivity.
        rewrite (reach_unfold H2 (val_loc (Loc l2))).
        eapply Included_Union_preserv_r. eapply reach'_set_monotonic.
        simpl; rewrite post_Singleton; [| eassumption ]. simpl.
        eapply In_Union_list. eapply in_map. eassumption.
        
    - destruct Hres as [Heq1 [Heqb [vs2 [Hget2 Hi]]]].
      split.
      + rewrite <- Hfeq, <- Hfeq'. eassumption.
        split. now eexists; eauto.
        now eapply reach'_extensive.
        split. now eexists; eauto.
        now eapply reach'_extensive.
      + do 2 eexists. split. eassumption.
        setoid_rewrite res_approx_fuel_eq in Hi.
        intros i' Hi'. split.
        rewrite res_approx_fuel_eq in *. eapply IHk; try eassumption.
        eapply Hi. eassumption.

        eapply f_eq_subdomain_antimon; [| eassumption ].
        eapply Included_Intersection_compat. reflexivity.
        rewrite (reach_unfold H1 (val_loc (Loc l1))).
        eapply Included_Union_preserv_r. eapply reach'_set_monotonic.
        simpl; rewrite post_Singleton; [| eassumption ]...

        eapply f_eq_subdomain_antimon; [| eassumption ].
        eapply Included_Intersection_compat. reflexivity.
        rewrite (reach_unfold H2 (val_loc (Loc l2))).
        eapply Included_Union_preserv_r. eapply reach'_set_monotonic.
        simpl; rewrite post_Singleton; [| eassumption ]...

        rewrite res_approx_fuel_eq in *. eapply IHk; try eassumption.
        eapply Hi. eassumption.

        eapply f_eq_subdomain_antimon; [| eassumption ].
        eapply Included_Intersection_compat. reflexivity.
        rewrite (reach_unfold H1 (val_loc (Loc l1))).
        eapply Included_Union_preserv_r. eapply reach'_set_monotonic.
        simpl; rewrite post_Singleton; [| eassumption ]...

        eapply f_eq_subdomain_antimon; [| eassumption ].
        eapply Included_Intersection_compat. reflexivity.
        rewrite (reach_unfold H2 (val_loc (Loc l2))).
        eapply Included_Union_preserv_r. eapply reach'_set_monotonic.
        simpl; rewrite post_Singleton; [| eassumption ]...

    - destruct Hres as [Heq1 [rho2 [Hget2 Hx]]].
      split.
      + rewrite <- Hfeq, <- Hfeq'. eassumption.
        split. now eexists; eauto.
        now eapply reach'_extensive.
        split. now eexists; eauto.
        now eapply reach'_extensive.
      + eexists. split; eauto. intros x.
        destruct (Hx x) as [[v1 [v2 [Hgetx1 [Hgetx2 Hi]]]] | Hgetx ]; eauto.
        left. repeat eexists; eauto. intros i' Hi'. 
        rewrite res_approx_fuel_eq in *. eapply IHk; try eassumption.
        setoid_rewrite res_approx_fuel_eq in Hi.
        eapply Hi.  eassumption.

        eapply f_eq_subdomain_antimon; [| eassumption ].
        eapply Included_Intersection_compat. reflexivity.
        rewrite (reach_unfold H1 (val_loc (Loc l1))).
        eapply Included_Union_preserv_r. eapply reach'_set_monotonic.
        simpl; rewrite post_Singleton; [| eassumption ]. simpl.
        eapply get_In_env_locs; eauto. constructor.

        eapply f_eq_subdomain_antimon; [| eassumption ].
        eapply Included_Intersection_compat. reflexivity.
        rewrite (reach_unfold H2 (val_loc (Loc l2))).
        eapply Included_Union_preserv_r. eapply reach'_set_monotonic.
        simpl; rewrite post_Singleton; [| eassumption ]. simpl.
        eapply get_In_env_locs; eauto. constructor.
    - firstorder.
    - firstorder.
    - firstorder.
  Qed. 


  Lemma res_equiv_rename_ext β1 β1' β2 β2' H1 H2 v1 v2 : 
    (v1, H1) ≈_(β1, β2) (v2, H2) ->
    f_eq_subdomain (dom H1 :&: reach' H1 (val_loc v1)) β1 β1' ->
    f_eq_subdomain (dom H2 :&: reach' H2 (val_loc v2)) β2 β2' ->
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
    f_eq_subdomain (dom H1 :&: reach' H1 (env_locs rho1 S)) β1 β1' ->
    f_eq_subdomain (dom H2 :&: reach' H2 (env_locs rho2 S)) β2 β2' ->
    heap_env_approx S (β1', (H1, rho1)) (β2', (H2, rho2)).
  Proof.
    intros Hap Heq1 Heq2 x l Hin Hget.  
    edestruct Hap as [l' [Hgetl' Hres]]; eauto.
    eexists; split; eauto.
    eapply res_equiv_rename_ext; eauto.

    eapply f_eq_subdomain_antimon; [| eassumption ].
    eapply Included_Intersection_compat. reflexivity.
    eapply reach'_set_monotonic. 
    now eapply get_In_env_locs; eauto.

    eapply f_eq_subdomain_antimon; [| eassumption ].
    eapply Included_Intersection_compat. reflexivity.
    eapply reach'_set_monotonic. 
    now eapply get_In_env_locs; eauto.
  Qed.

  Corollary heap_env_equiv_rename_ext S β1 β1' β2 β2' H1 H2 rho1 rho2 : 
    S |- (H1, rho1) ⩪_(β1, β2) (H2, rho2) ->
    f_eq_subdomain (dom H1 :&: reach' H1 (env_locs rho1 S)) β1 β1' ->
    f_eq_subdomain (dom H2 :&: reach' H2 (env_locs rho2 S)) β2 β2' ->
    S |- (H1, rho1) ⩪_(β1', β2') (H2, rho2).
  Proof.
    intros [Heq1 Heq2] Hfeq1 Hfeq2; split. 
    now eapply heap_env_approx_rename_ext; eauto.
    now eapply heap_env_approx_rename_ext; eauto.
  Qed.

  Lemma block_equiv_rename_ext β1 β1' β2 β2' H1 H2 b1 b2 : 
    block_equiv (β1, H1, b1) (β2, H2, b2) ->
    f_eq_subdomain (dom H1 :&: reach' H1 (locs b1)) β1 β1' ->
    f_eq_subdomain (dom H2 :&: reach' H2 (locs b2)) β2 β2' ->
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
      eapply Included_Intersection_compat. reflexivity.
      eapply reach'_set_monotonic.
      eapply In_Union_list. eapply in_map. eassumption.

      eapply f_eq_subdomain_antimon; [| eassumption ].
      eapply Included_Intersection_compat. reflexivity.
      eapply reach'_set_monotonic.
      eapply In_Union_list. eapply in_map. eassumption.

    - destruct Hb1 as [Hb1 Hb2]. split.
      
      eapply res_equiv_rename_ext; eauto.

      eapply f_eq_subdomain_antimon; [| eassumption ].
      eapply Included_Intersection_compat. reflexivity.
      eapply reach'_set_monotonic...

      eapply f_eq_subdomain_antimon; [| eassumption ].
      eapply Included_Intersection_compat. reflexivity.
      eapply reach'_set_monotonic...

      eapply res_equiv_rename_ext; eauto.

      eapply f_eq_subdomain_antimon; [| eassumption ].
      eapply Included_Intersection_compat. reflexivity.
      eapply reach'_set_monotonic...

      eapply f_eq_subdomain_antimon; [| eassumption ].
      eapply Included_Intersection_compat. reflexivity.
      eapply reach'_set_monotonic...

    - eapply heap_env_equiv_rename_ext; eauto.
  Qed.

  Lemma heap_approx_rename_ext S β1 β1' β2 β2' H1 H2 :
    heap_approx S (β1, H1) (β2, H2) ->
    f_eq_subdomain (dom H1 :&: reach' H1 S) β1 β1' ->
    f_eq_subdomain (dom H2 :&: reach' H2 S) β2 β2' ->
    heap_approx S (β1', H1) (β2', H2).
  Proof.
    intros Hap1 Heq1 Heq2 b l Hin Hget.
    edestruct Hap1 as [Heqb [bl2 [Hget2 Hbl]]]; eauto.
    split; eauto.
    rewrite <- Heq1, <- Heq2. eassumption. 

    split. now eexists; eauto.
    now eapply reach'_extensive.

    split. now eexists; eauto.
    now eapply reach'_extensive.

    eexists; split; eauto.

    eapply block_equiv_rename_ext; eauto.

    eapply f_eq_subdomain_antimon; [| eassumption ].
    eapply Included_Intersection_compat. reflexivity.
    rewrite (reach_unfold H1 S). eapply Included_Union_preserv_r.
    eapply reach'_set_monotonic. intros x Hin'. now repeat eexists; eauto.

    eapply f_eq_subdomain_antimon; [| eassumption ].
    eapply Included_Intersection_compat. reflexivity.
    rewrite (reach_unfold H2 S). eapply Included_Union_preserv_r.
    eapply reach'_set_monotonic. intros x Hin'. now repeat eexists; eauto.
  Qed. 
    
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
  
  Lemma heap_env_equiv_setlist S β1 β2 H1 H2 xs ls1 ls2 rho1 rho2 rho1' rho2' :
    Setminus _ S (FromList xs) |- (H1, rho1) ⩪_(β1, β2) (H2, rho2) ->
    setlist xs ls1 rho1 = Some rho1' -> setlist xs ls2 rho2 = Some rho2' ->
    Forall2 (fun l1 l2 => (l1, H1) ≈_(β1, β2) (l2, H2)) ls1 ls2  ->
    S |- (H1, rho1') ⩪_(β1, β2) (H2, rho2').
  Proof with (now eauto with Ensembles_DB).
    revert S rho1' rho2' ls1 ls2; induction xs;
    intros S  rho1' rho2' ls1 ls2 Heq Hs1 Hs2 Hall.
    - destruct ls1; destruct ls2; try discriminate. inv Hs1; inv Hs2; eauto.
      rewrite FromList_nil, Setminus_Empty_set_neut_r in Heq. eassumption.
    - destruct ls1; destruct ls2; try discriminate.
      inv Hall. simpl in Hs1, Hs2.
      destruct (setlist xs ls1 rho1) eqn:Hset1; try discriminate.
      destruct (setlist xs ls2 rho2) eqn:Hset2; try discriminate.
      inv Hs1; inv Hs2. eapply heap_env_equiv_set; eauto.
      eapply IHxs; eauto. eapply heap_env_equiv_antimon; eauto.
      rewrite FromList_cons...
  Qed.
  
  Lemma heap_env_equiv_def_funs_l S S1 S2 β1 H1 H2 rho1 rho2 clo_rho1 clo_rho2 B B0 l1 l2 :
    closed S1 H1 -> closed S2 H2 ->
    env_locs rho1 (Setminus _ S (name_in_fundefs B)) \subset S1 ->
    env_locs rho2 (Setminus _ S (name_in_fundefs B)) \subset S2 ->
    get l1 H1 = Some (Env clo_rho1) ->
    get l2 H2 = Some (Env clo_rho2) ->
    env_locs clo_rho1 (Full_set _) \subset S1 ->
    env_locs clo_rho2 (Full_set _) \subset S2 ->
    (occurs_free_fundefs B0) \subset (Setminus _ S (name_in_fundefs B)) ->
    (Loc l1, H1) ≈_(β1, id) (Loc l2, H2) ->             
    Setminus _ S (name_in_fundefs B) |- (H1, rho1) ⩪_(β1, id) (H2, rho2) ->
    (exists β1', S |- (def_closures B B0 rho1 H1 l1) ⩪_(β1', id) (def_closures B B0 rho2 H2 l2) /\
                f_eq_subdomain (dom H1) β1 β1').
  Proof with (now eauto with Ensembles_DB).
    revert S rho1 rho2; induction B;
    intros S rho1 rho2 Hc1 Hc2 Hinl1 Hinl2 He1 He2 Hg1 Hg2 Hsub Hloc Heq; simpl; eauto.
    - destruct (def_closures B B0 rho1 H1 l1) as [H1' rho1'] eqn:Hd1.
      destruct (def_closures B B0 rho2 H2 l2) as [H2' rho2'] eqn:Hd2.
      destruct (alloc (Clos (FunPtr B0 v) (Loc l1)) _) as [l1' H1''] eqn:Ha1.
      destruct (alloc (Clos (FunPtr B0 v) (Loc l2)) _) as [l2' H2''] eqn:Ha2.
      edestruct (def_funs_exists_new_set (S \\ [set v]) S1 H1 H1' rho1 rho1' clo_rho1 B) as [S1' [HsubS1 [Hcl1 Henv1]]]; eauto.
      eapply Included_trans; [| now apply Hinl1 ]. simpl. rewrite <- !Setminus_Union...
      edestruct (def_funs_exists_new_set (S \\ [set v]) S2 H2 H2' rho2 rho2' clo_rho2 B) as [S2' [HsubS2 [Hcl2 Henv2]]]; eauto.
      eapply Included_trans; [| now apply Hinl2 ]. simpl. rewrite <- !Setminus_Union...
      simpl in Heq, Hinl1, Hinl2. rewrite <- !Setminus_Union in Heq, Hinl1, Hinl2.

      edestruct IHB as [β1' [HBs Heqf]]; try eassumption.
      eapply Included_trans; [ eassumption |]. simpl. rewrite <- !Setminus_Union...

      eexists (β1' {l1' ~> l2'}). split.
      { eapply heap_env_equiv_alloc_alt; (try now apply Ha1); (try now apply Ha2); eauto.
        + simpl. rewrite Union_Empty_set_neut_l.
          eapply Singleton_Included. eapply dom_subheap.
          eapply def_funs_subheap. now eauto. now eexists; eauto.
        + simpl. rewrite Union_Empty_set_neut_l.
          eapply Singleton_Included. eapply dom_subheap.
          eapply def_funs_subheap. now eauto. now eexists; eauto.
        + simpl. rewrite Union_Empty_set_neut_l.
          rewrite post_Singleton; [| eapply def_funs_subheap; now eauto ].
          eapply Included_trans...
        + simpl. rewrite Union_Empty_set_neut_l.
          rewrite post_Singleton; [| eapply def_funs_subheap; now eauto ].
          eapply Included_trans...
        + eapply heap_env_equiv_rename_ext with (β1 := β1') (β2 := id).
          rewrite Hd1, Hd2 in HBs. eassumption.
          
          eapply f_eq_subdomain_extend_not_In_S_r. intros Hc.
          eapply Included_Intersection_l in Hc. destruct Hc as [v1' Hget'].
          erewrite alloc_fresh in Hget'; try eassumption.
          discriminate.
          
          reflexivity. reflexivity.
        + rewrite extend_gss. reflexivity.
        + simpl. split. rewrite res_equiv_eq; now eauto.
          eapply res_equiv_weakening_alt.
          now apply Hc1. now apply Hc2.
          
          eapply res_equiv_rename_ext. eassumption.
          
          eapply f_eq_subdomain_extend_not_In_S_r. intros Hc.
          eapply Included_Intersection_l in Hc.
          eapply dom_subheap in Hc; [| eapply def_funs_subheap; now eauto ]. 
          destruct Hc as [v1' Hget'].
          erewrite alloc_fresh in Hget'; try eassumption.
          discriminate.

          eapply f_eq_subdomain_antimon; [| eassumption ].
          eapply Included_Intersection_l.

          reflexivity.
          
          now eapply def_funs_subheap; eauto.
          now eapply def_funs_subheap; eauto.
          eapply Singleton_Included. now eexists; eauto.
          eapply Singleton_Included. now eexists; eauto.
          simpl. rewrite post_Singleton; [ | eassumption ].
          eassumption. 
          simpl. rewrite post_Singleton; [ | eassumption ].
          eassumption. }

      { eapply f_eq_subdomain_extend_not_In_S_r. intros Hc.
        eapply dom_subheap in Hc; [| eapply def_funs_subheap; now eauto ]. 
        destruct Hc as [v1' Hget'].
        erewrite alloc_fresh in Hget'; try eassumption.
        discriminate. eassumption. }
    - simpl. rewrite Setminus_Empty_set_neut_r in Heq.
      eexists. split. eassumption. reflexivity.
  Qed.
 
  
  Lemma res_equiv_get_Constr β1 β2 (H1 H2 : heap block)
        (l1 l2 : loc) (c : cTag) (vs1 : list value) :
    (Loc l1, H1) ≈_(β1, β2) (Loc l2, H2) ->
    get l1 H1 = Some (Constr c vs1) ->
    exists vs2,
      get l2 H2 = Some (Constr c vs2) /\
      Forall2 (fun v1 v2 => (v1, H1) ≈_(β1, β2) (v2, H2)) vs1 vs2.
  Proof.
    intros Hres Hget. 
    rewrite res_equiv_eq in Hres. simpl in Hres. rewrite Hget in Hres.
    destruct (get l2 H2); try contradiction.
    destruct Hres as [Heqb Hres].
    destruct b; try contradiction. 
    destruct Hres as [Heq Hb]. subst. eexists; split; eauto. 
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
  
  Lemma heap_env_equiv_env_getlist (S : Ensemble var) β1 β2 (H1 H2 : heap block)
        (rho1 rho2 : env) (xs : list var) (ls : list value) :
    getlist xs rho1 = Some ls ->
    S |- (H1, rho1) ⩪_(β1, β2) (H2, rho2) ->
    (FromList xs) \subset S ->
    exists ls',
      getlist xs rho2 = Some ls' /\
      Forall2 (fun l l' => (l, H1) ≈_(β1, β2) (l', H2)) ls ls'.
  Proof with now eauto with Ensembles_DB.
    revert ls; induction xs; intros ls Hget Heq Hin.
    - inv Hget.
      eexists; split; eauto. reflexivity.
    - simpl in Hget.
      destruct (M.get a rho1) as [l1 | ] eqn:Hgetl1; try discriminate.
      destruct (getlist xs rho1) as [ls1 | ] eqn:Hetls1; try discriminate.
      inv Hget.
      edestruct heap_env_equiv_env_get as [l2 [Hgetl2 Heq']]; eauto.
      eapply Hin. rewrite FromList_cons...
      edestruct IHxs as [ls2 [Hgetls2 Hall2]]; eauto.
      eapply Included_trans; try eassumption. 
      rewrite FromList_cons...
      eexists; split. simpl. rewrite Hgetl2, Hgetls2.
      reflexivity. constructor; eauto.
  Qed.
  

  Lemma heap_env_equiv_getlist_Forall2 S β1 β2 H1 H2 ys vs1 vs2 rho1 rho2 :
    S |- (H1, rho1) ⩪_(β1, β2) (H2, rho2) ->
    FromList ys \subset S ->
    getlist ys rho1 = Some vs1 ->
    getlist ys rho2 = Some vs2 ->
    Forall2 (fun l1 l2 => (l1, H1) ≈_(β1, β2) (l2, H2)) vs1 vs2.
  Proof.
    revert vs1 vs2; induction ys; intros vs1 vs2 Heq Hin Hg1 Hg2;
    destruct vs1; destruct vs2; simpl in *; try discriminate; try now constructor.
    - destruct (M.get a rho1) eqn:Heqa;
      destruct (getlist ys rho1) eqn:Heqys; try discriminate.
    - destruct (M.get a rho2) eqn:Heqa;
      destruct (getlist ys rho2) eqn:Heqys; try discriminate.
    - rewrite FromList_cons in Hin.
      destruct (M.get a rho1) eqn:Heqa;
        destruct (getlist ys rho1) eqn:Heqys; try discriminate. inv Hg1.
      eapply Heq in Heqa. destruct Heqa as [l' [Hget Heq']].
      rewrite Hget in Hg2.
      destruct (getlist ys rho2) eqn:Heqys'; try discriminate. inv Hg2.
      constructor; eauto. eapply IHys; eauto.
      eapply Included_trans; now eauto with Ensembles_DB.
      eapply Included_trans; now eauto with Ensembles_DB.
  Qed.
  
  Lemma block_equiv_Constr β1 β2 (H1 H2 : heap block) (c : cTag) (vs vs' : list value) :
    Forall2 (fun l1 l2 => (l1, H1) ≈_(β1, β2) (l2, H2)) vs vs' ->
    block_equiv (β1, H1, Constr c vs) (β2, H2, Constr c vs').
  Proof.
    simpl; split; eauto.
  Qed.
  
  Lemma block_equiv_Fun β1 β2 (H1 H2 : heap block) (rho1 rho2 : env) :
    Full_set _ |- (H1, rho1) ⩪_(β1, β2) (H2, rho2) ->
    block_equiv (β1, H1, Env rho1) (β2, H2, Env rho2).
  Proof.
    simpl; eauto.
  Qed.
  
  (** * Lemmas about [live] *)  

  Lemma live_exists S H (_ : ToMSet S) :
    exists H', live S H H'.
  Proof.
  Admitted.
  
(* 
  Lemma live_deterministic S (_ : ToMSet S) H1 H2 H2' :
    live S H1 H2 ->
    live S H1 H2' ->
    S |- H2 ≃ H2'.
  Proof.
    intros [Hyp1 Hyp2] [Hyp1' Hyp2'].
    eapply Equivalence.equiv_transitive; eauto.
    symmetry. eassumption.
  Qed.
 *)

  Lemma live_collect S (_ : ToMSet S) H1 H2 :
    live S H1 H2 ->
    collect S H1 H2.
  Proof.
    intros [Hs Hl]. 
  Admitted.

  Lemma live_idempotent (S : Ensemble loc) (_ : ToMSet S) (H1 H2 : heap block) :
    live S H1 H2 ->
    live S H2 H2.
  Proof.
    intros [Hs Heq]. split. rewrite Hs. 
  Abort.
  
  (* TODO move *)
  Instance ToMSet_Same_set (S1 S2 : Ensemble loc) :
    S1 <--> S2 ->
    ToMSet S1 ->
    ToMSet S2.
  Proof.
    intros Heq [mset mset_eq]. rewrite Heq in mset_eq.
    econstructor. eassumption.
  Qed.
  
  Lemma Proper_live S1 S2 (HS1 : ToMSet S1) (HS2 : ToMSet S2) H1 H2:
    S1 <--> S2 ->
    live S1 H1 H2 ->
    live S2 H1 H2.
  Proof.
    intros Heq [Hs Heq1]. split; eauto.
  Admitted.
  

  Lemma val_loc_in_dom β1 β2 (H1 H2 : heap block) (v1 v2 : value) :
    (v1, H1) ≈_(β1, β2) (v2, H2) ->
    val_loc v1 \subset dom H1 ->
    val_loc v2 \subset dom H2.
  Proof.
    intros Heq Hin.
    rewrite res_equiv_eq in Heq.
    destruct v1; destruct v2; try contradiction.
    - destruct (Hin l) as [b Hb].
      reflexivity. simpl in Heq. rewrite Hb in Heq. 
      eapply Singleton_Included.
      destruct b.
      + destruct (get l0 H2) eqn:Heq'; try contradiction. 
        now eexists; eauto.
      + destruct (get l0 H2) eqn:Heq'; try contradiction. 
        now eexists; eauto.
      + destruct (get l0 H2) eqn:Heq'; try contradiction. 
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

  Lemma heap_equiv_post S β1 β2 H1 H2 l1 n b1 :
    S |- H1 ≃_(β1, β2) H2 ->
    In _ ((post H1 ^ n) S) l1 ->
    get l1 H1 = Some b1 ->
    exists l2 b2, In _ ((post H2 ^ n) S) l2 /\ get l2 H2 = Some b2 /\
             block_equiv (β1, H1, b1) (β2, H2, b2).
  Proof.
    intros Heq.
    revert l1 b1. induction n as [| n IHn]; intros l1 b1 Hin Hget.
    - edestruct Heq as [[Heq1' [le Heq']] _]; eauto.
    - simpl in Hin. simpl.
      destruct Hin as [l1' [b1' [Hin [Hget' Hin']]]]. 
      edestruct IHn as [l2' [b2' [Hpost [Hget2 Heqb]]]]; eauto.
      simpl in Heqb.
      edestruct block_equiv_exists_loc as [l2 [Hl2in Hleq]]; eauto.
      rewrite res_equiv_eq in Hleq. simpl in Hleq. rewrite Hget in Hleq.
      destruct (get l2 H2) as [b2 |] eqn:Hgetl2; try contradiction.
      exists l2, b2. split; [| split; now eauto ].
      eexists. eexists. split; eauto.
  Qed.

  Lemma heap_equiv_respects_well_formed S β1 β2 H1 H2 :
    S |- H1 ≃_(β1, β2) H2 ->
    well_formed (reach' H1 S) H1 ->
    well_formed (reach' H2 S) H2.
  Proof.
    intros Heq Hwf l2 b2 [n [_ Hin]] Heq2.
    symmetry in Heq. 
    edestruct heap_equiv_post as [l1 [b1 [Hpost1 [Hget1 Heq1]]]]; eauto.
    eapply Hwf in Hget1; [| eexists; split; [ now constructor | now eauto ]].
    eapply locs_in_dom; eauto. symmetry; eassumption.
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
      rewrite Hget in Heqv.
      destruct (get l H2) eqn:Hgetl; try contradiction.
      destruct Heqv as [Hbs Heqv].
      do 2 eexists. split.
      eexists. split; eauto. rewrite Heqx'.
      reflexivity. split; eauto.
    - simpl in Hin.
      destruct Hin as [l1' [b1' [Hin [Hget' Hin']]]]. 
      edestruct IHn as [l2' [b2' [Hpost [Hget2 Heqb]]]]; eauto.
      simpl in Heqb.
      edestruct block_equiv_exists_loc as [l2 [Hl2in Hleq]]; eauto.
      rewrite res_equiv_eq in Hleq. simpl in Hleq. rewrite Hget in Hleq.
      destruct (get l2 H2) as [b2 |] eqn:Hgetl2; try contradiction.
      destruct Hleq as [Hbs' Heqv'].
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
  
  Lemma heap_equiv_in_dom S S' β1 β2 H1 H2 :
    S |- H1 ≃_(β1, β2) H2 ->
    S' \subset S ->
    S' \subset dom H1 ->
    S' \subset dom H2.
  Proof.
    intros Heq Hsub Hsub1 l Hin.
    edestruct Hsub1 as [b Hget]; eauto.
    edestruct Heq as [[Hbs [b' [Hget' _]]] _]; eauto.
    eexists; eauto.
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
  
  Lemma subheap_heap_approx_l S β (H H' : heap block) (rho : env) :
    well_formed (reach' H S) H ->
    S \subset dom H ->
    H ⊑ H' ->
    heap_approx S (β, H) (β, H').
  Proof.
    intros Hwf Hs Hsub b l Hin Hget.
    eapply Hsub in Hget. split; eauto.
    eexists; split; eauto.
    eapply subheap_block_equiv; eauto.
    eapply Included_trans; [| eapply Included_post_reach' ].
    intros l' Hin'. repeat eexists; eauto.
    edestruct reachable_in_dom as [b' Hgetb']; try eassumption.
    eapply reach'_extensive. eassumption.
    rewrite Hgetb'. eapply Hsub in Hgetb'. congruence.
  Qed.
  
  Lemma subheap_heap_approx_r S β (H H' : heap block) (rho : env) :
    well_formed (reach' H S) H ->
    S \subset dom H ->
    H ⊑ H' ->
    heap_approx S (β, H') (β, H).
  Proof.
    intros Hwf Hs Hsub b l Hin Hget.
    edestruct reachable_in_dom as [b' Hgetb']; try eassumption.
    eapply reach'_extensive. eassumption.
    split; eauto. eexists; split; eauto.
    assert (Hgetb := Hgetb').
    eapply Hsub in Hgetb'. subst_exp.
    symmetry. eapply subheap_block_equiv; eauto.
    eapply Included_trans; [| eapply Included_post_reach' ].
    intros l' Hin'. repeat eexists; eauto.
  Qed.
  
  Lemma subheap_heap_equiv S β (H H' : heap block) (rho : env) :
     well_formed (reach' H S) H ->
     S \subset dom H ->
     H ⊑ H' ->
     S |- H ≃_(β, β) H'.
  Proof.
    intros Hwf Hs Hsub.
    split. 
    now eapply subheap_heap_approx_l; eauto.
    now eapply subheap_heap_approx_r; eauto.
  Qed.
  
End HeapEquiv.
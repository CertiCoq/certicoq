(* Correctness of the implementation of closure conversion w.r.t.
   the inductive relation
 *)

From CertiCoq.L6 Require Import cps cps_util set_util identifiers ctx
                         Ensembles_util List_util hoare functions tactics.

Require Import CertiCoq.L6.Heap.closure_conversion CertiCoq.L6.Heap.closure_conversion_util.

From compcert.lib Require Import Coqlib.

From Coq Require Import ZArith.Znumtheory ArithRing Relations.Relations Arith.Wf_nat
        Lists.List MSets.MSets MSets.MSetRBT Numbers.BinNums
        NArith.BinNat PArith.BinPos Sets.Ensembles Omega.

From ExtLib Require Import Structures.Monads Data.Monads.StateMonad.

Import ListNotations.
Import MonadNotation.

Open Scope ctx_scope.
Open Scope fun_scope.
Close Scope Z_scope.

(** * Correspondence of the relational and the computational definitions of closure conversion *)

Section CC_sound.

  Variable (clo_tag : cTag).
  
  Definition Scope_st fvmap Scope :=
    [ set x | M.get x fvmap = Some BoundVar ] <--> Scope.

  Definition Funs_st fvmap Scope Funs :=
    [ set x | exists env, M.get x fvmap = Some (MRFun env) ] <--> (Funs \\ Scope).

  Definition fenv_st fvmap fenv :=
    forall x env, M.get x fvmap = Some (MRFun env) -> env = fenv x.

  Definition FV_st fvmap Scope Funs FVs :=
    (forall N x, M.get x fvmap = Some (FVar N) -> nthN FVs N = Some x) /\
    (forall x N, nthN FVs N = Some x -> ~ x \in Scope :|: Funs -> M.get x fvmap = Some (FVar N)).
  
  Definition CCState Scope Funs fenv FVs s :=
    Scope_st s Scope /\ Funs_st s Scope Funs /\ fenv_st s fenv /\ FV_st s Scope Funs FVs. 


  Instance Proper_CCState1 : Proper (Same_set _ ==> eq ==> eq ==> eq ==> eq ==> iff) CCState.
  Proof.
    intros s1 s2 Hseq ? ? ? ? ? ? ? ? ? ? ?? ; subst. unfold CCState, Scope_st, Funs_st, FV_st.
    split; intros [H1 [H2 [H3 [H4 H5]]]].
    - split; [| split; [| split; [| split ]]]; eauto.
      rewrite <- Hseq. eauto.
      rewrite <- Hseq. eauto.
      setoid_rewrite <- Hseq. eauto.
    - split; [| split; [| split; [| split ]]]; eauto.
      rewrite Hseq. eauto.
      rewrite Hseq. eauto.
      setoid_rewrite Hseq. eauto.
  Qed.
                                      
  Instance Proper_CCState2 Scope : Proper (Same_set _ ==> eq ==> eq ==> eq ==> iff) (CCState Scope).
  Proof.
    intros s1 s2 Hseq ? ? ? ? ? ? ? ? ?; subst. unfold CCState, Scope_st, Funs_st, FV_st.
    split; intros [H1 [H2 [H3 [H4 H5]]]].
    - split; [| split; [| split; [| split ]]]; eauto.
      rewrite <- Hseq. eauto.
      setoid_rewrite <- Hseq. eauto.
    - split; [| split; [| split; [| split ]]]; eauto.
      rewrite Hseq. eauto.
      setoid_rewrite Hseq. eauto.
  Qed.

  Instance Proper_CCState_f_eq Scope Funs : Proper (f_eq ==> eq ==> eq ==> iff) (CCState Scope Funs).
  Proof.
    intros s1 s2 Hseq ? ? ? ? ? ?; subst. unfold CCState, fenv_st.
    split; intros [H1 [H2 [H3 [H4 H5]]]].
    - split; [| split; [| split; [| split ]]]; eauto.
      intros. rewrite <- Hseq. eauto.
    - split; [| split; [| split; [| split ]]]; eauto.
      intros. rewrite Hseq. eauto.
  Qed.

    
  Lemma binding_in_map_in_FV Scope Funs FVs fenv s :
    CCState Scope Funs fenv FVs s ->
    binding_in_map (FV Scope Funs FVs) s.
  Proof.
    intros Hbin x Hin. inv Hin. inv H. 
    - destruct Hbin as [Hbin _]. eapply Hbin in H0. eauto.
    - eapply Hbin in H0.
      destruct H0 as [e Hget1]. eauto. 
    - inv H. edestruct In_nthN as [N Hn]. eapply H0.
      eapply Hbin in Hn; eauto.
  Qed.

  Lemma CCState_Funs_setminus Scope Funs FVs fenv s x :
    ~ x \in Funs ->
            CCState Scope (Funs \\ [set x]) fenv FVs s <->
            CCState Scope Funs fenv FVs s.
  Proof. 
    intros Hnin. rewrite <- (Included_Setminus_Disjoint Funs [set x]).
    reflexivity.
    eapply Disjoint_Singleton_r. eassumption. 
  Qed.

  Lemma CCState_Funs_setminus_l Scope Funs FVs fenv s x :
    ~ x \in Funs ->
            CCState Scope (Funs \\ [set x]) fenv FVs s ->
            CCState Scope Funs fenv FVs s.
  Proof. 
    intros. eapply CCState_Funs_setminus in H.
    eapply H; eauto.
  Qed.

  Lemma CCState_Funs_setminus_r Scope Funs FVs fenv s x :
    ~ x \in Funs ->
            CCState Scope Funs fenv FVs s ->
            CCState Scope (Funs \\ [set x]) fenv FVs s.
  Proof. 
    intros. eapply CCState_Funs_setminus in H.
    eapply H; eauto.
  Qed.
  
  Lemma CCState_Funs_Union_Setminus_l Scope Funs FVs fenv s x :
    CCState (x |: Scope) (Funs \\ [set x]) fenv FVs s ->
    CCState (x |: Scope) Funs fenv FVs s.
  Proof. 
    intros [H1 [H2 [H3 H4]]].
    unfold CCState in *.
    split; [| split; [| split ]]; try eassumption.

    unfold Funs_st in *.
    rewrite Setminus_Union in H2. rewrite Union_Same_set in H2; edb. 

    unfold FV_st in *.
    setoid_rewrite (Union_Setminus_Included _ _ [set x]) in H4; tci; edb. 
  Qed.

  Lemma CCState_Funs_Union_Setminus_r Scope Funs FVs fenv s x :
    CCState (x |: Scope) Funs fenv FVs s ->
    CCState (x |: Scope) (Funs \\ [set x]) fenv FVs s.            
  Proof. 
    intros [H1 [H2 [H3 H4]]].
    unfold CCState in *.
    split; [| split; [| split ]]; try eassumption.
    
    unfold Funs_st in *.
    rewrite Setminus_Union. rewrite Union_Same_set; edb. 
    
    unfold FV_st in *.
    setoid_rewrite (Union_Setminus_Included _ _ [set x]) ; tci; edb. 
  Qed.


  Lemma FV_Union_Scope1 Scope Funs FVs x :  
    x \in Funs -> ~ x \in Scope ->
                         FV Scope Funs FVs <--> FV (x |: Scope) (Funs \\ [set x]) FVs. 
  Proof.
    intros Hin Hnin. unfold FV. 
    rewrite !(Union_commut [set x] Scope) at 2.
    rewrite (Union_Setminus_Included _ _ [set x]); eauto with Ensembles_DB typeclass_instances.
    rewrite Setminus_Union.
    rewrite (Union_Same_set [set x] (Scope :|: [set x])); eauto with Ensembles_DB typeclass_instances.
    rewrite <- (Setminus_Union Funs ). 
    rewrite (Union_Setminus_Included _ _ [set x]); eauto with Ensembles_DB typeclass_instances.
    
    rewrite <- (Union_assoc Scope [set x] Funs).
    rewrite (Union_Same_set [set x] Funs); eauto with Ensembles_DB typeclass_instances.

    rewrite (Union_commut [set x]). rewrite <- (Union_assoc _ [set x] (Funs \\ Scope)).
    rewrite (Union_Same_set [set x] (Funs \\ Scope)); eauto with Ensembles_DB typeclass_instances.
  Qed. 

  Lemma FV_Union_Scope2 Scope Funs FVs x :  
    x \in FromList FVs -> ~ x \in Scope :|: Funs ->
                                 FV Scope Funs FVs <--> FV (x |: Scope) Funs FVs. 
  Proof.
    intros Hin Hnin. unfold FV.
    rewrite !(Union_commut [set x] Scope) at 2.
    rewrite <- (Union_assoc Scope [set x] Funs).
    rewrite !(Union_commut [set x] Funs) at 1.
    rewrite (Union_assoc Scope Funs [set x]).
    rewrite <- (Setminus_Union (FromList FVs) (Scope :|: Funs)).
    rewrite (Union_Setminus_Included _ _ [set x]);
      eauto with Ensembles_DB typeclass_instances.
    rewrite <- (Setminus_Union Funs ). 
    rewrite (Union_Setminus_Included _ _ [set x]); eauto with Ensembles_DB typeclass_instances.

    rewrite <- !(Union_assoc [set x]).
    rewrite (Union_Same_set [set x] _). reflexivity.
    eapply Singleton_Included. right. 
    constructor; eauto.
  Qed.

  Lemma FV_Union1_l Scope Funs FVs x :  
    x |: FV Scope Funs FVs \subset FV (x |: Scope) Funs FVs. 
  Proof.
    unfold FV. eapply Union_Included.
    now eauto with Ensembles_DB.
    
    rewrite !(Union_commut [set x] Scope) at 2.
    rewrite <- (Union_assoc Scope [set x] Funs).
    rewrite !(Union_commut [set x] Funs) at 1.
    rewrite (Union_assoc Scope Funs [set x]).
    rewrite <- (Setminus_Union (FromList FVs) (Scope :|: Funs)).
    rewrite (Union_Setminus_Included _ _ [set x]);
      eauto with Ensembles_DB typeclass_instances.
    rewrite <- (Setminus_Union Funs ). 
    rewrite (Union_Setminus_Included _ _ [set x]); eauto with Ensembles_DB typeclass_instances.
  Qed.

  Lemma FV_Setminus_Union_l Scope Funs FVs S `{ToMSet S}:  
      S :|: FV Scope Funs FVs \subset FV (Scope \\ S)  (S :|: Funs) FVs. 
  Proof.
    unfold FV. eapply Union_Included.
    now edb.
    rewrite !(Union_commut (Scope \\ S)).  
    rewrite !(Union_Setminus_Included _ _ S); tci; edb.
    rewrite <- (Union_assoc S Funs Scope).
    rewrite !(Union_commut S), <- !Setminus_Union.  
    rewrite !(Union_Setminus_Included _ _ S); tci; edb.
    eapply Union_Included; edb. 
    rewrite !Setminus_Union. edb.
  Qed.

  Lemma FV_Setminus2_l Scope Funs FVs x :  
    FV Scope Funs FVs \subset x |: FV Scope (Funs \\ [set x]) FVs. 
  Proof with now eauto with Ensembles_DB.
    unfold FV.
    rewrite !Setminus_Union.
    
    rewrite !(Union_commut [set x] Scope).
    rewrite <- !Setminus_Union. rewrite !Union_assoc. 
    rewrite (Union_Setminus_Included _ _ [set x]); eauto with Ensembles_DB typeclass_instances.
  Qed. 

  (** Get var entry lemmas *)
  
  Lemma get_var_entry_preserves_prop x P :
    {{ fun s => P s }} get_var_entry x {{ fun _ _ s => P s }}.
  Proof.
    eapply pre_post_mp_l. eapply bind_triple. eapply get_triple.
    intros [x1 c1 f1 e1 m1] [x2 c2 f2 e2 m2]. 
    simpl.
    destruct (Maps.PTree.get x x1); simpl; eapply return_triple;
      intros ? H ?; inv H; eauto.
  Qed.

  Lemma get_var_entry_binding_in_map x P :
    {{ fun s => binding_in_map [set x] (var_map s) /\ P s }}
      get_var_entry x
    {{ fun _ o s => P s /\ M.get x (var_map s) = o /\ exists v, o = Some v }}.
  Proof.
    eapply pre_post_mp_l. eapply bind_triple. eapply get_triple.
    intros [x1 c1 f1 e1 m1] [x2 c2 f2 e2 m2]. 
    simpl.
    destruct (Maps.PTree.get x x1) eqn:Hget; simpl; eapply return_triple;
      intros ? H [? ?]; inv H; split; eauto;    
        inv H2; edestruct H0 as [v' Hget'].

    reflexivity.     
    simpl. split. congruence. eexists; reflexivity.

    reflexivity. congruence. 
  Qed.

  (** Set var entry lemmas *)
  
  Lemma set_var_entry_bound x Scope Funs fenv FVs :
    {{ fun s => True }}
      set_var_entry x BoundVar
    {{ fun s _ s' => binding_in_map [set x] (var_map s') /\
                  (CCState Scope Funs fenv FVs (var_map s) ->
                   CCState (x |: Scope) Funs fenv FVs (var_map s')) /\
                  next_var s = next_var s'
    }}.
  Proof.
    eapply bind_triple. eapply get_triple.
    intros [x1 c1 f1 e1 m1] [x2 c2 f2 e2 m2].
    eapply pre_post_mp_l. eapply bind_triple. eapply put_triple.
    intros.
    eapply return_triple. intros ? ? [H1 H2]. subst. inv H1; eauto.
    split; [| split ]. 
    - simpl. eexists; eauto. inv H. rewrite M.gss; eauto.
    - unfold CCState. intros (H1 & H2 & H3 & H4).
      split; [| split; [| split] ].  
      + unfold Scope_st in *. rewrite <- H1. 
        simpl. split; intros x1; unfold In; simpl.
        
        * destruct (var_dec x1 x); subst.
          intros. now left.
          
          rewrite M.gso. intros. right. eassumption.
          eassumption.
          
        * intros H.
          destruct (var_dec x1 x); subst.
          
          rewrite M.gss; eauto.
          inv H; eauto. inv H0; contradiction. 
          rewrite M.gso; eauto.
          
      + unfold Funs_st in *. rewrite Union_commut, <- Setminus_Union, <- H2.  simpl. split; intros x1; unfold In; simpl.
        
        * destruct (var_dec x1 x); subst.
          
          intros [? H]. rewrite M.gss in H. congruence. 
          
          intros [? H]. rewrite M.gso in H; eauto.
          constructor.
          now eauto. intros Hc; inv Hc. congruence.

        * destruct (var_dec x1 x); subst.
          
          intros [? H]. exfalso; eauto.
          
          intros [[env Hyp1] Hyp2]. eexists.
          rewrite M.gso. eassumption. intros Hc; inv Hc. eauto.

      + unfold fenv_st in *. simpl.
        intros x1 e Hget.
        destruct (var_dec x1 x); subst.
        rewrite M.gss in Hget. congruence. 
        
        rewrite M.gso in Hget. eauto. eassumption.
        
      + unfold FV_st in *. split. 
        
        * intros N x1 Hget.
          destruct (var_dec x1 x); subst; simpl in *. 
          rewrite M.gss in Hget. congruence. 
          
          rewrite M.gso in Hget. eapply H4. eassumption. eassumption.
        * intros x1 N Hn Hnin. simpl.
          destruct (var_dec x1 x); subst; simpl in *. 
          exfalso; eauto.

          rewrite M.gso; eauto. eapply H4. eassumption.
          intros Hc. eapply Hnin. inv Hc; eauto.
    - reflexivity.
  Qed.

  Lemma set_var_entry_bound' x Scope Funs fenv FVs Q :
    {{ fun s => CCState Scope Funs fenv FVs (var_map s) /\ Q (next_var s) }}
      set_var_entry x BoundVar
    {{ fun s _ s' => CCState (x |: Scope) Funs fenv FVs (var_map s') /\ Q (next_var s') }}.
  Proof.
    eapply pre_post_mp_l.
    eapply post_weakening; [| eapply set_var_entry_bound ].
    intros s [] s' _ [Hin [Hst Heq]] [Hst' Hq].
    split; eauto. now rewrite <- Heq.
  Qed. 
    
  Lemma set_var_entry_fun x Scope Funs fenv FVs env :
    {{ fun s => True }}
      set_var_entry x (MRFun env)
    {{ fun s _ s' => binding_in_map [set x] (var_map s') /\
                    
                    (CCState Scope Funs fenv FVs (var_map s) ->
                     CCState (Scope \\ [set x]) (x |: Funs) (fenv{x ~> env}) FVs (var_map s')) /\
                    next_var s = next_var s'
      }}.
  Proof.
    eapply bind_triple. eapply get_triple.
    intros [x1 c1 f1 e1 m1] [x2 c2 f2 e2 m2].
    eapply pre_post_mp_l. eapply bind_triple. eapply put_triple.
    intros.
    eapply return_triple. intros ? ? [H1 H2]. subst. inv H1; eauto.
    split; [| split ]. 
    - simpl. eexists; eauto. inv H. rewrite M.gss; eauto.
    - unfold CCState. intros (H1 & H2 & H3 & H4).
      split; [| split; [| split] ].  
      + unfold Scope_st in *. rewrite <- H1. simpl. 
        split; intros x1; unfold In; simpl.
        
        * destruct (var_dec x1 x); subst.
          rewrite M.gss. congruence.
          
          rewrite M.gso; eauto. constructor; eauto.
          intros Hc; inv Hc; eauto.
          
        * intros H.
          destruct (var_dec x1 x); subst.
          now inv H; exfalso; eauto.
          rewrite M.gso; eauto.
          inv H; eauto.
          
      + unfold Funs_st in *. simpl in *. split; intros x1; unfold In; simpl.
        
        * destruct (var_dec x1 x); subst; eauto.
          intros. constructor; eauto. intros Hc; inv Hc; eauto.
          
          intros H. setoid_rewrite M.gso in H; eauto. eapply H2 in H.
          inv H; eauto. constructor; eauto. intros Hc; inv Hc; eauto.            
        * destruct (var_dec x1 x); subst.
          
          intros [? H]. setoid_rewrite M.gss; eauto.
          
          intros [? H]. setoid_rewrite M.gso; eauto.
          eapply H2. inv H0; try (now inv H5; eauto).
          constructor; eauto. intros Hc. eapply H; constructor; eauto. 
          intros Hc'; inv Hc'. eauto.  
          
      + unfold fenv_st in *. simpl.
        intros x1 e Hget.
        destruct (var_dec x1 x); subst.
        rewrite M.gss in Hget. rewrite extend_gss. congruence. 
        
        rewrite M.gso in Hget. eauto.
        rewrite extend_gso; eauto. eassumption.
        
      + unfold FV_st in *. split. 
        
        * intros N x1 Hget.
          destruct (var_dec x1 x); subst; simpl in *. 
          rewrite M.gss in Hget. congruence. 
          
          rewrite M.gso in Hget. eapply H4. eassumption. eassumption.
        * intros x1 N Hn Hnin. simpl.
          destruct (var_dec x1 x); subst; simpl in *. 
          exfalso; eauto.
          
          rewrite M.gso; eauto. eapply H4. eassumption.
          intros Hc. eapply Hnin. inv Hc.
          constructor; eauto. now constructor; eauto.
          right. now right. 
    - reflexivity.
  Qed. 
  
  Lemma set_var_entry_fv x Scope Funs fenv FVs N :
    ~ x \in Scope :|: Funs ->
    N.of_nat (length FVs) = N ->
    ~ x \in FromList FVs ->
    {{ fun s => True }}
      set_var_entry x (FVar N)
    {{ fun s _ s' => binding_in_map [set x] (var_map s') /\
                  (CCState Scope Funs fenv FVs (var_map s) ->
                   CCState Scope Funs fenv (@app positive FVs [ x ]) (var_map s')) /\
                  next_var s = next_var s'
    }}.
  Proof.
    intros Hnin Hlen Hnin'.  
    eapply bind_triple. eapply get_triple.
    intros [x1 c1 f1 e1 m1] [x2 c2 f2 e2 m2]. 
    eapply pre_post_mp_l. eapply bind_triple. now eapply put_triple.
    intros.
    eapply return_triple. intros s1 Heq [H1 H2]. subst.  inv H1; eauto.  
    split; [| split ]. 
    - simpl. eexists; eauto. inv H. rewrite M.gss; eauto.
    - unfold CCState. intros (H1 & H2 & H3 & H4).
      split; [| split; [| split] ].  
      + unfold Scope_st in *. rewrite <- H1. simpl. 
        split; intros x1; unfold In; simpl.
        
        * destruct (var_dec x1 x); subst.
          rewrite M.gss. congruence.
          
            rewrite M.gso; eauto.
            
        * intros H. eapply H1 in H. 
          destruct (var_dec x1 x); subst.
          now exfalso; eauto.
          rewrite M.gso; eauto. eapply H1; eauto. 
          
      + unfold Funs_st in *. simpl in *. split; intros x1; unfold In; simpl.
        
        * destruct (var_dec x1 x); subst; eauto.
          intros H. rewrite M.gss in H. destruct H; congruence.

          intros H. rewrite M.gso in H; eauto. eapply H2. eassumption.
        * destruct (var_dec x1 x); subst.

          intros Hin. inv Hin. now exfalso; eauto.

          intros Hin. setoid_rewrite M.gso; eauto.
          eapply H2; eauto. 
          
      + unfold fenv_st in *. simpl.
        intros x1 e Hget.
        destruct (var_dec x1 x); subst.
        rewrite M.gss in Hget. congruence. 
        
        rewrite M.gso in Hget. eauto. eassumption.
        
      + unfold FV_st in *. simpl in *. split. 
        
        * intros N x1 Hget. 
          destruct (var_dec x1 x); subst; simpl in *.

          rewrite M.gss in Hget. inv Hget. 
          rewrite nthN_app_geq; eauto. rewrite N.sub_diag.
          reflexivity. reflexivity.
          
          rewrite M.gso in Hget; eauto. eapply H4 in Hget.
          eapply nthN_is_Some_app. eassumption.
          
        * intros x1 N Hn Hnin1. simpl. 
          assert (Hor := @nthN_app positive FVs [x] N). 

          destruct (var_dec x1 x); subst; simpl. 

          rewrite M.gss. destruct Hor as [H | [H H']].

          rewrite H in Hn.
          eapply nthN_In in Hn. now exfalso; eauto. 

          rewrite H in Hn. eapply nthN_is_Some_length in Hn. 
          simpl in Hn. eapply N.lt_1_r in Hn. f_equal. f_equal.
          eapply N.sub_0_le in Hn. eapply N_as_OT.le_antisymm; eassumption.

          rewrite M.gso; eauto. eapply H4; eauto. 
          destruct Hor as [H | [H H']]. congruence.
          rewrite Hn in H. eapply nthN_is_Some_length in Hn. 
          simpl in H.
          destruct (N - N.of_nat (@length positive FVs))%N eqn:Hneq; try congruence.
    - reflexivity.
  Qed. 



  (** Get var spec *)
  
  Lemma get_var_sound S x c Γ Scope Funs fenv FVs :
    x \in FV Scope Funs FVs ->
    exists Scope' Funs',
      FV Scope Funs FVs <--> FV Scope' Funs' FVs /\
      {{ fun s : state_contents =>
           CCState Scope Funs fenv FVs (var_map s) /\
           fresh S (next_var s)
      }}
        get_var clo_tag x c Γ
      {{ fun s C s' =>
           project_var clo_tag Scope Funs fenv c Γ FVs x C Scope' Funs' /\             
           CCState Scope' Funs' fenv FVs (var_map s') /\
           fresh S (next_var s')
      }}.
  Proof with (eauto with Ensembles_DB).
    intros Hin. inv Hin. inv H.
    - (* Scope *)
      eexists Scope, Funs. split. reflexivity. 
      eapply pre_strenghtening
        with (P := fun s => binding_in_map [set x] (var_map s) /\
                         M.get x (var_map s) = Some BoundVar /\
                         CCState Scope Funs fenv FVs (var_map s) /\
                         fresh S (next_var s)).
      + intros s [Hs1 Hs2]. split; eauto. eapply binding_in_map_antimon; [| eapply binding_in_map_in_FV; eauto ].
        eapply Singleton_Included. left. now left.
        split; eauto.
        eapply Hs1. eassumption.
      + unfold get_var. eapply bind_triple.
        eapply get_var_entry_binding_in_map.
        intros v [x2 c2 f2 e2 m2]. eapply pre_post_mp_l.
        destruct v as [ [ | | ] | ]. 
        * eapply bind_triple. eapply (set_var_entry_bound x Scope Funs fenv FVs).
          intros r i. eapply return_triple.
          intros s'. intros [Hbin [Hcc Hv]] [[Hcc' Hf] [v Hb]].
          congruence.
        * eapply bind_triple. eapply (set_var_entry_bound x Scope Funs fenv FVs).
          intros r i. eapply return_triple.
          intros s'. intros [Hbin [Hcc Hv]] [[Hcc' Hf] [v' Hb]].
          congruence.
        * eapply return_triple.
          intros s'. intros _  [[Hget [Hcc Hf]] [Hcc' Hf']].
          split; eauto. constructor. eassumption.
        * eapply return_triple.
          intros s'. intros _  [[Hg1 _] [Hg2 _]].
          congruence.
    - (* Funs *)
      eexists (x |: Scope), (Funs \\ [set x]). split.
      inv H0. eapply FV_Union_Scope1; now eauto.
      eapply pre_strenghtening
        with (P := fun s => binding_in_map [set x] (var_map s) /\
                         M.get x (var_map s) = Some (MRFun (fenv x)) /\
                         CCState Scope Funs fenv FVs (var_map s) /\
                         fresh S (next_var s)).
      + intros s [Hs1 Hs2]. split; eauto.
        eapply binding_in_map_antimon; [| eapply binding_in_map_in_FV; eauto ].
        eapply Singleton_Included. left. now right.
        split; eauto.
        edestruct Hs1 as [Hss [Hhf [Hen Hfv]]]. 
        eapply Hhf in H0. edestruct H0 as [e' Hgetf].
        assert (Hgetf' := Hgetf). eapply Hen in Hgetf. congruence.
      + unfold get_var. eapply bind_triple.
        eapply get_var_entry_binding_in_map.
        intros v [x2 c2 f2 e2 m2]. eapply pre_post_mp_l.
        destruct v as [ [ | | ] | ]. 
        * eapply bind_triple. eapply (set_var_entry_bound x Scope Funs fenv FVs).
          intros r i. eapply return_triple.
          intros s'. intros [Hbin [Hcc Hv]] [[Hget [Hcc' Hf]] [v Hb]].
          congruence. 
        * eapply bind_triple. eapply (set_var_entry_bound x Scope Funs fenv FVs).
          intros r i. eapply return_triple.
          intros s'. intros [Hbin [Hcc Hv]] [[Hgetd [Hcc' Hf]] [v' Hb]].
          split; eauto.
          repeat subst_exp. inv H0. now econstructor; eauto.
          repeat subst_exp. 
          split; eauto. eapply CCState_Funs_Union_Setminus_r. now eauto.
          rewrite <- Hv. eassumption. 
        * eapply return_triple.
          intros s'. intros _  [[Hget [Hcc Hf]] [Hcc' Hf']].
          congruence.
        * eapply return_triple.
          intros s'. intros _  [[Hg1 _] [Hg2 _]].
          congruence.
    - (* FVs *)
      inv H.
      edestruct (@In_nthN var) as [N Hnth]. eassumption. 
      eexists (x |: Scope), Funs.
      split. apply FV_Union_Scope2; now eauto.
      
      eapply pre_strenghtening
        with (P := fun s => binding_in_map [set x] (var_map s) /\
                         M.get x (var_map s) = Some (FVar N) /\
                         CCState Scope Funs fenv FVs (var_map s) /\
                         fresh S (next_var s)).
      + intros s [Hs1 Hs2]. split; eauto.
        eapply binding_in_map_antimon; [| eapply binding_in_map_in_FV; eauto ].
        eapply Singleton_Included. now right.
        split; eauto. eapply Hs1; eauto. 
      + unfold get_var. eapply bind_triple.
        eapply get_var_entry_binding_in_map.
        intros v [x2 c2 f2 e2 m2]. eapply pre_post_mp_l.
        destruct v as [ [ | | ] | ]. 
        * eapply bind_triple. eapply (set_var_entry_bound x Scope Funs fenv FVs).
          intros r i. eapply return_triple.
          intros s'. intros [Hbin [Hcc Hv]] [[Hget [Hcc' Hf]] [v Hb]].
          repeat subst_exp.
          split; eauto. repeat subst_exp.
          now econstructor; eauto.
          split; eauto.
          rewrite <- Hv. eassumption.             
        * eapply bind_triple. eapply (set_var_entry_bound x Scope Funs fenv FVs).
          intros r i. eapply return_triple.
          intros s'. intros [Hbin [Hcc Hv]] [[Hgetd [Hcc' Hf]] [v' Hb]]. congruence.  
        * eapply return_triple.
          intros s'. intros _  [[Hget [Hcc Hf]] [Hcc' Hf']].
          congruence.
        * eapply return_triple.
          intros s'. intros _  [[Hg1 _] [Hg2 _]].
          congruence.
  Qed. 
  
  (** Get_vars spec *)
  
  Lemma get_vars_sound S xs c Γ Scope Funs fenv FVs :
    FromList xs \subset FV Scope Funs FVs ->
    exists Scope' Funs',
      FV Scope Funs FVs <--> FV Scope' Funs' FVs /\
      {{ fun s : state_contents =>
           CCState Scope Funs fenv FVs (var_map s) /\
           fresh S (next_var s)
      }}
        get_vars clo_tag xs c Γ
      {{ fun s C s' =>
           project_vars clo_tag Scope Funs fenv c Γ FVs xs C Scope' Funs' /\
           CCState Scope' Funs' fenv FVs (var_map s') /\
           fresh S (next_var s')
      }}.
  Proof with (eauto with Ensembles_DB).
    revert Scope Funs. induction xs as [| x xs IHxs ]; intros Scope Funs; normalize_sets; intros Hin.
    - eexists Scope, Funs. split. reflexivity. 
      eapply return_triple. intros s [H1 H2]; split; eauto.
      constructor.
    - assert (Hin' := Hin).
      eapply Union_Included_l in Hin. 
      eapply Union_Included_r in Hin'.
      edestruct get_var_sound as [Scope1 [Funs1 [Heq Hcomp']]]. eapply Hin. reflexivity.                 
      edestruct (IHxs Scope1 Funs1) as [Scope2 [Funs2 [Heq' Hcomp]]]. 
      rewrite <- Heq. eassumption.
      
      eexists Scope2, Funs2.
      split. rewrite Heq, Heq'. reflexivity.

      unfold get_vars. eapply bind_triple.
      eassumption.
      intros C1 s1. eapply bind_triple.
      eapply pre_strenghtening with (P := fun s' : state_contents =>
                                            project_var clo_tag Scope Funs fenv c Γ FVs x C1 Scope1 Funs1 /\
                                            CCState Scope1 Funs1 fenv FVs (var_map s') /\
                                            fresh S (next_var s')).
      clear. now firstorder.
      eapply frame_rule. eassumption. 
      intros C2 s2. eapply return_triple.
      intros s'. intros [H1 [H2 [H3 H4]]]. split; eauto.
      econstructor; eassumption. 
  Qed.

  Opaque bind ret.


  (** Peak push pop var_map specs *)

  Lemma peak_var_map_spec P Q :
     {{ fun s => P (var_map s) /\ Q (next_var s) }} peak_var_map tt {{ fun _ vm s' => P vm /\ P (var_map s') /\ Q (next_var s')}}. 
  Proof.
    unfold peak_var_map. eapply pre_post_mp_l.
    eapply bind_triple.
    - eapply get_triple. 
    - intros [vmap ? ? ? ? ?] s. eapply return_triple. 
      intros s'. intros [H1 H2] [H3 H4].
      subst. split; eauto.
  Qed.

  Lemma push_var_map_spec (P : VarInfoMap -> Prop) Q vm :
    P vm ->
    {{ fun s => Q (next_var s) }} push_var_map vm {{ fun _ _ s' => P (var_map s') /\ Q (next_var s')  }}. 
  Proof.
    unfold push_var_map. intros HP. eapply pre_post_mp_l.
    eapply bind_triple.
    - eapply get_triple. 
    - intros [vmap ? ? ? ? ?] s.
      eapply pre_post_mp_l.
      eapply bind_triple.
      + eapply put_triple.
      + intros [] s'. eapply return_triple. 
        intros s'' Heq [Heq' Heq'']. subst. split; eassumption.
  Qed.
  
  Lemma pop_var_map_spec P (P' : VarInfoMap -> Prop) Q :
    P' (M.empty _) ->
    {{ fun s => P (var_map s) /\ Q (next_var s) }} pop_var_map tt {{ fun _ vm s' => P vm /\ P' (var_map s') /\ Q (next_var s') }}. 
  Proof.
    intros Hin. unfold peak_var_map. eapply pre_post_mp_l.
    eapply bind_triple.
    - eapply get_triple. 
    - intros [vmap ? ? ? ? ?] s. eapply pre_curry_l. intros Heq; subst.
      eapply pre_post_mp_l. eapply bind_triple.
      eapply put_triple.
      intros x s'. eapply return_triple. intros s'' Heq1 Heq2 [H1 H2].
      subst. split; eauto. 
  Qed.

  (** VarInfoMap properties *)
  
  Lemma var_map_emtpy :
    CCState (Empty_set _) (Empty_set _) id [] (M.empty _). 
  Proof.
    split; [| split; [| split; [| split ]]].
    - unfold Scope_st.
      split; intros x; try (now intros []). unfold In.         
      rewrite M.gempty. congruence.
    - unfold Funs_st.
      split; intros x; try (now intros []). unfold In.
      rewrite M.gempty. intros [? ?]; congruence.
    - unfold fenv_st.  
      setoid_rewrite M.gempty. congruence.
    - setoid_rewrite M.gempty. congruence.
    - intros x N Hnin. inv Hnin.
  Qed. 

  Lemma add_params_spec Scope Funs fenv FVs xs P :
    {{ fun s => CCState Scope Funs fenv FVs (var_map s) /\ P (next_var s) }}
      add_params xs
    {{ fun _ _ s' => CCState (FromList xs :|: Scope) Funs fenv FVs (var_map s') /\
                  P (next_var s') }}.
  Proof.
    revert Scope; induction xs; intros Scope.
    - simpl. eapply return_triple. intros s. normalize_sets.
      rewrite Union_Empty_set_neut_l. eauto.
    - eapply bind_triple.
      + eapply pre_transfer_r.
        eapply pre_strenghtening_true.
        eapply set_var_entry_bound. 
      + intros [] s1.
        eapply pre_strenghtening with
            (P0 := fun i => CCState (a |: Scope) Funs fenv FVs (var_map i) /\ P (next_var i)). 
        { intros s2. intros [[H1 H1'] [H2 [H3 H4]]]. split; eauto. 
          now rewrite <- H4. }
        eapply post_weakening; [| eapply IHxs ].
        
        intros s3 x s4. normalize_sets.  rewrite Union_assoc, (Union_commut _ [set a]).
        now firstorder.
  Qed. 


  Lemma add_fvs_spec Scope Funs fenv FVs fvs N P :
    N.of_nat (length FVs) = N ->
    NoDup fvs ->
    Disjoint _ (FromList FVs) (FromList fvs) ->
    Disjoint _ (FromList FVs :|: FromList fvs) (Scope :|: Funs) ->
    {{ fun s => CCState Scope Funs fenv FVs (var_map s) /\ P (next_var s) }}
      add_fvs fvs N
    {{ fun _ _ s' => CCState Scope Funs fenv (FVs ++ fvs) (var_map s') /\
                  P (next_var s') }}.
  Proof with now eauto with Ensembles_DB functions_BD.
    revert N FVs. induction fvs as [ | v fvs Hfvs ]; intros N FVs Hleq Hnd Hd1 Hd2. 
    - simpl. eapply return_triple. intros s. normalize_sets.
      rewrite app_nil_r. eauto.
    - eapply bind_triple.
      + eapply pre_transfer_r.
        eapply pre_strenghtening_true.
        eapply (set_var_entry_fv v Scope Funs); try eassumption.

        intros Hc. eapply Hd2. constructor; [| eassumption ]. 
        normalize_sets...

        intros Hc. eapply Hd1. constructor; [ eassumption | ]. 
        normalize_sets...
      + intros [] s1.  
        eapply pre_strenghtening with
            (P0 := fun i => CCState Scope Funs fenv (@app positive FVs (@cons var v (@nil var))) (var_map i) /\ P (next_var i)). 
        { intros s2. intros [[H1 H1'] [H2 [H3 H4]]]. split; eauto. now rewrite <- H4. }
        
        eapply post_weakening; [| eapply Hfvs ].

        intros s3 x s4. normalize_sets. intros _. rewrite app_assoc_reverse; eauto. 

        simpl.

        rewrite app_length. simpl. zify. omega. 

        inv Hnd; eauto. 

        inv Hnd. rewrite FromList_app. normalize_sets.
        eapply Union_Disjoint_l. eapply Disjoint_Included_r; [| eassumption ].
        normalize_sets...

        normalize_sets. rewrite Union_Empty_set_neut_r. eapply Disjoint_Singleton_l.
        eassumption. 

        rewrite FromList_app. repeat normalize_sets.
        eapply Disjoint_Included_l; [| eassumption ]... 
  Qed.
  
    
  Lemma add_funs_spec Scope Funs fenv FVs B Γ P :
    {{ fun s => CCState Scope Funs fenv FVs (var_map s) /\ P (next_var s) }}
      add_funs B Γ
    {{ fun _ _ s' => CCState (Scope \\ name_in_fundefs B) (name_in_fundefs B :|: Funs) (extend_fundefs' fenv B Γ) FVs (var_map s') /\
                  P (next_var s') }}.
  Proof.
    revert Scope Funs fenv; induction B; intros Scope Funs fenv.
    - eapply bind_triple.
      + eapply pre_transfer_r.
        eapply pre_strenghtening_true.
        eapply set_var_entry_fun. 
      + intros [] s1.
        eapply pre_strenghtening with
            (P0 := fun i => CCState (Scope \\ [set v]) (v |: Funs) (fenv {v ~> Γ}) FVs (var_map i) /\ P (next_var i)). 
        { intros s2. intros [[H1 H1'] [H2 [H3 H4]]]. split; eauto. 
          now rewrite <- H4. }
        eapply post_weakening; [| eapply IHB ].
        
        intros s3 x s4. simpl. intros _. rewrite Setminus_Union.
        rewrite (Union_commut [set v] (name_in_fundefs B)) at 2.
        rewrite <- !Union_assoc.

        assert (Hfeq : f_eq (extend_fundefs' (fenv {v ~> Γ}) B Γ) (extend_fundefs' fenv (Fcons v f l e B) Γ)).
        { intros x1.
          destruct (Decidable_name_in_fundefs B). destruct (Dec x1).
          rewrite !extend_fundefs'_get_s; eauto.
          now right. 

          rewrite extend_fundefs'_get_o; eauto. 

          destruct (peq x1 v); subst.
          rewrite extend_fundefs'_get_s; eauto. rewrite extend_gss. reflexivity.
          now left.
          
          rewrite extend_fundefs'_get_o; eauto. 
          rewrite extend_gso; eauto. intros Hc; inv Hc; eauto. inv H; eauto. }

        rewrite <- Hfeq. eauto. 
    - simpl. eapply return_triple. intros s. normalize_sets.
      rewrite Setminus_Empty_set_neut_r.
      assert (Hfeq : f_eq (extend_fundefs' fenv Fnil Γ) fenv).
      { intros x1. rewrite extend_fundefs'_get_o; eauto. intros Hc; inv Hc. }
      rewrite Hfeq. eauto. 
  Qed. 


  (** Spec for [get_name_entry] *)
  Lemma get_name_entry_preserves_prop x P Q :
    {{ fun s => Q (var_map s) /\ P (next_var s) }} get_name_entry x {{ fun _ _ s => Q (var_map s) /\ P (next_var s) }}.
  Proof.
    eapply pre_post_mp_l. eapply bind_triple. eapply get_triple.
    intros [x1 c1 f1 e1 m1] [x2 c2 f2 e2 m2].
    destruct (Maps.PTree.get x name_env);
      eapply return_triple; intros ? H ?; inv H; eauto.
  Qed.

  (** Spec for [set_name_entry] *)
  Lemma set_name_entry_preserves_prop x s P Q :
    {{ fun s => Q (var_map s) /\ P (next_var s) }} set_name_entry x s
    {{ fun _ _ s => Q (var_map s) /\ P (next_var s) }}.
  Proof.
    eapply pre_post_mp_l. eapply bind_triple. eapply get_triple.
    intros [x1 c1 f1 e1 m1] [x2 c2 f2 e2 m2].
    eapply pre_post_mp_l. eapply bind_triple. 
    eapply put_triple. intros.
    eapply return_triple. intros ? ? [H1 H2]. inv H1; eauto.
  Qed.

  (** Specs for adding names *)
  Lemma add_name_preserves_prop x y P Q :
    {{ fun s => Q (var_map s) /\ P (next_var s) }}
      add_name x y
    {{ fun _ _ s => Q (var_map s) /\ P (next_var s) }}.
  Proof.
    eapply set_name_entry_preserves_prop.
  Qed.

  
  Lemma add_name_suff_preserves_prop x y s P Q :
    {{ fun s => Q (var_map s) /\ P (next_var s) }}
      add_name_suff x y s
    {{ fun _ _ s => Q (var_map s) /\ P (next_var s) }}.
  Proof.
    eapply bind_triple. now apply get_name_entry_preserves_prop.
    intros n s1. destruct n; now apply set_name_entry_preserves_prop.
  Qed.

  Lemma make_record_cTag_preserves_prop n P Q :
    {{ fun s => Q (var_map s) /\ P (next_var s) }} make_record_cTag n {{ fun _ _ s => Q (var_map s) /\ P (next_var s) }}.
  Proof.
    eapply pre_post_mp_l. eapply bind_triple. eapply get_triple.
    intros [x1 c1 f1 e1 m1] [x2 c2 f2 e2 m2].
    apply pre_post_mp_l. eapply bind_triple. now apply put_triple.
    intros x s. eapply return_triple. intros s'. intros <-. intros [H1 H2]; subst. inv H1.
    eauto.
  Qed.

  Opaque put get. 
    
  (** Get_name spec *)
  Lemma get_name_spec Q S x str :
    {{ fun s => Q (var_map s) /\ fresh S (next_var s) }}
      get_name x str 
    {{ fun _ y s' => y \in S /\ Q (var_map s') /\ fresh (S \\ [set y]) (next_var s') }}.
  Proof.
    eapply bind_triple.
    + eapply pre_transfer_r. eapply pre_strenghtening_true. now eapply get_triple.
    + intros [x1 x2 x3 x4 x5 x6] [y1 y2 y3 y4 y5 y6]. simpl. 
      eapply pre_curry_l. intros [HQ Hf]. eapply pre_curry_l. intros H. inv H. 
      eapply pre_post_mp_l. eapply bind_triple. now eapply put_triple.
      
      intros [] s.
      eapply pre_strenghtening with (P := fun s => var_map s = y1 /\ next_var s = (y2 + 1)%positive).
      intros s' Heq; subst. now firstorder. 
      eapply bind_triple.
      eapply add_name_suff_preserves_prop with (Q := fun s => s = y1) (P := fun s => s= (y2 + 1)%positive).
      intros. eapply return_triple. intros s2 [H1 H2] H3; eauto. subst.
      split; eauto.
      eapply Hf. reflexivity. split; eauto.
      rewrite H2. intros z Heq. constructor; eauto.
      eapply Hf. zify; omega.
      intros Hc. inv Hc. zify; omega.       
  Qed.

  (** Get_name_n0_suff spec *)
  Lemma get_name_no_suff_spec Q S str :
    {{ fun s => Q (var_map s) /\ fresh S (next_var s) }}
      get_name_no_suff str 
    {{ fun _ y s' => y \in S /\ Q (var_map s') /\ fresh (S \\ [set y]) (next_var s') }}.
  Proof.
    eapply bind_triple.
    + eapply pre_transfer_r. eapply pre_strenghtening_true. now eapply get_triple.
    + intros [x1 x2 x3 x4 x5 x6] [y1 y2 y3 y4 y5 y6]. simpl. 
      eapply pre_curry_l. intros [HQ Hf]. eapply pre_curry_l. intros H. inv H. 
      eapply pre_post_mp_l. eapply bind_triple. now eapply put_triple.
      
      intros [] s.
      eapply pre_strenghtening with (P := fun s => var_map s = y1 /\ next_var s = (y2 + 1)%positive).
      intros s' Heq; subst. now firstorder. 
      eapply bind_triple.
      eapply add_name_preserves_prop with (Q := fun s => s = y1) (P := fun s => s= (y2 + 1)%positive).
      intros. eapply return_triple. intros s2 [H1 H2] H3; eauto. subst.
      split; eauto.
      eapply Hf. reflexivity. split; eauto.
      rewrite H2. intros z Heq. constructor; eauto.
      eapply Hf. zify; omega.
      intros Hc. inv Hc. zify; omega.       
  Qed.
     
  Lemma make_env_spec S Scope Funs fenv FVs fvs c Γ Γ' :
    FromList fvs \subset FV Scope Funs FVs ->
    exists Scope' Funs',
      FV Scope Funs FVs <--> FV Scope' Funs' FVs /\
      {{ fun s => CCState Scope Funs fenv FVs (var_map s) /\ fresh S (next_var s) }}
        make_env clo_tag fvs c Γ' Γ
      {{ fun _ cC s' =>
           let '(c', C) := cC in
           (exists C', comp_ctx_f C' (Econstr_c Γ' c' fvs Hole_c) = C /\                
                  project_vars clo_tag Scope Funs fenv c Γ FVs fvs C' Scope' Funs') /\
           CCState Scope' Funs' fenv FVs (var_map s') /\
           fresh S (next_var s')
      }}.
  Proof.
    intros Hsub.
    edestruct get_vars_sound as [Scope' [Funs' [Hfveq Hc]]].
    - eassumption.
    - do 2 eexists. split. eassumption.
      eapply bind_triple. eassumption. 
      intros C1 s1. 
      eapply pre_curry_l. intros Hvars.
      eapply bind_triple.
      eapply make_record_cTag_preserves_prop.
      intros c' s'. eapply return_triple.
      intros s'' [Hcc Hf]. split; eauto.
  Qed.

  Lemma fresh_monotonic S1 S2 s:
    fresh S1 s ->
    S1 \subset S2 ->
    fresh S2 s. 
  Proof.
    intros Hf Hs x Hin.
    eapply Hs. eapply Hf. eassumption.
  Qed.

  Lemma exp_closure_conv_Closure_conv_sound :
    (forall e Scope Funs c Γ FVs fenv S
       (HD1 : Disjoint _ S ((bound_var e) :|: (FV Scope Funs FVs) :|:
                                          (FV_cc Scope Funs fenv Γ)))
       (HFV : occurs_free e \subset FV Scope Funs FVs),
       {{ fun s => CCState Scope Funs fenv FVs (var_map s) /\ fresh S (next_var s) }}
         exp_closure_conv clo_tag e c Γ
       {{ fun s eC s' =>
            let '(e', C) := eC in
            Closure_conversion clo_tag Scope Funs fenv c Γ FVs e e' C /\
            fresh S (next_var s')
       }}) /\
    (forall B B0 FVs c S
       (HD1 : Disjoint _ S (name_in_fundefs B0 :|: bound_var_fundefs B :|: FromList FVs))
       (Hfeq1 : name_in_fundefs B \subset name_in_fundefs B0)
       (Hfeq2 : occurs_free_fundefs B \subset FromList FVs :|: name_in_fundefs B0),
       {{ fun s => CCState (Empty_set _) (Empty_set _) id FVs (var_map s) /\ fresh S (next_var s) }}
         fundefs_closure_conv clo_tag B0 B c
       {{ fun s B' s' =>     
            Closure_conversion_fundefs clo_tag B0 c FVs B B' /\
            fresh S (next_var s')
       }}).
  Proof with now eauto with Ensembles_DB functions_BD.
    eapply exp_def_mutual_ind'; intros.  
    - (* Econstr *)
      edestruct get_vars_sound as (Scope' & Funs' & Hfeq & Hcfv).
      eapply Included_trans; [| eassumption ].
      normalize_occurs_free... 
      simpl. eapply bind_triple; [ eassumption | ].
      intros C s1.
      eapply pre_curry_l. intros Hvars. 
      eapply bind_triple. eapply pre_transfer_r.
      eapply (set_var_entry_bound' v Scope' Funs' fenv FVs).
      intros [] s2.  
      eapply pre_curry_l. intros [Hcc Hfs2].
      eapply bind_triple. 
      +  (* IH *)  
        eapply H. 
        * eapply Disjoint_Included_r; [| eassumption ].
          normalize_bound_var. eapply Union_Included. eapply Union_Included.
          now eauto with Ensembles_DB. 

          eapply Included_trans.
          eapply FV_Union1. eapply Union_Included.
          now eauto with Ensembles_DB. rewrite Hfeq... 

          eapply Included_trans.
          eapply FV_cc_Union1. eapply Union_Included.
          now eauto with Ensembles_DB. 
          eapply Included_trans. eapply project_vars_FV_cc. eassumption.
          eapply Included_trans;
            [| eapply Included_Union_compat; [ eapply Included_Union_compat; [ reflexivity | eassumption ] | reflexivity ]].
          normalize_occurs_free...
        * eapply Included_trans; [| eapply FV_Union1_l ].
          rewrite <- Hfeq. 
          eapply Included_trans; [| eapply Included_Union_compat; [ reflexivity | eassumption ] ].
          normalize_occurs_free. 
          rewrite Union_assoc. 
          rewrite Union_Setminus_Included; eauto with Ensembles_DB typeclass_instances.
      + intros [e' C'] s3. eapply return_triple.
        intros s4 [Hcc' Hfresh]. split.
        econstructor; eassumption. eassumption. 
    - (* Ecase *)
      edestruct get_var_sound as (Scope' & Funs' & Hfeq & Hcfv).
      eapply HFV. now eapply Free_Ecase1.
      simpl. eapply bind_triple; [ eassumption | ].
      intros C1 s1. 
      eapply pre_curry_l. intros Hvar.       
      eapply bind_triple with (post' := fun _ l' s' =>
                                          Forall2
                                            (fun pat pat' : cTag * exp =>
                                               fst pat = fst pat' /\
                                               (exists (C' : exp_ctx) (e' : exp),
                                                   snd pat' = C' |[ e' ]| /\ Closure_conversion clo_tag Scope' Funs' fenv c Γ FVs (snd pat) e' C')) l l' /\ fresh S (next_var s')). 
      { induction l as [| [e1 t1] l IHl ]. 
        * eapply return_triple. intros s Hcc. now constructor.  
        * {  eapply bind_triple.
             - eapply peak_var_map_spec.
             - intros vm s2. eapply pre_curry_l. intros HCC.
               eapply bind_triple.
               + (* apply IH for head *) inv H. eapply H2.
                 eapply Disjoint_Included_r; [| eassumption ].
                 normalize_bound_var. eapply Union_Included. eapply Union_Included.
                 now eauto with Ensembles_DB. 
                 
                 rewrite Hfeq...
                 
                 eapply Included_trans. eapply project_var_FV_cc. eassumption.
                 eapply Included_trans;
                   [| eapply Included_Union_compat; [ eapply Included_Union_compat; [ reflexivity | eassumption ] | reflexivity ]].
                 normalize_occurs_free...
                 
                 rewrite <- Hfeq. 
                 eapply Included_trans; [| eassumption ].
                 normalize_occurs_free...
               + intros [e1' C2] s3.
                 eapply pre_curry_l. intros Hcc.
                 eapply bind_triple. 
                 * eapply push_var_map_spec. eassumption. 
                 * intros [] s4. eapply bind_triple.
                   { eapply IHl.
                     - inv H. eapply H3.
                     - eapply Disjoint_Included_r; [| eassumption ].
                       normalize_bound_var...
                     - eapply Included_trans; [| eassumption ].                       
                       normalize_occurs_free... }
                   intros l' s5. eapply return_triple.
                   intros s6.  intros [Hall Hf]. split; eauto.
                   constructor; eauto. split; eauto.
                   do 2 eexists. split. reflexivity. eassumption. } }  
          
      intros l' s3. eapply return_triple. 
      intros s2 [Hall Hf]. split; eauto.
      econstructor; eassumption. 
    - (* Eproj *)
      edestruct get_var_sound as (Scope' & Funs' & Hfeq & Hcfv).
      eapply HFV. normalize_occurs_free. now left.

      simpl. eapply bind_triple; [ eassumption | ].
      intros C s1.
      eapply pre_curry_l. intros Hvars. 
      eapply bind_triple. eapply pre_transfer_r.
      eapply (set_var_entry_bound' v Scope' Funs' fenv FVs).
      intros [] s2.  
      eapply pre_curry_l. intros [Hcc Hfs2].
      eapply bind_triple. 
      +  (* IH *)  
        eapply H. 
        * eapply Disjoint_Included_r; [| eassumption ].
          normalize_bound_var. eapply Union_Included. eapply Union_Included.
          now eauto with Ensembles_DB. 

          eapply Included_trans.
          eapply FV_Union1. eapply Union_Included.
          now eauto with Ensembles_DB. rewrite Hfeq... 

          eapply Included_trans.
          eapply FV_cc_Union1. eapply Union_Included.
          now eauto with Ensembles_DB. 
          eapply Included_trans. eapply project_var_FV_cc. eassumption.
          eapply Included_trans;
            [| eapply Included_Union_compat; [ eapply Included_Union_compat; [ reflexivity | eassumption ] | reflexivity ]].
          normalize_occurs_free...
        * eapply Included_trans; [| eapply FV_Union1_l ].
          rewrite <- Hfeq. 
          eapply Included_trans; [| eapply Included_Union_compat; [ reflexivity | eassumption ] ].
          normalize_occurs_free. 
          rewrite Union_assoc. 
          rewrite Union_Setminus_Included; eauto with Ensembles_DB typeclass_instances.
      + intros [e' C'] s3. eapply return_triple.
        intros s4 [Hcc' Hfresh]. split.
        econstructor; eassumption. eassumption. 
    - (* Efun *)
      simpl. eapply bind_triple. eapply get_name_no_suff_spec. intros x s1.
      eapply pre_curry_l. intros Hin.
      
      edestruct make_env_spec with (fvs := PS.elements (fundefs_fv f2)) as [Scope' [Funs' [Hfeq Hc]]].
      eapply Included_trans; [| eassumption ].
      normalize_occurs_free. rewrite fundefs_fv_correct...

      eapply bind_triple. eapply Hc.
      intros [c' C] s2. eapply pre_curry_l. intros [C' [Heq Hvars]]. subst.

      eapply bind_triple. eapply pop_var_map_spec.
      eapply var_map_emtpy. intros vm s3.
      eapply pre_curry_l. intros Hvm.
      eapply bind_triple. eapply add_fvs_spec.
      reflexivity. eapply NoDupA_NoDup.
      now eapply PS.elements_spec2w.
      normalize_sets...
      normalize_sets...
      intros [] s4. simpl.
      eapply bind_triple.
      { eapply H. (* IH for functions *)
        + eapply Disjoint_Included; [| | eapply HD1 ].
          normalize_bound_var.
          rewrite <- !Union_assoc. eapply Union_Included.
          eapply Included_trans. eapply name_in_fundefs_bound_var_fundefs. now edb.
          eapply Included_Union_compat. reflexivity.
          replace (@FromList var (PS.elements (fundefs_fv f2))) with (FromSet (fundefs_fv f2)) by reflexivity. 
          rewrite <- fundefs_fv_correct.
          eapply Included_Union_preserv_r. eapply Included_Union_preserv_l.
          eapply Included_trans; [| eassumption ]. normalize_occurs_free...
          edb.
        + reflexivity.
        + rewrite fundefs_fv_correct... }
      + intros B' s5. eapply pre_curry_l. intros HccB.
        eapply bind_triple. eapply push_var_map_spec. now eapply Hvm. 
        intros [] s6.
        eapply bind_triple. eapply add_funs_spec.
        intros [] s7.
        eapply bind_triple.
        { eapply H0. (* IH for exp *)
          + eapply Disjoint_Included_r with (s9 := (x |: (bound_var e :|: name_in_fundefs f2 :|: FV Scope Funs FVs :|: FV_cc Scope Funs fenv Γ))).
            { eapply Union_Included. eapply Union_Included. now edb.
              
              eapply Included_trans. eapply FV_Setminus1; tci. 
              eapply Union_Included. now edb.
              eapply Included_trans. eapply FV_Union2.
              erewrite <- project_vars_FV_eq; [| eassumption ]... 

              eapply Included_trans. eapply FV_cc_Setminus1; tci.
              eapply Union_Included. eapply Union_Included.
              now edb. eapply Included_trans. eapply extend_fundefs'_image. now edb. 
              eapply Included_trans. eapply FV_cc_Union2.
              eapply Union_Included. eapply Union_Included.
              now edb. eapply Included_trans. eapply extend_fundefs'_image. now edb.
              eapply Included_trans. now eapply FV_cc_extend_fundefs.
              eapply Union_Included. now edb. 
              eapply Included_trans. eapply project_vars_FV_cc. eassumption.
              eapply Union_Included.
              replace (@FromList var (PS.elements (fundefs_fv f2))) with (FromSet (fundefs_fv f2)) by reflexivity. 
              rewrite <- fundefs_fv_correct.
              eapply Included_Union_preserv_r. eapply Included_Union_preserv_l. eapply Included_Union_preserv_r. 
              eapply Included_trans; [| eassumption ]. normalize_occurs_free...
              now edb. }

            eapply Union_Disjoint_r. now edb.
            eapply Disjoint_Included; [| | eapply HD1 ]; edb.
            assert (Hsub := name_in_fundefs_bound_var_fundefs f2). 
            normalize_bound_var... 
          + eapply Included_trans; [| eapply FV_Setminus_Union_l ]; tci.
            rewrite <- project_vars_FV_eq; [| eassumption ]; tci. 
            eapply Included_trans; [| eapply Included_Union_compat; [ reflexivity | eassumption ]].
            normalize_occurs_free. rewrite Union_assoc, Union_Setminus_Included; tci; edb. }
        intros [e' Ce] s. eapply return_triple.  
        intros s8. intros [Hcc Hf]. split; eauto.
        econstructor.
        * rewrite fundefs_fv_correct. reflexivity.
        * eapply NoDupA_NoDup. eapply PS.elements_spec2w.
        * eassumption.
        * intros Hc1. eapply HD1. constructor. eassumption.
          inv Hc1; eauto. inv H1; eauto. inv H2; eauto.
          eapply fundefs_fv_correct in H1. left; right. eapply HFV. normalize_occurs_free...
        * eassumption.
        * eassumption. 
        * eapply fresh_monotonic. eassumption. edb.
    - (* Eapp *)
      edestruct get_vars_sound with (xs := v :: l) as [Scope' [Funs' [Heq Hc]]].
      normalize_sets. eapply Included_trans; [| eassumption ]. normalize_occurs_free...
      eapply bind_triple. eassumption.
      intros C1 s1.
      eapply pre_curry_l. intros Hvars. eapply bind_triple. eapply get_name_spec. 
      intros x s2. eapply pre_curry_l; intros Hinx.
      eapply bind_triple. eapply get_name_spec.
      intros y s3. eapply pre_curry_l; intros Hiny.
      eapply return_triple. intros s4.
      intros [Hsc Hf].
      split; eauto. inv Hiny. eapply CC_Eapp; [| eassumption | eassumption | | ].
      eapply Disjoint_Included_r; [| eassumption ].
      eapply Included_trans. eapply project_vars_FV_cc. eassumption.
      rewrite <- Union_assoc. eapply Included_Union_preserv_r.
      eapply Included_Union_compat; [| reflexivity ].
      normalize_sets. eapply Included_trans; [| eassumption ].
      normalize_occurs_free...
      eassumption.
      intros Hc2. subst; eauto.
      eapply fresh_monotonic. eassumption. edb.
    - (* Eprim *)
            edestruct get_vars_sound as (Scope' & Funs' & Hfeq & Hcfv).
      eapply Included_trans; [| eassumption ].
      normalize_occurs_free... 
      simpl. eapply bind_triple; [ eassumption | ].
      intros C s1.
      eapply pre_curry_l. intros Hvars. 
      eapply bind_triple. eapply pre_transfer_r.
      eapply (set_var_entry_bound' v Scope' Funs' fenv FVs).
      intros [] s2.  
      eapply pre_curry_l. intros [Hcc Hfs2].
      eapply bind_triple. 
      +  (* IH *)  
        eapply H. 
        * eapply Disjoint_Included_r; [| eassumption ].
          normalize_bound_var. eapply Union_Included. eapply Union_Included.
          now eauto with Ensembles_DB. 

          eapply Included_trans.
          eapply FV_Union1. eapply Union_Included.
          now eauto with Ensembles_DB. rewrite Hfeq... 

          eapply Included_trans.
          eapply FV_cc_Union1. eapply Union_Included.
          now eauto with Ensembles_DB. 
          eapply Included_trans. eapply project_vars_FV_cc. eassumption.
          eapply Included_trans;
            [| eapply Included_Union_compat; [ eapply Included_Union_compat; [ reflexivity | eassumption ] | reflexivity ]].
          normalize_occurs_free...
        * eapply Included_trans; [| eapply FV_Union1_l ].
          rewrite <- Hfeq. 
          eapply Included_trans; [| eapply Included_Union_compat; [ reflexivity | eassumption ] ].
          normalize_occurs_free. 
          rewrite Union_assoc. 
          rewrite Union_Setminus_Included; eauto with Ensembles_DB typeclass_instances.
      + intros [e' C'] s3. eapply return_triple.
        intros s4 [Hcc' Hfresh]. split.
        econstructor; eassumption. eassumption. 
    - (* Ehalt *) 
      edestruct get_var_sound as [Scope' [Funs' [Heq Hc]]].
      eapply HFV. rewrite occurs_free_Ehalt. reflexivity.
      eapply bind_triple. eassumption.
      intros C1 s1.
      eapply pre_curry_l. intros Hvar.
      eapply return_triple. intros s4.
      intros [Hsc Hf].
      split; eauto. econstructor. eassumption.
    - (* Fcons *) 
      eapply bind_triple. eapply peak_var_map_spec.
      intros vm s1. eapply pre_curry_l. intros Hvm.
      eapply bind_triple. eapply get_name_spec.
      intros G s2.  eapply pre_curry_l. intros HG.
      eapply bind_triple. eapply add_funs_spec.
      intros [] s3.
      eapply bind_triple. eapply add_params_spec.
      intros [] s4.
      eapply bind_triple.
      + (* IH for exp *)
        eapply pre_strenghtening; [| eapply H ].
        * intros s. rewrite Setminus_Empty_set_abs_r, !Union_Empty_set_neut_r. now eauto.
        * eapply Disjoint_Included_r with (s6 :=  G |: (name_in_fundefs B0 :|: bound_var_fundefs (Fcons v t l e f5) :|: FromList FVs)).
          { normalize_bound_var.
            eapply Union_Included. eapply Union_Included. now eauto 20 with Ensembles_DB.
            eapply Union_Included; edb. 
            eapply Union_Included; edb.
            eapply Union_Included; edb. 
            eapply Union_Included; edb. 
            eapply Union_Included; edb. 
            eapply Included_trans. eapply image_monotonic.
            eapply Setminus_Included.
            eapply Included_trans. eapply extend_fundefs'_image. edb. }
          eapply Union_Disjoint_r.
          eapply Disjoint_Setminus_l. reflexivity. 
          eapply Disjoint_Included; [| | eapply HD1 ]; edb.
        * rewrite occurs_free_fundefs_Fcons in Hfeq2.
          eapply Union_Included_l in Hfeq2.
          assert (Hfeq1' := Hfeq1). eapply Union_Included_l in Hfeq1. eapply Union_Included_r in Hfeq1'.
          eapply Included_Union_Setminus_Included in Hfeq2; tci.
          eapply Included_trans. eassumption.
          unfold FV.
          rewrite Union_Setminus_Included; tci.
          rewrite Union_Setminus_Included; tci; edb.
          eapply Singleton_Included_r in Hfeq1. 
          eapply Union_Included; edb.
          now eapply Union_Included; edb. 
          rewrite Union_Setminus_Included; tci; edb.
      + intros [e1 C1] _. eapply pre_curry_l. intros Hcce.
        eapply bind_triple. eapply push_var_map_spec. eassumption. 
        intros [] s5.
        eapply bind_triple.
        * (* IH for fundefs *)
          { eapply H0. 
            - eapply Disjoint_Included; [| | eapply HD1 ]; edb.
              normalize_bound_var...
            - eapply Included_trans; [| eassumption ]...
            - rewrite occurs_free_fundefs_Fcons in Hfeq2.
              assert (Hfeq2' := Hfeq2). eapply Union_Included_l in Hfeq2. eapply Union_Included_r in Hfeq2'.
              eapply Included_Union_Setminus_Included in Hfeq2'; tci.
              eapply Included_trans. eassumption.
              eapply Union_Included. eapply Singleton_Included. right. eapply Hfeq1. now left.
              reflexivity. }
        * intros Bcc s6.
          eapply return_triple. intros s7 [Hcc Hf].
          split; eauto.
          econstructor; try eassumption.
          eapply Disjoint_Included_r; [| eassumption ].
          normalize_bound_var.
          now eauto 20 with Ensembles_DB.
          eapply fresh_monotonic...

    - (* Fnil *)
      eapply return_triple. intros s [H Hf]. split; eauto. constructor.
  Qed.


  Lemma runState_triple {S t} Pre Post (e : state S t) s:
    {{ Pre }} e {{ Post }} ->
    let '(r, s') := runState e s in
    Pre s ->
    Post s r s'.
  Proof.
    intros. unfold triple in *. 
    destruct (runState e s) eqn:Hr. intros Hpre. eapply H in Hpre.
    rewrite Hr in Hpre. eassumption.
  Qed. 
  
  Lemma closure_conversion_top_sound (e : exp) (c : cTag) (Γ : var) (i : iTag) (cenv : cEnv) (names:M.t BasicAst.name) :
    let (e', C) := closure_conversion_top clo_tag e c Γ i cenv names in
    closed_exp e ->
    Closure_conversion clo_tag (Empty_set _) (Empty_set _) id 1%positive Γ [] e e' C.  
  Proof. 
    destruct (closure_conversion_top _ _ _ _ _ _) as [e' C] eqn:Hcc.
    intros Hclo.
    unfold closure_conversion_top in *.
    destruct exp_closure_conv_Closure_conv_sound as [Hexp _].
    unfold triple in Hexp.
    assert (Hdis : Disjoint _ (fun y =>
                                 (Pos.max (max_var e 1) Γ + 1 <= y)%positive)
                            (bound_var e :|: FV (Empty_set var) (Empty_set var) []
                                       :|: FV_cc (Empty_set var) (Empty_set var) id Γ)).
    { unfold FV, FV_cc.
      rewrite !Setminus_Empty_set_abs_r, !Union_Empty_set_neut_r at 1.
      normalize_sets. 
      rewrite !Setminus_Empty_set_abs_r, !image_Empty_set, !Union_Empty_set_neut_l, !Union_Empty_set_neut_r at 1.

      eapply Union_Disjoint_r.
      constructor. intros x Hin. inv Hin. unfold In in *.
      eapply bound_var_leq_max_var  with (y := 1%positive) in H0.
      now zify; omega.
      eapply Disjoint_Singleton_r.
      intros Hc. unfold In in *. zify. omega. } 
    assert (Hfv : occurs_free e \subset FV (Empty_set var) (Empty_set var) []).
    { unfold closed_exp in Hclo. rewrite Hclo. edb. }
    set (s :=  {| var_map := Maps.PTree.empty VarInfo;
                   next_var := (Pos.max (max_var e 1) Γ + 1)%positive;
                   nect_cTag := c;
                   next_iTag := i;
                   cenv := cenv;
                   name_env := names |}). 
    fold s in Hcc.  
    specialize (Hexp e (Empty_set _) (Empty_set _) 1%positive Γ [] id (fun y => Pos.max (max_var e 1%positive) Γ + 1 <= y)%positive Hdis Hfv s).
 
    destruct (runState (exp_closure_conv clo_tag e 1%positive Γ) s)
      as [[ecc Ccc] s'] eqn:Hrn.
    inv Hcc. eapply Hexp. 

    split.
    unfold s; simpl. eapply var_map_emtpy.

    intros x Hin. unfold In.
    eassumption.
  Qed.

End CC_sound. 
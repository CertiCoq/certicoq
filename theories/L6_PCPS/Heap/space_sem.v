(* Space semantics for L6. Part of the CertiCoq project.
 * Author: Zoe Paraskevopoulou, 2016
 *)

From Coq Require Import NArith.BinNat Relations.Relations MSets.MSets
         MSets.MSetRBT Lists.List omega.Omega Sets.Ensembles Relations.Relations
         Classes.Morphisms.
From ExtLib Require Import Structures.Monad Data.Monads.OptionMonad Core.Type.
From L6 Require Import cps cps_util eval List_util Ensembles_util functions
        identifiers Heap.heap Heap.heap_defs.
From Libraries Require Import Coqlib.

Module SpaceSem (H : Heap).

  Module Defs := HeapDefs H.

  Import H Defs.

  (** Non-deterministic semantics with garbage collection *)
  Inductive big_step :
    heap val -> (* The heap. Maps locations to values *)
    env -> (* The environment. Maps variables to locations *)
    exp -> (* The expression to be evaluated *)
    res -> (* The final result, which is a pair of a location an a heap *)
    nat -> (* The concrete cost of the evaluation  *)
    nat -> (* The maximum space required for the evaluation *)
    Type := (* This will bite us. Change it. *)
  | Eval_constr :
      forall (H H' : heap val) (rho rho' : env) (x : var) (t : cTag) (ys :list var)
        (e : exp) (ls : list loc) (l : loc) (r : res) (c : nat) (m : nat),
        getlist ys rho = Some ls ->
        alloc (Vconstr t ls) H = (l, H') ->
        big_step H' (M.set x l rho) e r c m ->
        big_step H rho (Econstr x t ys e) r (c + 1 + length ys) m
  | Eval_proj :
      forall (H : heap val) (rho : env) (x : var) (t : cTag) (n : N)
        (y : var) (e : exp) (l l' : loc) (ls : list loc) (r : res) (c m : nat),
        M.get y rho = Some l ->
        get l H = Some (Vconstr t ls) -> 
        nthN ls n = Some l' ->
        big_step H (M.set x l' rho) e r c m ->
        big_step H rho (Eproj x t n y e) r (c + 1) m
  | Eval_case :
      forall (H : heap val) (rho : env) (y : var) (cl : list (cTag * exp))
        (l : loc) (t : cTag) (ls : list loc)
        (e : exp) (r : res) (c m : nat),
        M.get y rho = Some l ->
        get l H = Some (Vconstr t ls) ->
        findtag cl t = Some e ->
        big_step H rho e r c m ->
        big_step H rho (Ecase y cl) r (c + 1) m
  | Eval_fun :
      forall (H H' : heap val) (rho : env) (B : fundefs)
        (l : loc) (e : exp) (r : res)
        (c : nat) (m : nat),
        alloc (Vfun rho B) H = (l, H') ->  
        big_step H' (def_funs B l rho) e r c m ->
        big_step H rho (Efun B e) r (c + fundefs_num_fv B + 1) m
  | Eval_app :
      forall (H : heap val) (rho rho' rho'' : env) (B : fundefs) (f : var) (t : cTag)
        (xs : list var) (e : exp) (l : loc) (ls : list loc) (ys : list var)
        (r : res) (c : nat) (m : nat),
        M.get f rho = Some l ->
        get l H = Some (Vfun rho' B) -> 
        getlist ys rho = Some ls ->
        find_def f B = Some (t, xs, e) ->
        setlist xs ls (def_funs B l rho') = Some rho'' ->
        big_step H rho'' e r c m ->
        big_step H rho (Eapp f t ys) r (c + 1 + length ys) m
  | Eval_halt :
      forall H rho x l m,
        M.get x rho = Some l ->
        size_heap H = m ->
        big_step H rho (Ehalt x) (l, H) 1 m
  | Eval_GC :
      forall (H H1 H2 : heap val) (rho : env) (e : exp) (r : res) (c : nat) (m m' : nat),
        (* Garbage collect H *)
        collect (env_locs rho (occurs_free e)) H H1 ->
        (* The live part of H. *)
        live (env_locs rho (occurs_free e)) H H2 ->
        size_heap H1 = m' ->
        big_step H1 rho e r c m ->
        big_step H rho e r (c + m') (max m m').
  

  (** Deterministic semantics with perfect garbage collection
   * The execution time cost model does not account for the cost of GC  *)
  Inductive big_step_perfect_GC :
    heap val -> (* The heap. Maps locations to values *)
    env -> (* The environment. Maps variables to locations *)
    exp -> (* The expression to be evaluated *)
    res -> (* The final result, which is a pair of a location an a heap *)
    nat -> (* The concrete cost of the evaluation  *)
    nat -> (* The maximum space required for the evaluation *)
    Prop :=
  | Eval_constr_per :
      forall (H H' H'' : heap val) (rho rho' : env) (x : var) (t : cTag) (ys :list var)
        (e : exp) (ls : list loc) (l : loc) (r : res) (c m m' : nat),
        getlist ys rho = Some ls ->
        alloc (Vconstr t ls) H = (l, H') ->

        (* collect H' *)
        live (env_locs (M.set x l rho) (occurs_free e)) H' H'' ->
        size_heap H' = m' ->
        
        big_step_perfect_GC H'' (M.set x l rho) e r c m ->

        big_step_perfect_GC H rho (Econstr x t ys e) r (c + 1 + length ys) (max m m')
  | Eval_proj_per :
      forall (H H' : heap val) (rho : env) (x : var) (t : cTag) (n : N)
        (y : var) (e : exp) (l l' : loc) (ls : list loc) (r : res) (c m m' : nat),
        M.get y rho = Some l ->
        get l H = Some (Vconstr t ls) -> 
        nthN ls n = Some l' ->

        (* collect H *)
        live (env_locs (M.set x l' rho) (occurs_free e)) H H' ->
        size_heap H = m' ->

        big_step_perfect_GC H' (M.set x l' rho) e r c m ->

        big_step_perfect_GC H rho (Eproj x t n y e) r (c + 1) (max m m')
  | Eval_case_per :
      forall (H H' : heap val) (rho : env) (y : var) (cl : list (cTag * exp))
        (l : loc) (t : cTag) (ls : list loc) (e : exp) (r : res) (c m m' : nat),
        M.get y rho = Some l ->
        get l H = Some (Vconstr t ls) ->
        findtag cl t = Some e ->

        (* collect H *)
        live ((env_locs rho) (occurs_free e)) H H' ->
        size_heap H = m' ->

        big_step_perfect_GC H' rho e r c m ->
        
        big_step_perfect_GC H rho (Ecase y cl) r (c + 1) (max m m')
  | Eval_fun_per :
      forall (H H' H'': heap val) (rho : env) (B : fundefs)
        (l : loc) (e : exp) (r : res) (c : nat) (m m' : nat),
        alloc (Vfun rho B) H = (l, H') ->
 
        (* collect H' *)
        collect ((env_locs (def_funs B l rho)) (occurs_free e)) H' H'' ->
        size_heap H' = m' ->

        big_step_perfect_GC H'' (def_funs B l rho) e r c m ->

        big_step_perfect_GC H rho (Efun B e) r (c + fundefs_num_fv B + 1) (max m m')
  | Eval_app_per : 
      forall (H H' : heap val) (rho rho' rho'' : env) (B : fundefs) (f : var) (t : cTag)
        (xs : list var) (e : exp) (l : loc) (ls : list loc) (ys : list var)
        (r : res) (size c m m' : nat),
        M.get f rho = Some l ->
        get l H = Some (Vfun rho' B) -> 
        getlist ys rho = Some ls ->
        find_def f B = Some (t, xs, e) ->
        setlist xs ls (def_funs B l rho') = Some rho'' ->

        (* collect H *)
        collect ((env_locs (def_funs B l rho)) (occurs_free e)) H H' ->
        size_heap H = m' ->

        big_step_perfect_GC H' rho'' e r c m ->
        big_step_perfect_GC H rho (Eapp f t ys) r (c + 1 + length ys) (max m m')
  | Eval_halt_per :
      forall H rho x l m,
        M.get x rho = Some l ->
        size_heap H = m ->
        big_step_perfect_GC H rho (Ehalt x) (l, H) 1 m.


 (** Deterministic semantics with garbage collection when needed.
   * The execution time cost model accounts for the cost of GC  *)
 Context (Hmax : nat).
 
 Inductive big_step_GC_when_needed :
    heap val -> (* The heap. Maps locations to values *)
    env -> (* The environment. Maps variables to locations *)
    exp -> (* The expression to be evaluated *)
    res -> (* The final result, which is a pair of a location an a heap *)
    nat -> (* The concrete cost of the evaluation  *)
    nat -> (* The maximum space required for the evaluation *)
    Prop :=
  | Eval_constr_need :
      forall (H H' : heap val) (rho rho' : env) (x : var) (t : cTag) (ys :list var)
        (e : exp) (ls : list loc) (l : loc) (r : res) (c m : nat),

        (* No GC is needed *)
        size_heap H < Hmax ->

        getlist ys rho = Some ls ->
        alloc (Vconstr t ls) H = (l, H') ->
        big_step_GC_when_needed H' (M.set x l rho) e r c m ->
        big_step_GC_when_needed H rho (Econstr x t ys e) r (c + 1 + length ys) m
  | Eval_proj_need :
      forall (H : heap val) (rho : env) (x : var) (t : cTag) (n : N)
        (y : var) (e : exp) (l l' : loc) (ls : list loc) (r : res) (c m : nat),

        (* No GC is needed *)
        size_heap H < Hmax ->

        M.get y rho = Some l ->
        get l H = Some (Vconstr t ls) -> 
        nthN ls n = Some l' ->
        big_step_GC_when_needed H (M.set x l' rho) e r c m ->
        big_step_GC_when_needed H rho (Eproj x t n y e) r (c + 1) m
  | Eval_case_need :
      forall (H : heap val) (rho : env) (y : var) (cl : list (cTag * exp))
        (l : loc) (t : cTag) (ls : list loc)
        (e : exp) (r : res) (size c m : nat),

        (* No GC is needed *)
        size_heap H < Hmax ->

        M.get y rho = Some l ->
        get l H = Some (Vconstr t ls) ->
        findtag cl t = Some e ->
        big_step_GC_when_needed H rho e r c m ->
        big_step_GC_when_needed H rho (Ecase y cl) r (c + 1) m
  | Eval_fun_need :
      forall (H H' : heap val) (rho : env) (B : fundefs)
        (l : loc) (e : exp) (r : res) (size c m : nat),

        (* No GC is needed *)
        size_heap H < Hmax ->

        alloc (Vfun rho B) H = (l, H') ->  
        big_step_GC_when_needed H' (def_funs B l rho) e r c m ->
        big_step_GC_when_needed H rho (Efun B e) r (c + fundefs_num_fv B + 1) m
  | Eval_app_need : 
      forall (H : heap val) (rho rho' rho'' : env) (B : fundefs) (f : var) (t : cTag)
        (xs : list var) (e : exp) (l : loc) (ls : list loc) (ys : list var)
        (r : res) (size c m : nat),

        (* No GC is needed *)
        size_heap H < Hmax ->

        M.get f rho = Some l ->
        get l H = Some (Vfun rho' B) -> 
        getlist ys rho = Some ls ->
        find_def f B = Some (t, xs, e) ->
        setlist xs ls (def_funs B l rho') = Some rho'' ->
        big_step_GC_when_needed H rho'' e r c m ->
        big_step_GC_when_needed H rho (Eapp f t ys) r (c + 1 + length ys) m
  | Eval_halt_need :
      forall H rho x l m,
        M.get x rho = Some l ->
        size_heap H = m ->
        big_step_GC_when_needed H rho (Ehalt x) (l, H) 1 m
  | Eval_GC_need :
      forall (H H' : heap val) (rho : env) (e : exp) (r : res) (c : nat) (m m' : nat),
        (* Garbage collect H *)
        live (env_locs rho (occurs_free e)) H H' ->
        size_heap H' = m' ->
        (* Collect only if it's needed *)
        Hmax <= m' ->
        big_step_GC_when_needed H' rho e r c m ->
        big_step_GC_when_needed H rho e r (c + m') (max m m').

   Fixpoint noGC {Heap rho e v c m} (H : big_step Heap rho e v c m) : Prop :=
    match H with
      | Eval_constr Hp Hp' rho rho' x t ys e ls l r c m x0 x1 H' =>
        noGC H'
      | Eval_proj H rho x t n y e l l' ls r c m x0 x1 x2 H' =>
        noGC H'
      | Eval_case H rho y cl l t ls e r c m x x0 x1 H' =>
        noGC H'
      | Eval_fun Hp Hp' rho B l e r c m x H' =>
        noGC H'
      | Eval_app H rho rho' rho'' B f t xs e l ls ys r c m x x0 x1 x2 x3 H' =>
        noGC H'
      | Eval_halt _ _ _ _ _ _ _ => True
      | Eval_GC _ _ _ _ _ _ _ _ _ _ _ _ _ => False
    end.

   (** Size of the [big_step] derivation *)
   Fixpoint size_big_step {Heap rho e v c m} (H : big_step Heap rho e v c m) : nat :=
    match H with
      | Eval_constr Hp Hp' rho rho' x t ys e ls l r c m x0 x1 H' =>
        S (size_big_step H')
      | Eval_proj H rho x t n y e l l' ls r c m x0 x1 x2 H' =>
        S (size_big_step H')
      | Eval_case H rho y cl l t ls e r c m x x0 x1 H' =>
        S (size_big_step H')
      | Eval_fun Hp Hp' rho B l e r c m x H' =>
        S (size_big_step H')
      | Eval_app H rho rho' rho'' B f t xs e l ls ys r c m x x0 x1 x2 x3 H' =>
        S (size_big_step H')
      | Eval_halt _ _ _ _ _ _ _ => 0
      | Eval_GC _ _ _ _ _ _ _ _ _ _ _ _ H' => S (size_big_step H')
    end.
   

   Lemma big_step_deterministic  H1 H2 rho1 rho2 e r1 c1 m1 r2 c2 m2 :
     well_formed (reach' H1 (env_locs rho1 (occurs_free e))) H1 ->
     well_formed (reach' H2 (env_locs rho2 (occurs_free e))) H2 ->
     env_locs rho1 (occurs_free e) \subset dom H1 ->
     env_locs rho2 (occurs_free e) \subset dom H2 ->
     big_step H1 rho1 e r1 c1 m1 -> (* D1 *)
     big_step H2 rho2 e r2 c2 m2 -> (* D2 *)
     (occurs_free e) |- (H1, rho1) ⩪ (H2, rho2) ->
     r1 ≈ r2.
   Proof with now eauto with Ensembles_DB.
     (* Lexicographic induction on the size of the first derivation and the size of the second derivation *)
     intros Hwf1 Hwf2 Hwfe1 Hwfe2 Hbs1 Hbs2. remember (size_big_step Hbs1) as n.
     revert H1 H2 rho1 rho2 e r1 c1 m1 r2 c2 m2 Hwf1 Hwf2 Hwfe1 Hwfe2 Hbs1 Heqn Hbs2.
     induction n as [n IH1] using lt_wf_rec1.
     intros H1 H2 rho1 rho2 e r1 c1 m1 r2 c2 m2 Hwf1 Hwf2 Hwfe1 Hwfe2 Hbs1 Heqn Hbs2.
     subst.
     remember (size_big_step Hbs2) as m.
     revert H1 H2 rho1 rho2 e r1 c1 m1 r2 c2 m2 Hwf1 Hwf2 Hwfe1 Hwfe2 Hbs1 Hbs2 Heqm IH1.
     induction m as [m IH2] using lt_wf_rec1.  
     intros H1 H2 rho1 rho2 e r1 c1 m1 r2 c2 m2 Hwf1 Hwf2 Hwfe1 Hwfe2 Hbs1 Hbs2 Heqm IH1 Heq.
     destruct Hbs1; simpl in *. 
     - (* D1 : Eval_constr *)
       subst m. remember (Econstr x t ys e) as e'. destruct Hbs2; inv Heqe'; simpl in *.
       + (* D2 : Eval_constr *)
         eapply IH1 with (Hbs1 := Hbs1); [ | | | | | reflexivity | |]. 
         * omega.
         * eapply well_formed_antimon. eapply reach'_set_monotonic.
           eapply env_locs_monotonic. now apply occurs_free_Econstr_Included.
           eapply well_formed_reach_alloc with (H := H); eauto.
           eapply Included_trans; [| now apply reach'_extensive ].
           simpl. eapply FromList_env_locs; eauto. normalize_occurs_free...
         * eapply well_formed_antimon. eapply reach'_set_monotonic.
           eapply env_locs_monotonic. now apply occurs_free_Econstr_Included.
           eapply well_formed_reach_alloc with (H := H0); eauto.
           eapply Included_trans; [| now apply reach'_extensive ].
           simpl. eapply FromList_env_locs; eauto. normalize_occurs_free...
         * eapply Included_trans.
           eapply env_locs_monotonic. now apply occurs_free_Econstr_Included.
           eapply Included_trans. eapply env_locs_set_Inlcuded.
           eapply Union_Included. eapply Singleton_Included.
           now eapply alloc_In_dom; eauto.
           eapply Included_trans. eassumption.
           eapply dom_subheap. now eapply alloc_subheap; eauto.
         * eapply Included_trans.
           eapply env_locs_monotonic. now apply occurs_free_Econstr_Included.
           eapply Included_trans. eapply env_locs_set_Inlcuded.
           eapply Union_Included. eapply Singleton_Included.
           now eapply alloc_In_dom; eauto.
           eapply Included_trans. eassumption.
           eapply dom_subheap. now eapply alloc_subheap; eauto.
         * now apply Hbs2.
         * eapply (heap_env_equiv_set_alloc_Vconstr _ _ _ H H0); eauto. 
           eapply reach'_closed. eassumption. eassumption.
           eapply reach'_closed. eassumption. eassumption.
           eapply Included_trans; [| now apply reach'_extensive ].
           eapply env_locs_monotonic. normalize_occurs_free...
           eapply Included_trans; [| now apply reach'_extensive ].
           eapply env_locs_monotonic. normalize_occurs_free...
           eapply Included_trans; [| now apply reach'_extensive ].
           eapply FromList_env_locs; eauto. normalize_occurs_free...
           eapply Included_trans; [| now apply reach'_extensive ].
           eapply FromList_env_locs; eauto. normalize_occurs_free...
           eapply heap_env_equiv_antimon. eassumption.
           eapply Setminus_Included_Included_Union. now eapply occurs_free_Econstr_Included.
           eapply Forall2_symm_strong; [| eapply heap_env_equiv_getlist_Forall2 ]. 
           intros. now symmetry. now split; eapply Heq.
           rewrite occurs_free_Econstr... eassumption. eassumption.
       + (* D2 : Eval_GC *)
         assert (Hex : exists  (Hbs1' : big_step H rho (Econstr x t ys e) r (c + 1 + length ys) m0),
                         size_big_step Hbs1' = S (size_big_step Hbs1)).
         { exists (Eval_constr H H' rho (M.set x l rho)  x t ys e ls l r c m0 e0 e1 Hbs1).
           reflexivity. }
         destruct Hex as [Hbs1' Hsize]. 
         eapply IH2 with (Hbs2 := Hbs2) (Hbs1 := Hbs1'); [ | | | | | reflexivity | | ]; try eassumption.
         * omega.
         * rewrite <- reach'_heap_eq; eauto. eapply well_formed_heap_eq.
           eassumption. now eapply reach'_closed; eauto.
           eapply collect_heap_eq. eassumption.
           eapply collect_heap_eq. eassumption.      
         * eapply heap_eq_dom; [| eassumption | now apply reach'_extensive ].
           eapply collect_heap_eq. eassumption.
         * intros. subst. eapply IH1 with (Hbs1 := Hbs0); [| | | | | reflexivity | |]; try eassumption.
           omega.
         * edestruct Equivalence_heap_env_equiv. eapply Equivalence_Transitive; eauto.
           eapply reach_heap_env_equiv.
           eapply collect_heap_eq. eassumption.
     - (* D1 : Eval_proj *)
       subst m. remember (Eproj x t n y e) as e'. destruct Hbs2; inv Heqe'; simpl in *.
       + (* D2 : Eval_proj *)
         eapply IH1 with (Hbs1 := Hbs1); [ | | | | | reflexivity | |]; try eassumption.
         * omega.
         * eapply well_formed_antimon. eapply reach'_set_monotonic.
           eapply Included_trans.
           eapply env_locs_monotonic. now apply occurs_free_Eproj_Included.
           eapply env_locs_set_Inlcuded.
           rewrite <-reach_spec. eassumption. now eauto with Ensembles_DB.
           eapply Union_Included.
           eapply Singleton_Included. eexists 1.
           split. now constructor. eexists l. eexists.
           repeat split; eauto; simpl. now eexists; split; eauto.
           now eapply nthN_In; eauto.
           now apply reach'_extensive.
         * eapply well_formed_antimon. eapply reach'_set_monotonic.
           eapply Included_trans.
           eapply env_locs_monotonic. now apply occurs_free_Eproj_Included.
           eapply env_locs_set_Inlcuded.
           rewrite <-reach_spec. eassumption. now eauto with Ensembles_DB.
           eapply Union_Included.
           eapply Singleton_Included. eexists 1. split.
           now constructor.
           eexists l0. eexists. repeat split; eauto; simpl.
           now eexists; split; eauto.
           now eapply nthN_In; eauto.
           now apply reach'_extensive.
         * eapply Included_trans.
           eapply env_locs_monotonic. now apply occurs_free_Eproj_Included.
           eapply Included_trans. eapply env_locs_set_Inlcuded.
           eapply Union_Included; [| eassumption ].
           eapply Singleton_Included. eapply reachable_in_dom; eauto.
           eexists 1. split.
           now constructor.
           eexists l. eexists. repeat split; eauto; simpl.
           now eexists; split; eauto. now eapply nthN_In; eauto.
         * eapply Included_trans.
           eapply env_locs_monotonic. now apply occurs_free_Eproj_Included.
           eapply Included_trans. eapply env_locs_set_Inlcuded.
           eapply Union_Included; [| eassumption ].
           eapply Singleton_Included. eapply reachable_in_dom; eauto.
           eexists 1. split.
           now constructor.
           eexists l0. eexists. repeat split; eauto; simpl.
           now eexists; split; eauto. now eapply nthN_In; eauto.
         * eapply heap_env_equiv_set.
           eapply heap_env_equiv_antimon. eassumption.
           eapply Setminus_Included_Included_Union. now eapply occurs_free_Eproj_Included.
           eapply Heq in e0. destruct e0 as [l2' [Hget' Heq']]. rewrite e4  in Hget'. inv Hget'.
           intros n'; split.
           { eapply Heq' with (n := S n') in e1.
             destruct e1 as [v2 [Hgetv2 Hequiv]]. rewrite e5 in Hgetv2. inv Hgetv2.
             edestruct (@Forall2_nthN loc loc) as [l1' [Hnth Heql1']]; [ eapply Hequiv with (i := n')| | ]; eauto.
             rewrite e6 in Hnth; inv Hnth. now rewrite <- res_approx_fuel_eq. }
           { eapply Heq' with (n := S n') in e5.
             destruct e5 as [v2 [Hgetv2 Hequiv]]. rewrite e1 in Hgetv2. inv Hgetv2.
             edestruct (@Forall2_nthN loc loc) as [l1' [Hnth Heql1']]; [ eapply Hequiv with (i := n')| | ]; eauto.
             rewrite e2 in Hnth; inv Hnth. now rewrite <- res_approx_fuel_eq. }
           now eauto.
       + (* D2 : Eval_GC *)
         assert (Hex : exists  (Hbs1' : big_step H rho (Eproj x t n y e) r (c + 1) m0), size_big_step Hbs1' = S (size_big_step Hbs1)).
         { exists (Eval_proj H rho x t n y e l l' ls r c m0 e0 e1 e2 Hbs1).
           reflexivity. }
        destruct Hex as [Hbs1' Hsize].
        eapply IH2 with (Hbs2 := Hbs2) (Hbs1 := Hbs1'); [ | | | | | reflexivity | | ]; try eassumption.
         * omega.
         * rewrite <- reach'_heap_eq; eauto. eapply well_formed_heap_eq.
           eassumption. now eapply reach'_closed; eauto.
           eapply collect_heap_eq. eassumption.
           eapply collect_heap_eq. eassumption.
         * eapply heap_eq_dom; [| eassumption | now apply reach'_extensive ].
           eapply collect_heap_eq. eassumption.
         * intros. subst. eapply IH1 with (Hbs1 := Hbs0); [| | | | | reflexivity | |]; try eassumption.
           omega.
         * edestruct Equivalence_heap_env_equiv. eapply Equivalence_Transitive; eauto.
           eapply reach_heap_env_equiv.
           eapply collect_heap_eq. eassumption.
     - (* D1 : Eval_case *)
       subst m. remember (Ecase y cl) as e'. destruct Hbs2; inv Heqe'; simpl in *.
       + (* D2 : Eval_case *)
         eapply Heq in e0. edestruct e0 as [l' [Hget Heql']]. rewrite e4 in Hget; inv Hget.
         eapply Heql' with (n := 0) in e1. destruct e1 as [v' [Hget' Heql'']]. rewrite e5 in Hget'. inv Hget'.
         eapply Heql' with (n := 0) in e5.  inv Heql''. rewrite e2 in e6; inv e6.
         eapply IH1 with (Hbs1 := Hbs1); [ | | | | | reflexivity | | ]; try eassumption; eauto.   
         * eapply well_formed_antimon; [| eassumption ].
           eapply reach'_set_monotonic. eapply env_locs_monotonic.
           rewrite occurs_free_Ecase_Included. reflexivity.
           eapply cps_util.findtag_In. eassumption.
         * eapply well_formed_antimon; [| eassumption ].
           eapply reach'_set_monotonic. eapply env_locs_monotonic.
           rewrite occurs_free_Ecase_Included. reflexivity.
           eapply cps_util.findtag_In. eassumption.
         * eapply Included_trans; [| eassumption ].
           eapply env_locs_monotonic.
           rewrite occurs_free_Ecase_Included. reflexivity.
           eapply cps_util.findtag_In. eassumption.
         * eapply Included_trans; [| eassumption ].
           eapply env_locs_monotonic.
           rewrite occurs_free_Ecase_Included. reflexivity.
           eapply cps_util.findtag_In. eassumption.
         * eapply heap_env_equiv_antimon.
           eassumption.
           rewrite occurs_free_Ecase_Included. reflexivity.
           eapply cps_util.findtag_In. eassumption.
         * eauto.
       + (* D2 : Eval_GC *)
         assert (Hex : exists  (Hbs1' : big_step H rho (Ecase y cl) r (c + 1) m0), size_big_step Hbs1' = S (size_big_step Hbs1)).
         { exists (Eval_case H rho y cl l t ls e r c m0 e0 e1 e2 Hbs1). reflexivity. }
         destruct Hex as [Hbs1' Hsize].
         eapply IH2 with (Hbs2 := Hbs2) (Hbs1 := Hbs1'); [ | | | | | reflexivity | | ]; try eassumption.
         * omega.
         * rewrite <- reach'_heap_eq; eauto. eapply well_formed_heap_eq.
           eassumption. now eapply reach'_closed; eauto.
           eapply collect_heap_eq. eassumption.
           eapply collect_heap_eq. eassumption.
         * eapply heap_eq_dom; [| eassumption | now apply reach'_extensive ].
           eapply collect_heap_eq. eassumption.
         * intros. subst. eapply IH1 with (Hbs1 := Hbs0); [| | | | | reflexivity | |]; try eassumption.
           omega.
         * edestruct Equivalence_heap_env_equiv. eapply Equivalence_Transitive; eauto.
           eapply reach_heap_env_equiv.
           eapply collect_heap_eq. eassumption.
     - (* D1 : Eval_fun *)
       subst m. remember (Efun B e) as e'. destruct Hbs2; inv Heqe'; simpl in *.
       + (* D2 : Eval_fun *)
         eapply IH1 with (Hbs1 := Hbs1); [| | | | | reflexivity | eassumption |].
         * omega.
         * eapply well_formed_antimon. eapply reach'_set_monotonic.
           eapply env_locs_monotonic. now apply occurs_free_Efun_Included.
           eapply well_formed_reach_alloc_def_funs; eauto.
           simpl. eapply Included_trans; [| now eapply reach'_extensive ].
           eapply env_locs_monotonic. normalize_occurs_free...
         * eapply well_formed_antimon. eapply reach'_set_monotonic.
           eapply env_locs_monotonic. now apply occurs_free_Efun_Included.
           eapply well_formed_reach_alloc_def_funs; eauto.
           simpl. eapply Included_trans; [| now eapply reach'_extensive ].
           eapply env_locs_monotonic. normalize_occurs_free...
         * eapply Included_trans.
           eapply env_locs_monotonic. now apply occurs_free_Efun_Included.
           eapply Included_trans. eapply env_locs_def_funs_Included.
           eapply Union_Included.
           eapply Included_trans. eassumption.
           eapply dom_subheap. now eapply alloc_subheap; eauto.
           eapply Singleton_Included.
           now eapply alloc_In_dom; eauto.
         * eapply Included_trans.
           eapply env_locs_monotonic. now apply occurs_free_Efun_Included.
           eapply Included_trans. eapply env_locs_def_funs_Included.
           eapply Union_Included.
           eapply Included_trans. eassumption.
           eapply dom_subheap. now eapply alloc_subheap; eauto.
           eapply Singleton_Included.
           now eapply alloc_In_dom; eauto.
         * eapply heap_env_equiv_antimon; [| now apply occurs_free_Efun_Included ].
           eapply (heap_env_equiv_def_funs_alloc _ _ _ H H0).
           now eapply reach'_closed; eauto.
           now eapply reach'_closed; eauto.
           eapply Included_trans; [| now apply reach'_extensive ].
           eapply env_locs_monotonic...
           eapply Included_trans; [| now apply reach'_extensive ].
           eapply env_locs_monotonic...
           rewrite Setminus_Union_distr, Setminus_Same_set_Empty_set, Union_Empty_set_neut_r.
           rewrite Setminus_Disjoint. normalize_occurs_free...
           normalize_occurs_free.
           eapply Union_Disjoint_l.
           constructor. intros x Hc. inv Hc; eapply fun_names_not_free_in_fundefs; eauto.
           eapply Disjoint_Setminus_l...
           rewrite Setminus_Union_distr, Setminus_Same_set_Empty_set, Union_Empty_set_neut_r.
           eapply heap_env_equiv_antimon; [ eassumption | ]...
           eassumption. eassumption.
       + (* D2 : Eval_GC *)
         assert (Hex : exists  (Hbs1' : big_step H rho (Efun B e) r (c + fundefs_num_fv B + 1) m0), size_big_step Hbs1' = S (size_big_step Hbs1)).
         { exists (Eval_fun H H' rho B l e r c m0 e0 Hbs1).
           reflexivity. }
         destruct Hex as [Hbs1' Hsize].
         eapply IH2 with (Hbs2 := Hbs2) (Hbs1 := Hbs1'); [| | |  | | reflexivity | | ]; try eassumption.
         * omega.
         * rewrite <- reach'_heap_eq; eauto. eapply well_formed_heap_eq.
           eassumption. now eapply reach'_closed; eauto.
           eapply collect_heap_eq. eassumption.
           eapply collect_heap_eq. eassumption.
         * eapply heap_eq_dom; [| eassumption | now apply reach'_extensive ].
           eapply collect_heap_eq. eassumption.
         * intros. subst. eapply IH1 with (Hbs1 := Hbs0); [| | | | | reflexivity | |]; try eassumption.
           omega.
         * edestruct Equivalence_heap_env_equiv. eapply Equivalence_Transitive; eauto.
           eapply reach_heap_env_equiv. 
           eapply collect_heap_eq. eassumption.
     - (* D1 : Eval_app *)
       subst m. remember (Eapp f t ys) as e'. destruct Hbs2; inv Heqe'; simpl in *.
       + (* D2 : Eval_app *)
         assert (r ≈ r0).
         { assert (Hgetf' := e6). assert (Hgetl' := e7).
           eapply Heq in e6. destruct e6 as [l' [Hget Hequiv]].
           rewrite Hget in e0; inv e0. eapply Hequiv with (n := 1) in e7.
           destruct e7 as [v2 [Hget2 Heq2]]. rewrite Hget2 in e1. inv e1.
           inv Heq2. rewrite e9 in e3; inv e3.
           assert (Hreach1 : reach' H (env_locs rho' (occurs_free_fundefs B)) \subset
                             reach' H (env_locs rho (occurs_free (Eapp f t ys)))).
           { rewrite (reach_unfold H (env_locs rho _) ).
             eapply Included_Union_preserv_r. eapply reach'_set_monotonic.
             intros l1 H1. do 2 eexists. repeat split; eauto.
             eexists f. now split; eauto. }
           assert (Hreach2 : reach' H0 (env_locs rho'0 (occurs_free_fundefs B)) \subset
                             reach' H0 (env_locs rho0 (occurs_free (Eapp f t ys)))).
           { rewrite (reach_unfold H0 (env_locs rho0 _) ).
             eapply Included_Union_preserv_r. eapply reach'_set_monotonic.
             intros l1 [x [Hin1 Hget1]].
             repeat eexists; eauto. repeat eexists; eauto. }
           eapply IH1 with (Hbs1 := Hbs1); [| | | | | reflexivity | eassumption |].         
           - omega.
           - eapply well_formed_antimon; [| eassumption ].
             eapply Included_trans. eapply reach'_set_monotonic.
             eapply env_locs_monotonic. eapply occurs_free_in_fun.
             eapply find_def_correct. eassumption. rewrite Union_commut.
             eapply Included_trans. eapply reach'_set_monotonic.
             eapply env_locs_setlist_Included; eauto.
             rewrite (Union_commut (name_in_fundefs B) (occurs_free_fundefs B)).
             eapply Included_trans. eapply reach'_set_monotonic. eapply Included_Union_compat.
             eapply env_locs_def_funs_Included. reflexivity.
             rewrite !reach'_Union. eapply Union_Included; [ eapply Union_Included |].
             + eassumption.
             + eapply reach'_set_monotonic.
               intros l1 H1. inv H1. do 2 eexists. repeat split; eauto.
               eassumption. 
             + eapply reach'_set_monotonic.
               intros l1 H1. edestruct (@getlist_In_val loc) as [y [Hin' Hget']]; [| eassumption |]; eauto.
               exists y; split; eauto.
           - eapply well_formed_antimon; [| eassumption ].
             eapply Included_trans. eapply reach'_set_monotonic.
             eapply env_locs_monotonic. eapply occurs_free_in_fun.
             eapply find_def_correct. eassumption. rewrite Union_commut.
             eapply Included_trans. eapply reach'_set_monotonic.
             eapply env_locs_setlist_Included; eauto.
             rewrite (Union_commut (name_in_fundefs B) (occurs_free_fundefs B)).
             eapply Included_trans. eapply reach'_set_monotonic. eapply Included_Union_compat.
             eapply env_locs_def_funs_Included. reflexivity.
             rewrite !reach'_Union. eapply Union_Included; [ eapply Union_Included |].
             + eassumption.
             + eapply reach'_set_monotonic.
               intros l1 H1. inv H1. do 2 eexists. repeat split; eauto.
               eassumption. 
             + eapply reach'_set_monotonic.
               intros l1 H1. edestruct (@getlist_In_val loc) as [y [Hin' Hget']]; [| eassumption |]; eauto.
               exists y; split; eauto.
           - eapply Included_trans. eapply env_locs_monotonic. eapply occurs_free_in_fun.
             eapply find_def_correct. eassumption. rewrite Union_commut.
             eapply Included_trans. eapply env_locs_setlist_Included; eauto.
             rewrite (Union_commut (name_in_fundefs B) (occurs_free_fundefs B)).
             eapply Included_trans. eapply Included_Union_compat.
             eapply env_locs_def_funs_Included. reflexivity.
             eapply Union_Included; [ eapply Union_Included |].
             eapply Included_trans; [| now eapply reachable_in_dom; eauto ].
             eapply Included_trans. now apply reach'_extensive. eassumption.
             eapply Singleton_Included. now eexists; eauto.
             eapply Included_trans; [| eassumption ].
             eapply FromList_env_locs; eauto. normalize_occurs_free...
           - eapply Included_trans. eapply env_locs_monotonic. eapply occurs_free_in_fun.
             eapply find_def_correct. eassumption. rewrite Union_commut.
             eapply Included_trans. eapply env_locs_setlist_Included; eauto.
             rewrite (Union_commut (name_in_fundefs B) (occurs_free_fundefs B)).
             eapply Included_trans. eapply Included_Union_compat.
             eapply env_locs_def_funs_Included. reflexivity.
             eapply Union_Included; [ eapply Union_Included |].
             eapply Included_trans; [| now eapply reachable_in_dom; eauto ].
             eapply Included_trans. now apply reach'_extensive. eassumption.
             eapply Singleton_Included. now eexists; eauto.
             eapply Included_trans; [| eassumption ].
             eapply FromList_env_locs; eauto. normalize_occurs_free...
           - eapply heap_env_equiv_setlist; eauto.
             eapply heap_env_equiv_def_funs; eauto.
             eapply heap_env_equiv_antimon.
             eapply (heap_env_equiv_Vfun _ rho rho0); eauto. symmetry. eassumption.
             rewrite Setminus_Union. apply Setminus_Included_Included_Union.
             eapply Included_trans. eapply occurs_free_in_fun.
             eapply find_def_correct; eauto. now eauto with Ensembles_DB.
             symmetry. eassumption. 
             eapply heap_env_equiv_getlist_Forall2; eauto.
             normalize_occurs_free...
           - eauto. }
         firstorder.
       + (* D2 : Eval_GC *)
         assert (Hex : exists (Hbs1' : big_step H rho (Eapp f t ys) r (c + 1 + length ys) m0),
                         size_big_step Hbs1' = S (size_big_step Hbs1)).
         { exists (Eval_app H rho rho' rho'' B f t xs e l ls ys r c m0 e0 e1 e2 e3 e4 Hbs1).
           reflexivity. }
         destruct Hex as [Hbs1' Hsize].
         eapply IH2 with (Hbs2 := Hbs2) (Hbs1 := Hbs1'); [| | | | | reflexivity | | ]; try eassumption.
         * omega.
         * rewrite <- reach'_heap_eq; eauto. eapply well_formed_heap_eq.
           eassumption. now eapply reach'_closed; eauto.
           eapply collect_heap_eq. eassumption.
           eapply collect_heap_eq. eassumption.
         * eapply heap_eq_dom; [| eassumption | now apply reach'_extensive ].
           eapply collect_heap_eq. eassumption.
         * intros. subst. eapply IH1 with (Hbs1 := Hbs0); [| | | | | reflexivity | |]; try eassumption.
           omega.
         * edestruct Equivalence_heap_env_equiv. eapply Equivalence_Transitive; eauto.
           eapply reach_heap_env_equiv. eapply collect_heap_eq. eassumption.      
     - (* D1 : Eval_GC *)
       subst m. remember (Ehalt x) as e'. destruct Hbs2; inv Heqe'; simpl in *.
       + (* D2 : Eval_halt *)
         eapply Heq in e1; eauto. destruct e1 as [l' [Hget Hequiv]].
         rewrite e in Hget; inv Hget. symmetry. eassumption.
       + (* D2 : Eval_GC *)
         assert (Hex : exists  (Hbs1' : big_step H rho (Ehalt x) (l, H) 1 (size_heap H)), size_big_step Hbs1' = 0).
         { exists (Eval_halt H rho x l (size_heap H) e eq_refl). eauto. }
         destruct Hex as [Hbs1' Hsize].
         eapply IH2 with (Hbs2 := Hbs2) (Hbs1 := Hbs1'); [| | | | | reflexivity | | ]; try eassumption.
         * omega.
         * rewrite <- reach'_heap_eq; eauto. eapply well_formed_heap_eq.
           eassumption. now eapply reach'_closed; eauto.
           eapply collect_heap_eq. eassumption.
           eapply collect_heap_eq. eassumption.
         * eapply heap_eq_dom; [| eassumption | now apply reach'_extensive ].
           eapply collect_heap_eq. eassumption.
         * intros. subst. eapply IH1 with (Hbs1 := Hbs1); [| | | | | reflexivity | |]; try eassumption.
           omega. 
         * edestruct Equivalence_heap_env_equiv. eapply Equivalence_Transitive; eauto.
           eapply reach_heap_env_equiv.
           eapply collect_heap_eq. eassumption.
     - (* D1 : Eval_GC *)
       eapply IH1 with (Hbs1 := Hbs1); [| | | | | reflexivity | eassumption |].
       + omega.
       + rewrite <- reach'_heap_eq; eauto. eapply well_formed_heap_eq.
         eassumption. now eapply reach'_closed; eauto.
         eapply collect_heap_eq. eassumption.
         eapply collect_heap_eq. eassumption.
       + eassumption.
       + eapply heap_eq_dom; [| eassumption | now apply reach'_extensive ].
         eapply collect_heap_eq. eassumption.
       + eassumption.
       + edestruct Equivalence_heap_env_equiv. eapply Equivalence_Transitive; try eassumption.
         symmetry. eapply reach_heap_env_equiv.
         eapply collect_heap_eq. eassumption.
   Qed.
   
End SpaceSem.
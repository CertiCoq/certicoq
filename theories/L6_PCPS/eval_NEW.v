Require Import Coq.NArith.BinNat Coq.Relations.Relations Coq.MSets.MSets
        Coq.MSets.MSetRBT Coq.Lists.List Coq.omega.Omega Coq.Sets.Ensembles
        Coq.Relations.Relations.
Require Import ExtLib.Structures.Monad ExtLib.Core.Type.
Require Import cps_NEW List_util.

Import ListNotations MonadNotation.

Definition env := M.t val. (* An [env]ironment maps [var]s to their [val]ues *)

Definition state := (env*exp)%type.

Definition prims := M.t (list val -> option val).

Section EVAL.

  Variable (pr : prims).

  Variable (cenv : cEnv).

  (** Proof that a case statement only checks constructors from the same type *)
  Inductive caseConsistent : list (cTag * exp) -> cTag -> Prop :=
  | CCnil  : forall t , caseConsistent nil t
  | CCcons : forall l t t' ty ty' n n' i i' e ,
             M.get t cenv  = Some (ty, n, i) ->
             M.get t' cenv = Some (ty', n', i') ->
             ty = ty' ->
             caseConsistent l t ->
             caseConsistent ((t', e) :: l) t.

  (** Big step semantics with cost counting *)
  Inductive bstep_e :  env -> exp -> val -> nat -> Prop :=
  | BStep_constr :
      forall (x : var) (t : cTag) (ys :list var) (e : exp)
             (rho rho' : env) (vs : list val) (v : val) (c : nat),
        getlist ys rho = Some vs ->
        M.set x (Vconstr t vs) rho = rho' ->
        bstep_e rho' e v c ->
        bstep_e rho (Econstr x t ys e) v c
  | BStep_proj :
      forall (t : cTag) (vs : list val) (v : val)
             (rho : env) (x : var) (n : N) (y : var)
             (e : exp) (ov : val) (c : nat),
        M.get y rho = Some (Vconstr t vs) ->
        nthN vs n = Some v -> 
        bstep_e (M.set x v rho) e ov c ->
        bstep_e rho (Eproj x t n y e) ov c (* force equality on [t] *)
  | BStep_case :
      forall (y : var) (v : val) (e : exp) (t : cTag) (cl : list (cTag * exp))
             (vl : list val) (rho : env) (c : nat),
        M.get y rho = Some (Vconstr t vl) ->
        caseConsistent cl t -> (* NEW *)
        findtag cl t = Some e ->
        bstep_e rho e v c ->
        bstep_e rho (Ecase y cl) v c
  | BStep_app_fun :
      forall (rho' : env) (fl : fundefs) (f' : var) (vs : list val) 
             (xs : list var) (e : exp) (rho'' rho : env) (f : var)
             (t : tag) (ys : list var) (v : val) (c : nat),
        M.get f rho = Some (Vfun rho' fl f') ->
        getlist ys rho = Some vs ->
        find_def f' fl = Some (t,xs,e) ->
        setlist xs vs (def_funs fl fl rho' rho') = Some rho'' ->
        bstep_e rho'' e v c ->
        bstep_e rho (Eapp f t ys) v (c+1)  (* force equality on [t] *)
  | BStep_fun :
      forall (rho : env) (fl : fundefs) (e : exp) (v : val) (c : nat),
        bstep_e (def_funs fl fl rho rho) e v c ->
        bstep_e rho (Efun fl e) v c
  | BStep_prim :
      forall (vs : list val) (rho' rho : env) (x : var) (f : prim) 
             (f' : list val -> option val) (ys : list var) (e : exp)
             (v v' : val) (c : nat),
        getlist ys rho = Some vs ->
        M.get f pr = Some f' ->
        f' vs = Some v ->
        M.set x v rho = rho' ->
        bstep_e rho' e v' c ->
        bstep_e rho (Eprim x f ys e) v' c.
    
  (** Small step semantics -- Relational definition *)
  (* TODO : this semantics currently does not match the big step semantic.
   * We need them to match and a proof that they indeed match. *)
  Inductive step: state -> state -> Prop := 
  | Step_constr: forall vs rho x t ys e,
                   getlist ys rho = Some vs ->
                   step (rho, Econstr x t ys e) (M.set x (Vconstr t vs) rho, e)
  | Step_proj: forall vs v rho x t n y e,
                 M.get y rho = Some (Vconstr t vs) ->
                 nthN vs n = Some v ->
                 step (rho, Eproj x t n y e) (M.set x v rho, e)
  | Step_case: forall t vl e' rho y cl,
                 M.get y rho = Some (Vconstr t vl) ->
                 caseConsistent cl t ->
                 findtag cl t = Some e' -> 
                 step (rho, Ecase y cl) (rho, e')
  | Step_fun: forall rho fl e,
                step (rho, Efun fl e) (def_funs fl fl rho rho, e)
  | Step_app: forall rho' fl f' vs xs e rho'' rho f t ys,
                M.get f rho = Some (Vfun rho' fl f') ->
                getlist ys rho = Some vs ->
                find_def f' fl = Some (t,xs,e) ->
                setlist xs vs (def_funs fl fl rho' rho') = Some rho'' ->
                step (rho, Eapp f t ys) (rho'', e)
  | Step_prim: forall vs v rho' rho x f f' ys e,
                 getlist ys rho = Some vs ->
                 M.get f pr = Some f' ->
                 f' vs = Some v ->
                 M.set x v rho = rho' ->
                 step (rho, Eprim x f ys e) (rho', e).

  
  (********** FROM HERE DOWN IS NOT UPDATED ***********)

  
  (** Small step semantics -- Computational definition *)
  Definition stepf (s: env * exp) : option (env * exp) := 
    let (rho,e) := s in
    match e with
      | Econstr x t ys e => 
        vs <- getlist ys rho ;; 
        ret (M.set x (Vconstr t vs) rho, e)
      | Eproj x t n y e =>
        match M.get y rho with
          | Some (Vconstr t' vs) =>
            match (t =? t')%positive with
              | true =>
                v <- nthN vs n ;; ret (M.set x v rho, e)
              | _ => None
            end
          | _ => None
        end
      | Ecase y cl =>
        match M.get y rho with
          | Some (Vconstr t vl) =>
            e' <- findtag cl t ;; ret (rho, e')
          | _ => None
        end
      | Efun fl e => 
        ret (def_funs fl fl rho rho, e)
      | Eapp f t ys =>
        match M.get f rho with
            | Some (Vfun rho' fl f') =>
              vs <- getlist ys rho ;;
                 match find_def f' fl with
                   | Some (t',xs,e) =>
                     match (t =? t')%positive with
                       | true =>
                         rho'' <- setlist xs vs (def_funs fl fl rho' rho') ;;
                         ret (rho'', e)
                       | _ => None
                     end 
                   | _ => None
                 end
            | _ => None
        end
      | Eprim x f ys e =>
        vs <- getlist ys rho ;;
        f' <- M.get f pr ;;
        v <- f' vs ;;
        ret (M.set x v rho, e)
    end.

  (** Correspondence of the two small step semantics definitions *)
  Lemma step_stepf:
    forall s s',
      step s s' ->
      stepf s = Some s'.
  Proof.
    intros [rho e] [rho' e'] H;
    inv H; simpl;
    repeat match goal with
             | H: ?A= _ |- match ?A with _ => _ end = _ => rewrite H 
           end; 
    auto.
  Qed.

  Lemma stepf_step:
    forall s s',
      stepf s = Some s' ->
      step s s'.
  Proof.
    intros [rho e] [rho' e'] H.
    destruct e; simpl in H; 
    repeat 
      match goal with
        | H: match ?A with _ => _ end = Some _ |- _ => destruct A eqn:?; inv H
        | H: Some _ = Some _ |- _ => inv H
      end;
    try solve [econstructor; eauto].
  Qed.

  
  (** Reflexive transitive closure of the small-step relation *)
  Definition mstep: relation state := clos_refl_trans_1n state step.

  Ltac subst_exp :=
    match goal with
      | [H1 : ?e = ?e1, H2 : ?e = ?e2 |- _ ] =>
        rewrite H1 in H2; inv H2
    end.

  (** The evalutation semantics is deterministic *)
  Lemma bstep_e_deterministic e rho v1 v2 c1 c2 :
    bstep_e rho e v1 c1 ->
    bstep_e rho e v2 c2 ->
    v1 = v2 /\ c1 = c2.
  Proof.
    intros Heval1 Heval2.
    revert c2 Heval2; induction Heval1; intros c2 Heval2;
    inv Heval2; repeat subst_exp; eauto.
    split; f_equal; eapply IHHeval1; eauto. 
  Qed.

  Lemma step_deterministic:
    forall s s' s'',
      step s s' -> step s s'' -> s' = s''.
  Proof.
    intros.
    inversion H; inversion H0; subst;
    repeat match goal with
             | [ |- ?P = ?P] => reflexivity
             | [H: ( Some _ = Some _ ) |- _ ] => inversion H; subst      
             | [H1: (?P = Some _), H2:(?P = Some _) |- _ ] => rewrite H1 in H2;
                 inversion H2; subst
             | [H: ((?rho0, _) = (?rho, _)) |- _ ] => inversion H; subst
           end.
    + rewrite H6 in H2.  inversion H2; subst. reflexivity.
    + rewrite H6 in H2; inversion H2; subst. reflexivity.
    + rewrite H9 in H3; inversion H3; subst.
      rewrite H2 in H8; inversion H8; subst.
      rewrite H10 in H4; inversion H4. reflexivity.
    + rewrite H2 in H8; inversion H8; subst.
      rewrite H9 in H3; inversion H3; subst; reflexivity.
  Qed.

  Lemma step_confluent :
    forall s sv1 sv2,
      mstep s sv1 -> mstep s sv2 ->
      (exists s', mstep sv1 s' /\ mstep sv2 s').
  Proof.
    intros s sv1 sv2 Hs1. revert sv2. induction Hs1.
    - intros z Hs.
      eexists. split. eassumption. now constructor.
    - intros s2 Hs2.
      inv Hs2. 
      + eexists z. split; [ now constructor |].
        econstructor 2; eassumption.
      + assert (Heq : y = y0) by (eapply step_deterministic; eassumption).
        subst. apply IHHs1.  eassumption. 
  Qed.
  
End EVAL.
  
  (** The following are not used anywhere. They have to do either with "well-typedness"
    * or observable values. We need to go through them to decide if can can through them
    * away altogether. *)
  (* Inductive observable_val: val -> Prop := *)
  (* | obv_int : forall i, observable_val (Vint i) *)
  (* | obv_obvs : forall t, observable_val (Vobv t). *)

  (* may want to force all vals in the list to be observable? *)
  (* Inductive obs_val: Type := *)
  (* | Obs : forall vs:list val, type -> Forall observable_val vs -> obs_val. *)
  
  (* if only consider ints and observers (i.e observable_val), syntactic 
     equality on val is the desired notion of equality. *)

  (* Definition val_proper: val -> Prop := observable_val.  *)
  (* Definition val_equiv: val -> val -> Prop := @eq val.  *)

  (* Theorem val_equiv_eq_rel: Equivalence (val_equiv). *)
  (* Proof. *)
  (*   constructor; red. *)
  (*   + intros. reflexivity. *)
  (*   + intros. inversion H. reflexivity. *)
  (*   + intros. inversion H. inversion H0. reflexivity. *)
  (* Qed.   *)
  
  (* Definition obs_val_proper: obs_val -> Prop := fun _ => True. *)
  (* Definition obs_val_equiv: relation obs_val := *)
  (*   fun vso1 vso2 => match vso1, vso2 with *)
  (*                      | Obs vs1 t1 vsop1, Obs vs2 t2 vsop2 => Forall2 (val_equiv) vs1 vs2 end. *)

  
  (* Theorem obs_val_equiv_eq_rel: Equivalence (obs_val_equiv). *)
  (* Proof. *)
  (*   assert (Equivalence (Forall2 val_equiv)). apply forall2_eq_rel. *)
  (*   apply val_equiv_eq_rel. constructor; red; intros. *)
  (*   + unfold obs_val_equiv. destruct x. apply H. *)
  (*   + unfold obs_val_equiv. unfold obs_val_equiv in H0. *)
  (*     destruct x; destruct y. revert H0. apply H. *)
  (*   + unfold obs_val_equiv. unfold obs_val_equiv in H0. *)
  (*     unfold obs_val_equiv in H1. *)
  (*     destruct x; destruct y; destruct z. revert H1; revert H0. apply H. *)
  (* Qed. *)

  (* Definition type_obs_val : T.type (obs_val) := *)
  (*   {| T.equal := obs_val_equiv ; *)
  (*      T.proper := obs_val_proper |}. *)

  (* Instance typeOk_obs_val: T.typeOk (type_obs_val). *)
  (* Proof. *)
  (*   constructor. *)
  (*   + intros. split; do 3 red; constructor. *)
  (*   + do 3 red. intros. red.  destruct x. apply forall2_eq_rel. *)
  (*     apply val_equiv_eq_rel. *)
  (*   + do 3 red. intros. red in H. red in H. revert H. *)
  (*     apply obs_val_equiv_eq_rel. *)
  (*   + do 3 red. intros. do 2 (red in H). do 2 (red in H0). *)
  (*     revert H0; revert H; apply obs_val_equiv_eq_rel. *)
  (* Qed. *)

  (* (* small-step based equality on state *)     *)
  (* Definition valid_term_state (s:state) := *)
  (*   match s with *)
  (*     | (rho, Eapp g varl) => *)
  (*       match M.get g rho with *)
  (*         | Some (Vobvs t) => *)
  (*           Forall (fun var => match M.get var rho with *)
  (*                             | Some val => observable_val val *)
  (*                             | _ => False *)
  (*                           end) varl *)
  (*         | _ => False *)
  (*       end *)
  (*     | _ => False *)
  (*   end *)

 
  (* Definition var_equiv: env -> env -> relation var := *)
  (*   fun rho1 rho2 => *)
  (*     fun var1 var2 => *)
  (*       match (M.get var1 rho1, M.get var2 rho2) with *)
  (*         |(Some v1, Some v2) => val_equiv v1 v2 *)
  (*         | _ => False *)
  (*       end. *)


  (* small-step based equality on state *)    
  (* Definition valid_term_state (s:state) := *)
  (*   match s with *)
  (*     | (rho, Eapp g varl) => *)
  (*       match M.get g rho with *)
  (*         | Some (Vobvs t) => *)
  (*           Forall (fun var => match M.get var rho with *)
  (*                                | Some val => observable_val val *)
  (*                                | _ => False *)
  (*                              end) varl *)
  (*         | _ => False *)
  (*       end *)
  (*     | _ => False *)
  (*   end. *)
  
  (* Definition state_equiv: relation state := *)
  (*   fun s1 s2 => *)
  (*     exists sv1 sv2, *)
  (*       mstep s1 sv1 /\ mstep s2 sv2 /\ *)
  (*       valid_term_state sv2 /\ valid_term_state sv1 /\ *)
  (*       match (sv1, sv2) with *)
  (*         | ((rho1, Eapp g1 varl1) , (rho2, Eapp g2 varl2)) => *)
  (*           match (M.get g1 rho1, M.get g2 rho2) with  *)
  (*              | (Some v1, Some v2) => val_equiv v1 v2 *)
  (*              | _ => False *)
  (*            end *)
  (*           /\ Forall2 (var_equiv rho1 rho2) varl1 varl2 *)
  (*         | _ => False *)
  (*       end. *)

 
  (* Definition env_of_tenv :=  *)
  (*   fun rho:env => *)
  (*     fun Gamma:tenv => *)
  (*       forall var, *)
  (*         (exists ty, M.get var Gamma = Some ty <-> *)
  (*                     exists val, M.get var rho = Some val /\ type_of_val val ty). *)


  (* Lemma cant_step_terminal: *)
  (*   forall s s', *)
  (*     valid_term_state s -> ~ step s s'. *)
  (* Proof. *)
  (*   intros s s' H Hstep. unfold valid_term_state in H. *)
  (*   destruct s. destruct e0; try inversion H.  *)
  (*   destruct (M.get v e) eqn:Heq; try inversion H. destruct v0; try inv H;  *)
  (*   inv Hstep; congruence.  *)
  (* Qed. *)

  (* Theorem state_equiv_step_l: *)
  (*   forall s1 s2 s1', step s1 s1' -> (state_equiv s1 s2 <-> state_equiv s1' s2). *)
  (* Proof. *)
  (*   intros s1 s2 s1' H0. split; intro. *)
  (*   + unfold state_equiv in H. destruct H as [sv1 ?]. destruct H as [sv2 ?]. *)
  (*     do 4 ( destruct H as [?V H]). inversion V; subst.  assert (s3 = s1'). *)
  (*     eapply step_deterministic. apply H1. apply H0. subst. unfold state_equiv. *)
  (*     exists sv1. exists sv2. split. assumption. split. assumption. split. *)
  (*     assumption. split. assumption. assumption. *)
  (*     apply (cant_step_terminal _ _ V2) in H0. inversion H0. *)
  (*   + unfold state_equiv in H. destruct H as [sv1 ?]. destruct H as [sv2 ?]. *)
  (*     do 4 (destruct H as [?V H]). assert (mstep s1 sv1). eapply s_step. *)
  (*     apply H0. apply V. unfold state_equiv. exists sv1. exists sv2. split. *)
  (*     assumption. split. assumption. split. assumption. split. assumption. *)
  (*     assumption. *)
  (* Qed. *)

  (* Theorem state_equiv_step_r: *)
  (*   forall s1 s2 s2', step s2 s2' -> *)
  (*                     (state_equiv s1 s2  <-> state_equiv s1 s2'). *)
  (* Proof. *)
  (*   intros s1 s2 s2' H0. split; intro. *)
  (*   + unfold state_equiv in H. destruct H as [sv1 ?]. destruct H as [sv2 ?]. *)
  (*     do 4 (destruct H as [?V H]). inversion V0; subst. assert (s3 = s2'). *)
  (*     eapply step_deterministic. apply H1. assumption. subst. *)
  (*     unfold state_equiv. exists sv1. exists sv2. split. assumption. *)
  (*     split. assumption. split. assumption. split. assumption. assumption. *)
  (*     apply (cant_step_terminal _ _ V1) in H0. inversion H0. *)
  (*   + unfold state_equiv in H. destruct H as [sv1 ?]. destruct H as [sv2 ?]. *)
  (*     do 4 (destruct H as [?V H]). assert (mstep  s2 sv2). eapply s_step; eauto. *)
  (*     unfold state_equiv. exists sv1. exists sv2. split. assumption. split. *)
  (*     assumption. split. assumption. split. assumption. assumption. *)
  (* Qed. *)



  (* Theorem mstep_terminal_to_itself: *)
  (*   forall s s', *)
  (*     valid_term_state s ->  *)
  (*     mstep s s' -> *)
  (*     s = s'. *)
  (* Proof. *)
  (*   intros. inversion H0; subst. *)
  (*   assert False. eapply cant_step_terminal. apply H. apply H1. inversion H3. *)
  (*   reflexivity. *)
  (* Qed. *)
  
  
  (* Theorem forall2_varequiv_transitive: *)
  (*   forall e1 e2 e3 l1 l2 l3, *)
  (*     Forall2 (var_equiv e1 e2) l1 l2 -> *)
  (*     Forall2 (var_equiv e2 e3) l2 l3 -> *)
  (*     Forall2 (var_equiv e1 e3) l1 l3. *)
  (* Proof. *)
  (*   intros. generalize dependent l2. generalize dependent l3. *)
  (*   induction l1; intros. *)
  (*   inversion H; subst. inversion H0; subst. constructor. *)
  (*   inversion H; subst. inversion H0; subst. constructor. *)
  (*   red. red in H3. red in H4. clear H0. clear H7. clear H. *)
  (*   clear IHl1. destruct (M.get a e1); try inversion H3. *)
  (*   destruct (M.get y e2); try inversion H3. destruct (M.get y0 e3); *)
  (*     try inversion H4. reflexivity. *)
  (*   eapply IHl1. apply H5. apply H7. *)
  (* Qed. *)


  (* Definition state_proper := *)
  (*   fun st => exists sv, mstep st sv /\ valid_term_state sv. *)

  (* (* small step state equivalence *) *)
  (* Definition type_state : T.type (state) := *)
  (*   {| T.equal := state_equiv *)
  (*      ; T.proper := state_proper *)
  (*   |}. *)

  (* Instance typeOk_state : T.typeOk (type_state).  *)
  (* constructor.   *)
  (* intros. *)

  (* (* only proper *) *)
  (* inversion H. destruct H0. destruct H0. destruct H1. *)
  (* destruct H2. destruct H3. split; do 2 red. exists x0; split; assumption. *)
  (* exists x1; split; assumption. *)

  (* (* Reflective for proper state *)          *)
  (* red. intros. inversion H. destruct H0. red. red. red. exists x0. *)
  (* exists x0. split. assumption. split. assumption. split. assumption. *)
  (* split. assumption. unfold valid_term_state in H1. destruct x0. *)
  (* destruct e0; try inversion H1. destruct (M.get v e); try inversion H1. *)
  (* split. red. reflexivity. clear H0. induction l. constructor. constructor. *)
  (* red. destruct v0; try inversion H1; subst.  destruct (M.get a e). reflexivity. *)
  (* inversion H3. apply (IHl). destruct v0; try inversion H1. inversion H1; subst. *)
  (* assumption. *)

  (* (* symmetric *) *)
  (* red. intros. red. red. red. destruct H. destruct H. destruct H. destruct H0. *)
  (* destruct H1. destruct H2. exists x1. exists x0. split. assumption. split. *)
  (* assumption. split. assumption. split. assumption. destruct x0. destruct x1. *)
  (* destruct e0; try inversion H3. destruct e2; try inversion H3. split. clear H. *)
  (* clear H0. destruct (M.get v e); try inversion H3. *)
  (* destruct (M.get v0 e1); try inversion H4. reflexivity. inversion H. clear H. *)
  (* clear H0. clear H1. clear H2. clear H3. generalize dependent l0. induction l. *)
  (* intros. inversion H5. subst. constructor. intros. inversion H5. constructor. *)
  (* (* var_equiv is quasi-symmetric*) unfold var_equiv. unfold var_equiv in H1. *)
  (* destruct (M.get a e); try inversion H1. *)
  (* destruct (M.get y0 e1); try inversion H1. reflexivity.  apply IHl. assumption. *)

  (* (* Transitive *) *)
  (* red. intros. do 3 red. do 3 red in H.  do 3 red in H0. destruct H. destruct H. *)
  (* destruct H0. destruct H0. destruct H. destruct H1. destruct H2. destruct H3. *)
  (* destruct H0. destruct H5. destruct H6. destruct H7. *)
  (* assert (exists s', mstep x1 s' /\ mstep x2 s'). *)
  (* apply (church_rosser y x1 x2 H1 H0). *)
  (* destruct H9. destruct H9. *)
  (* apply (mstep_terminal_to_itself _ _ H7) in H10; subst. *)
  (* apply (mstep_terminal_to_itself _ _ H2) in H9; subst. exists x0. exists x3. *)
  (* repeat (split; try assumption). *)
  (* destruct x0. destruct e0; try inversion H4. destruct x3. destruct x4. *)
  (* destruct e3; try inversion H4. destruct e1; try inversion H8. *)
  (* destruct (M.get v e); try inversion H9. split. destruct (M.get v0 e2); try inversion H8. *)
  (* destruct (M.get v1 e0); try inversion H11. eapply transitivity. apply H9. *)
  (* apply H11. inversion H11. eapply forall2_varequiv_transitive. destruct H4. *)
  (* apply f. apply H12.  *)
  (* Qed. *)
  (* (* proofs of semantics preservation for P will look like  *)
  (*  forall rho, proper (rho, e) -> equal (rho, e) (rho, P e). *) *)
  

  (* (* small step exp equivalence *) *)
  (* Definition exp_equiv: relation exp := *)
  (*   fun e1 e2 => *)
  (*     (forall rho1, *)
  (*        state_proper(rho1, e1) -> state_equiv (rho1, e1) (rho1, e2)) /\ *)
  (*     (forall rho2, *)
  (*        state_proper (rho2, e2) -> state_equiv (rho2, e1) (rho2, e2)). *)

  (* Definition exp_proper := fun e:exp => True. *)

  (* Definition type_exp : T.type (exp) := *)
  (*   {| T.equal := exp_equiv  *)
  (*      ; T.proper := exp_proper *)
  (*   |}. *)

  (* Ltac tci := eauto with typeclass_instances. *)

  (* Instance typeOk_exp : T.typeOk (type_exp). *)
  (* Proof. *)
  (*   constructor. *)
  (*   intros. split; do 3 red; constructor. *)
  (*   (* PRefl *) *)
  (*   + red. intros. do 3 red. split; intros; apply typeOk_state; tci. *)

  (*   (* Symmetric *)     *)
  (*   + red. intros. do 3 red in H. destruct H. do 3 red. split; intros. *)
  (*   - apply H0 in H1. generalize H1. apply typeOk_state; tci. *)
  (*   - apply H in H1. generalize H1. apply typeOk_state; tci. *)
  (*     (* Transitive *) *)
  (*     + do 3 red. intros. do 3 red in H. destruct H. do 3 red in H0. *)
  (*       destruct H0. red. split; intros. *)
  (*   - apply H in H3. assert (H4 := H3). apply typeOk_state in H3. destruct H3. *)
  (*     apply H0 in H5. generalize H5. generalize H4. apply typeOk_state; tci. *)
  (*   - apply H2 in H3. assert (H4 := H3). apply typeOk_state in H3; destruct H3. *)
  (*     apply H1 in H3. generalize H4. generalize H3. apply typeOk_state; tci. *)
  (* Qed. *)

  (* (* fun equivalence *) *)
  (* Definition fun_equiv: forall e1 e2, exp_equiv e1 e2 -> relation fundefs := *)
  (*   fun e1 e2 => *)
  (*     fun equiv_e1e2 => *)
  (*       fun fds1 fds2 => *)
  (*         (forall rho1, *)
  (*            state_proper (def_funs fds1 fds1 rho1 rho1, e1) -> *)
  (*            state_equiv (def_funs fds1 fds1 rho1 rho1, e1) (def_funs fds2 fds2 rho1 rho1, e2)) /\ *)
  (*         (forall rho2, *)
  (*            state_proper (def_funs fds2 fds2 rho2 rho2, e2) -> *)
  (*            state_equiv (def_funs fds1 fds1 rho2 rho2, e1) (def_funs fds2 fds2 rho2 rho2, e2)). *)

  (* Definition fun_proper := fun f:fundefs => True. *)

  (* Definition etype_fun :  forall e1 e2, exp_equiv e1 e2 -> T.type fundefs  := *)
  (*   fun e1 e2 => fun equiv_e1e2 =>  *)
  (*                  {| T.equal := fun_equiv e1 e2 equiv_e1e2 *)
  (*                     ; T.proper := fun_proper *)
  (*                  |}. *)

  (* Instance etypeOk_fun : forall e1 e2, forall equiv_e1e2: exp_equiv e1 e2, T.typeOk (etype_fun e1 e2 equiv_e1e2). *)
  (* intros. constructor. *)
  (* (* only *) *)
  (* + intros. split; do 3 red; constructor. *)
  (* (* Prefl *) *)
  (* + red. intros. do 3 red. split; intros. *)
  (* - red in equiv_e1e2. destruct equiv_e1e2. *)
  (*   apply s in H0. assumption.   *)
  (* - red in equiv_e1e2. destruct equiv_e1e2. apply s0 in H0. assumption.  *)
  (*   (* symmetric *) *)
  (*   + red. intros. do 3 red in H. do 3 red. destruct H. red in equiv_e1e2. *)
  (*     destruct equiv_e1e2. split; intros. *)
  (* - assert (H4 := H3). apply H1 in H4.  assert (H5 := H4). *)
  (*   apply typeOk_state in H4; destruct H4.  apply H0 in H6. *)
  (*   assert (H7 := H6). apply typeOk_state in H6; destruct H6. apply H1 in H6. *)
  (*   eapply (@T.equiv_trans _ type_state typeOk_state). *)
  (*   eapply (@T.equiv_trans _ type_state typeOk_state). *)
  (*   apply H5. apply (T.equiv_sym type_state _ _) in H7. apply H7. assumption. *)
  (* - apply H2 in H3. assert (H4 := H3). apply typeOk_state in H4; destruct H4. *)
  (*   apply H in H4. assert (H6 := H4). apply typeOk_state in H4; destruct H4. *)
  (*   apply H2 in H7. eapply (@T.equiv_trans _ type_state typeOk_state). *)
  (*   eapply (@T.equiv_trans _ type_state typeOk_state). apply H7. *)
  (*   apply (T.equiv_sym type_state _ _) in H6. apply H6. assumption.     *)
  (*   (* transitive *) *)
  (*   + red. intros. do 3 red in H. do 3 red in H0. do 3 red. *)
  (*     destruct H. destruct H0. red in equiv_e1e2. destruct equiv_e1e2. *)
  (*     split; intros. *)
  (* - apply H in H5. assert (Hfin1 := H5). apply typeOk_state in H5; destruct H5. *)
  (*   apply H4 in H6. assert (Hfin2 := H6). apply typeOk_state in H6; destruct H6. *)
  (*   apply H0 in H6. Print T. About T.equiv_sym. *)
  (*   eapply (T.equiv_sym type_state _ _) in Hfin2. About T.equiv_trans. *)
  (*   eapply (@T.equiv_trans _ type_state typeOk_state). *)
  (*   eapply (@T.equiv_trans _ type_state typeOk_state). apply Hfin1. *)
  (*   apply Hfin2. apply H6. *)
  (* - apply H2 in H5. assert (Hfin1 := H5). apply typeOk_state in H5; destruct H5. *)
  (*   apply H3 in H5. assert (Hfin2 := H5). apply typeOk_state in H5; destruct H5. *)
  (*   apply H1 in H7.  eapply (@T.equiv_trans _ type_state typeOk_state). *)
  (*   eapply (@T.equiv_trans _ type_state typeOk_state). apply H7. *)
  (*   apply (T.equiv_sym type_state _ _) in Hfin2. apply Hfin2. assumption. *)
  (* Qed. *)
  
  (* (* big step exp equivalence *) *)
  (* Definition  bs_exp_proper := *)
  (*   fun _:exp => True (* fun e:exp => exists rho v, bstep_e rho e v. *). *)



  (* Definition bs_exp_equiv : relation exp := *)
  (*   fun e1 e2 => *)
  (*     (forall rho v, *)
  (*        bstep_e rho e1 v -> exists v', bstep_e rho e2 v' /\ obs_val_equiv v v') /\ *)
  (*     (forall rho v, *)
  (*        bstep_e rho e2 v -> exists v', bstep_e rho e1 v' /\ obs_val_equiv v v'). *)

  (* Definition type_bs_exp : T.type (exp) := *)
  (*   {| T.equal := bs_exp_equiv *)
  (*      ;T.proper := bs_exp_proper |}. *)

  (* Instance typeOk_bs_exp : T.typeOk (type_bs_exp). *)
  (* Proof. *)
  (*   constructor. *)
  (*   intros. split; do 3 red; constructor. *)
  (*   + do 3 red. intros. unfold bs_exp_equiv. *)
  (*     split; intros. exists v. split. assumption. *)
  (*     apply obs_val_equiv_eq_rel. exists v. split. assumption. *)
  (*     apply typeOk_obs_val. auto. *)
  (*   + red. intros. do 3 red in H.  destruct H. do 3 red. split; intros. *)
  (*     apply H0 in H1. destruct H1. destruct H1. exists x0. split. assumption. *)
  (*     assumption. apply H in H1. destruct H1. destruct H1. *)
  (*     exists x0. split; assumption. *)
  (*   + do 3 red. intros. do 3 red in H. destruct H. do 3 red in H0. *)
  (*     destruct H0. red. split. intros. apply H in H3. destruct H3. destruct H3. *)
  (*     apply H0 in H3. destruct H3. exists x1. destruct H3. split. assumption. *)
  (*     revert H5. revert H4. apply typeOk_obs_val. *)
  (*     intros. apply H2 in H3. destruct H3. destruct H3. apply H1 in H3. *)
  (*     destruct H3. exists x1. destruct H3. split. assumption. revert H5. *)
  (*     revert H4. apply typeOk_obs_val. *)
  (* Qed. *)
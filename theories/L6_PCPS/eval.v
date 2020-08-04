From Coq Require Import NArith.BinNat Relations.Relations MSets.MSets
     MSets.MSetRBT Lists.List omega.Omega Sets.Ensembles
     Relations.Relations Strings.String.

From CertiCoq.Common Require Import AstCommon exceptionMonad.

From CertiCoq Require Import L6.cps L6.List_util L6.size_cps L6.ctx L6.cps_util L6.set_util L6.map_util
     L6.identifiers L6.tactics L6.Ensembles_util.

Require Import compcert.lib.Coqlib.
Require Import L6.algebra. 

Import ListNotations.

(** An [env]ironment maps [var]s to their [val]ues *)
Definition env := M.t val.

(** A pair of an environment and an expression. The small step semantics is a transition system between this state *)
Definition state := (env * exp)%type.

(** Primitive functions map. *)
Definition prims := M.t (list val -> option val).

Section EVAL.

  Variable (pr : prims).

  Variable (cenv : ctor_env).

  (** Big step semantics with cost counting *)
  Inductive bstep_e : env -> exp -> val -> nat -> Prop :=
  | BStep_constr :
      forall (x : var) (t : ctor_tag) (ys :list var) (e : exp)
             (rho rho' : env) (vs : list val) (v : val) (c : nat),
        get_list ys rho = Some vs ->
        M.set x (Vconstr t vs) rho = rho' ->
        bstep_e rho' e v c ->
        bstep_e rho (Econstr x t ys e) v c
  | BStep_proj :
      forall (t : ctor_tag) (vs : list val) (v : val)
             (rho : env) (x : var) (n : N) (y : var)
             (e : exp) (ov : val) (c : nat),
        M.get y rho = Some (Vconstr t vs) ->
        nthN vs n = Some v ->
        bstep_e (M.set x v rho) e ov c ->
        bstep_e rho (Eproj x t n y e) ov c (* force equality on [t] *)
  | BStep_case :
      forall (y : var) (v : val) (e : exp) (t : ctor_tag) (cl : list (ctor_tag * exp))
             (vl : list val) (rho : env) (c : nat),
        M.get y rho = Some (Vconstr t vl) ->
        caseConsistent cenv cl t -> (* NEW *)
        findtag cl t = Some e ->
        bstep_e rho e v c ->
        bstep_e rho (Ecase y cl) v c
  | BStep_app :
      forall (rho' : env) (fl : fundefs) (f' : var) (vs : list val)
             (xs : list var) (e : exp) (rho'' rho : env) (f : var)
             (t : ctor_tag) (ys : list var) (v : val) (c : nat),
        M.get f rho = Some (Vfun rho' fl f') ->
        get_list ys rho = Some vs ->
        find_def f' fl = Some (t,xs,e) ->
        set_lists xs vs (def_funs fl fl rho' rho') = Some rho'' ->
        bstep_e rho'' e v c ->
        bstep_e rho (Eapp f t ys) v (c+1)  (* force equality on [t] *)
  | BStep_letapp :
      forall (rho' : env) (fl : fundefs) (f' : var) (vs : list val)
             (xs : list var) (e_body e : exp) (rho'' rho : env) (x f : var)
             (t : ctor_tag) (ys : list var) (v v' : val) (c c' : nat),
        (* evaluate application *)
        M.get f rho = Some (Vfun rho' fl f') ->
        get_list ys rho = Some vs ->
        find_def f' fl = Some (t,xs,e_body) ->
        set_lists xs vs (def_funs fl fl rho' rho') = Some rho'' ->
        bstep_e rho'' e_body v c -> (* body evaluates to v *)
        (* evaluate let continuation *)
        bstep_e (M.set x v rho) e v' c' ->
        bstep_e rho (Eletapp x f t ys e) v' (c + c' + 1)  (* force equality on [t] *)
  | BStep_fun :
      forall (rho : env) (fl : fundefs) (e : exp) (v : val) (c : nat),
        bstep_e (def_funs fl fl rho rho) e v c ->
        bstep_e rho (Efun fl e) v c
  | BStep_prim :
      forall (vs : list val) (rho' rho : env) (x : var) (f : prim)
             (f' : list val -> option val) (ys : list var) (e : exp)
             (v v' : val) (c : nat),
        get_list ys rho = Some vs ->
        M.get f pr = Some f' ->
        f' vs = Some v ->
        M.set x v rho = rho' ->
        bstep_e rho' e v' c ->
        bstep_e rho (Eprim x f ys e) v' c
  | BStep_halt :
      forall x v rho,
        M.get x rho = Some v ->
        bstep_e rho (Ehalt x) v 0.


  (* fuel-based evaluator, could also use n from bstep_e with a termination lex (n, e) *)


  Definition l_opt {A} (e:option A) (s:string):exception A :=
    match e with
    | None => Exc s
    | Some e => Ret e
    end.

  (*
  (* Zoe : How to write small step for letapp? *)
  Definition sstep_f (rho:env) (e:exp) : exception (env* exp) :=
    match e with
      | Eprim x f ys e' =>
          do vs  <- l_opt (getlist ys rho) ("Eprim: failed to getlist");
          do f' <- l_opt (M.get f pr) ("Eprim: prim not found");
          do v <- l_opt (f' vs) ("Eprim: prim did not compute");
          let rho' := M.set x v rho in
          Ret (rho', e')
      | Econstr x t ys e' =>
        do vs <- l_opt (get_list ys rho) ("Econstr: failed to get args");
          let rho' := M.set x (Vconstr t vs) rho in
          Ret (rho', e')
      | Eproj x t m y e' =>
        (match (M.get y rho) with
           | Some (Vconstr t' vs) =>
             if Pos.eqb t t' then
               do v <- l_opt (nthN vs m) ("Eproj: projection failed");
               let rho' := M.set x v rho in
               Ret (rho', e')
             else (exceptionMonad.Exc "Proj: tag check failed")
           | _ => (exceptionMonad.Exc "Proj: var not found")
         end)
      | Efun fl e' =>
        let rho' := def_funs fl fl rho rho in
        Ret (rho', e')
      | Ehalt x =>
        (exceptionMonad.Exc "Halt: can't step")
      | Ecase y cl =>
        match M.get y rho with
          | Some (Vconstr t vs) =>
            do e <- l_opt (findtag cl t) ("Case: branch not found");
              if caseConsistent_f cenv cl t then
                Ret (rho, e)
               else     (exceptionMonad.Exc "Case: consistency failure")
          | Some _ =>  (exceptionMonad.Exc "Case: arg is not a constructor")
          | None => (exceptionMonad.Exc "Case: arg not found")
        end
      | Eletapp x f t ys e =>
        (match (M.get f rho) with
           | Some (Vfun rho' fl f') =>
             do vs <- l_opt (get_list ys rho) ("App: failed to get args");
               (match  find_def f' fl with
                | Some (t', xs ,e_body) =>
                  if (Pos.eqb t t') then
                  do rho'' <- l_opt (set_lists xs vs (def_funs fl fl rho' rho')) ("Fun: set_lists failed");
                    Ret (rho'', e)
                  else (exceptionMonad.Exc "Fun: tag check failed")
              | _ => (exceptionMonad.Exc "Fun: function not found in bundle")
            end)
           |  _ => (exceptionMonad.Exc "Fun: Bundle not found")
         end)
    end.

      | Eapp f t ys =>
        (match (M.get f rho) with
           | Some (Vfun rho' fl f') =>
             do vs <- l_opt (get_list ys rho) ("App: failed to get args");
           (match  find_def f' fl with
              | Some (t', xs ,e) =>
                if (Pos.eqb t t') then
                  do rho'' <- l_opt (set_lists xs vs (def_funs fl fl rho' rho')) ("Fun: set_lists failed");
                  Ret (rho'', e)
                else (exceptionMonad.Exc "Fun: tag check failed")
              | _ => (exceptionMonad.Exc "Fun: function not found in bundle")
            end)
           |  _ => (exceptionMonad.Exc "Fun: Bundle not found")
         end)
    end.
   *)
  (* Either fail with an Exn, runs out of fuel and return (Ret) inl of the current state or finish to evaluate and return inr of a val *)
  Fixpoint bstep_f (rho:env) (e:exp) (n:nat): exception ((env * exp) + val) :=
    match n with
    | O => exceptionMonad.Ret (inl (rho, e))
    | S n' =>
      ( match e with
        | Eprim x f ys e' =>
          do vs <- l_opt (get_list ys rho) ("Eprim: failed to get_list");
          do f' <- l_opt (M.get f pr) ("Eprim: prim not found");
          do v <- l_opt (f' vs) ("Eprim: prim did not compute");
          let rho' := M.set x v rho in
          bstep_f rho' e' n'
        | Econstr x t ys e' =>
          do vs <- l_opt (get_list ys rho) ("Econstr: failed to get args");
          let rho' := M.set x (Vconstr t vs) rho in
          bstep_f rho' e' n'
        | Eproj x t m y e' =>
          (match (M.get y rho) with
           | Some (Vconstr t' vs) =>
             if Pos.eqb t t' then
               do v <- l_opt (nthN vs m) ("Eproj: projection failed");
               let rho' := M.set x v rho in
               bstep_f rho' e' n'
             else (exceptionMonad.Exc "Proj: tag check failed")
           | _ => (exceptionMonad.Exc "Proj: var not found")
           end)
        | Efun fl e' =>
          let rho' := def_funs fl fl rho rho in
          bstep_f rho' e' n'
        | Ehalt x =>
          match (M.get x rho) with
          | Some v => exceptionMonad.Ret (inr v)
          | None => (exceptionMonad.Exc "Halt: value not found")
          end
        | Ecase y cl =>
          match M.get y rho with
          | Some (Vconstr t vs) =>
            do e <- l_opt (findtag cl t) ("Case: branch not found");
            if caseConsistent_f cenv cl t then
              bstep_f rho e n'
            else (exceptionMonad.Exc "Case: consistency failure")
          | _ => (exceptionMonad.Exc "Case: branch not found")
          end
        | Eletapp x f t ys e =>
          (match (M.get f rho) with
           | Some (Vfun rho' fl f') =>
             do vs <- l_opt (get_list ys rho) ("App: failed to get args");
             (match  find_def f' fl with
              | Some (t', xs ,e_body) =>
                if (Pos.eqb t t') then
                  do rho'' <- l_opt (set_lists xs vs (def_funs fl fl rho' rho')) ("Fun: set_lists failed");
                  do v <- bstep_f rho'' e_body n';
                  match v with
                  | inl st => Ret (inl st)
                  | inr v => bstep_f (M.set x v rho) e n'
                  end
                else (exceptionMonad.Exc "Fun: tag check failed")
              | _ => (exceptionMonad.Exc "Fun: function not found in bundle")
              end)
           |  _ => (exceptionMonad.Exc "Fun: Bundle not found")
           end)
        | Eapp f t ys =>
          (match (M.get f rho) with
           | Some (Vfun rho' fl f') =>
             do vs <- l_opt (get_list ys rho) ("App: failed to get args");
             (match  find_def f' fl with
              | Some (t', xs ,e) =>
                if (Pos.eqb t t') then
                  do rho'' <- l_opt (set_lists xs vs (def_funs fl fl rho' rho')) ("Fun: set_lists failed");
                  bstep_f rho'' e n'
                else (exceptionMonad.Exc "Fun: tag check failed")
              | _ => (exceptionMonad.Exc "Fun: function not found in bundle")
              end)
           |  _ => (exceptionMonad.Exc "Fun: Bundle not found")
           end)
        end)
    end.

  Theorem bstep_f_sound:
    forall n rho e v,
      bstep_f rho e n = Ret (inr v) ->
      exists m, bstep_e rho e v m.
  Proof.
    induction n; intros. inv H.
    simpl in H.
    destruct e.
    -  destruct (get_list l rho) eqn:glr; [| inv H].
       apply IHn in H. inv H.
       exists x. econstructor; eauto.
    - destruct (M.get v0 rho) eqn:gv0r.
      destruct v1. destruct (findtag l c) eqn:flc.
      destruct (caseConsistent_f cenv l c) eqn:clc.
      apply caseConsistent_c in clc.
      apply IHn in H. inv H. exists x.
      econstructor; eauto.
      inv H. inv H. inv H. inv H. inv H.
    - destruct (M.get v1 rho) eqn:gv1r; [|inv H].
      destruct v2; [ | inv H | inv H].
      destruct (c=?c0)%positive eqn:eqcc0; [| inv H].
      destruct (nthN l n0) eqn:nln0; [| inv H].
      apply IHn in H. inv H.
      apply Peqb_true_eq in eqcc0. subst.
      exists x. econstructor; eauto.
    - destruct (M.get v1 rho) eqn:gv0r; [| inv H].
      destruct v2; [inv H| | inv H].
      destruct (get_list l rho) eqn:glr; [| inv H].
      destruct (find_def v2 f0) eqn:gv1f0; [| inv H].
      destruct p. destruct p.
      destruct (f =? f1)%positive eqn:ff1; [| inv H].
      apply Peqb_true_eq in ff1. subst.
      simpl in H.
      destruct (set_lists l1 l0 (def_funs f0 f0 t t)) eqn:ll0; [| inv H].
      simpl in H.
      destruct (bstep_f t0 e0 n) as [ exc | [ oot | v' ] ] eqn:Heval; simpl.
      + simpl in H. congruence.
      + simpl in H. congruence.
      + simpl in H.
        apply IHn in H. inv H.
        apply IHn in Heval. inv Heval.
        eexists. eapply BStep_letapp; try eassumption.
    - apply IHn in H. inv H.
      exists x.
      constructor;
        auto.
    - destruct (M.get v0 rho) eqn:gv0r; [| inv H].
      destruct v1; [inv H| | inv H].
      destruct (get_list l rho) eqn:glr; [| inv H].
      destruct (find_def v1 f0) eqn:gv1f0; [| inv H].
      destruct p. destruct p.
      destruct (f =? f1)%positive eqn:ff1; [| inv H].
      apply Peqb_true_eq in ff1. subst. simpl in *.
      destruct (set_lists l1 l0 (def_funs f0 f0 t t)) eqn:ll0; [| inv H].
      simpl in H.
      apply IHn in H. inv H. exists (x+1)%nat.
      econstructor; eauto.
    - destruct (get_list l rho) eqn:glr; [| inv H].
      destruct (M.get p pr) eqn:ppr; [| inv H].
      destruct (o l0) eqn:ol0; [| inv H].
      simpl in H. rewrite ol0 in H. simpl in H.
      apply IHn in H. inv H. exists x.
      econstructor; eauto.
      rewrite ol0 in H1. simpl in H1. inv H1.
    - destruct (M.get v0 rho) eqn:gv0r.
      inv H.
      exists 0%nat. constructor; auto.
      inv H.
  Qed.


  (** Big step semantics with a more precise cost model.
   * The goal is that the number of machine instructions that
   * correspond to each rule is proportional to the assigned cost. *)
  Inductive bstep_cost :  env -> exp -> val -> nat -> Prop :=
  | BStepc_constr :
      forall (x : var) (t : ctor_tag) (ys :list var) (e : exp)
             (rho rho' : env) (vs : list val) (v : val) (c : nat),
        get_list ys rho = Some vs ->
        M.set x (Vconstr t vs) rho = rho' ->
        bstep_cost rho' e v c ->
        bstep_cost rho (Econstr x t ys e) v (c + 1 + (List.length ys))
  | BStepc_proj :
      forall (t : ctor_tag) (vs : list val)
             (rho : env) (x : var) (n : N) (y : var)
             (e : exp) (v v': val) (c : nat),
        M.get y rho = Some (Vconstr t vs) ->
        (* The number of instructions generated here should be
         * independent of n. We just need to add an offset *)
        nthN vs n = Some v ->
        bstep_cost (M.set x v rho) e v' c ->
        bstep_cost rho (Eproj x t n y e) v' (c + 1)
  | BStepc_case :
      forall (y : var) (v : val) (e : exp) (t : ctor_tag) (cl : list (ctor_tag * exp))
             (vl : list val) (rho : env) (n c : nat),
        M.get y rho = Some (Vconstr t vl) ->
        caseConsistent cenv cl t ->
        find_tag_nth cl t e n ->
        bstep_cost rho e v c ->
        bstep_cost rho (Ecase y cl) v (c + n)
  | BStepc_app :
      forall (rho' : env) (fl : fundefs) (f' : var) (vs : list val)
             (xs : list var) (e : exp) (rho'' rho : env) (f : var)
             (t : ctor_tag) (ys : list var) (v : val) (c : nat),
        M.get f rho = Some (Vfun rho' fl f') ->
        get_list ys rho = Some vs ->
        (* The number of instructions generated here should be
         * independent of the size of B. We just need to
         * jump to a label *)
        find_def f' fl = Some (t,xs,e) ->
        set_lists xs vs (def_funs fl fl rho' rho') = Some rho'' ->
        bstep_cost rho'' e v c ->
        bstep_cost rho (Eapp f t ys) v (c + 1 + List.length ys)
  | BStepc_letapp :
      forall (rho' : env) (fl : fundefs) (f' : var) (vs : list val)
             (xs : list var) (e_body e : exp) (rho'' rho : env) (x f : var)
             (t : ctor_tag) (ys : list var) (v v' : val) (c c' : nat),
        (* evaluate application *)
        M.get f rho = Some (Vfun rho' fl f') ->
        get_list ys rho = Some vs ->
        find_def f' fl = Some (t,xs,e_body) ->
        set_lists xs vs (def_funs fl fl rho' rho') = Some rho'' ->
        bstep_cost rho'' e_body v c -> (* body evaluates to v *)
        (* evaluate let continuation *)
        bstep_cost (M.set x v rho) e v' c' ->
        bstep_cost rho (Eletapp x f t ys e) v' (c + c' + 1 + List.length ys)  (* force equality on [t] *)
  | BStepc_fun :
      forall (rho : env) (B : fundefs) (e : exp) (v : val) (c : nat),
        bstep_cost (def_funs B B rho rho) e v c ->
        (* The definition of a function incur cost proportional to the number of FVs
           (to make the bound of the current cc independent of the term) *)
        (* TODO eventually remove the unit cost, it helps but it shouldn't be required *)
        bstep_cost rho (Efun B e) v (c + (1 + PS.cardinal (fundefs_fv B)))
  | BStepc_prim :
      forall (vs : list val) (rho' rho : env) (x : var) (f : prim)
             (f' : list val -> option val) (ys : list var) (e : exp)
             (v v' : val) (c : nat),
        get_list ys rho = Some vs ->
        M.get f pr = Some f' ->
        f' vs = Some v ->
        M.set x v rho = rho' ->
        bstep_cost rho' e v' c ->
        bstep_cost rho (Eprim x f ys e) v' (c + 1 + List.length ys)
  | BStepc_halt :
      forall x v rho,
        M.get x rho = Some v ->
        bstep_cost rho (Ehalt x) v 1.

  Lemma find_tag_nth_deterministic l c e n e' n' :
    find_tag_nth l c e n ->
    find_tag_nth l c e' n' ->
    e = e' /\ n = n'.
  Proof.
    intros H1.
    revert e' n'; induction H1; intros e1 n1 H2;
      inv H2; try congruence; eauto. eapply IHfind_tag_nth in H8.
    inv H8; eauto.
  Qed.


  (** Big step semantics with cost counting as fuel. Can raise out-of-time exception.
      Needed to prove divergence preservation *)

  Inductive res {A} : Type :=
  | OOT
  | Res : A -> res.

  Definition cost (e : exp) : nat :=
    match e with
    | Econstr x t ys e => 1 (* + length ys *)
    | Eproj x t n y e => 1
    | Ecase y cl => 1
    | Eapp f t ys => 1 (* + length ys *)
    | Eletapp x f t ys e => 1 (* + length ys *)
    | Efun B e => 1 (* + PS.cardinal (fundefs_fv B) *)
    | Eprim x f ys e => 1 (* + length ys *)
    | Ehalt x => 1
    end.
  
  Context {steps: Type} {Hr : @resource_exp steps}.

  Open Scope alg_scope.

  Inductive bstep :  env -> exp -> @res val -> steps -> Prop :=
  | BStept_constr :
      forall (x : var) (t : ctor_tag) (ys :list var) (e : exp)
             (rho rho' : env) (vs : list val) (v : res) (cin : steps),
        get_list ys rho = Some vs ->
        M.set x (Vconstr t vs) rho = rho' ->
        bstep_fuel rho' e v cin ->
        bstep rho (Econstr x t ys e) v cin
  | BStept_proj :
      forall (t : ctor_tag) (vs : list val)
             (rho : env) (x : var) (n : N) (y : var)
             (e : exp) (v : val) (v' : res) (cin : steps),
        M.get y rho = Some (Vconstr t vs) ->
        nthN vs n = Some v ->
        bstep_fuel (M.set x v rho) e v' cin ->
        bstep rho (Eproj x t n y e) v' cin
  | BStept_case :
      forall (y : var) (v : res) (e : exp) (t : ctor_tag) (cl : list (ctor_tag * exp))
             (vl : list val) (rho : env) (cin : steps) (n : nat),
        M.get y rho = Some (Vconstr t vl) ->
        caseConsistent cenv cl t ->
        find_tag_nth cl t e n ->
        bstep_fuel rho e v cin ->
        bstep rho (Ecase y cl) v cin
  | BStept_app :
      forall (rho' : env) (fl : fundefs) (f' : var) (vs : list val)
             (xs : list var) (e : exp) (rho'' rho : env) (f : var)
             (t : ctor_tag) (ys : list var) (v : res) (cin : steps),
        M.get f rho = Some (Vfun rho' fl f') ->
        get_list ys rho = Some vs ->
        (* The number of instructions generated here should be
         * independent of the size of B. We just need to
         * jump to a label *)
        find_def f' fl = Some (t,xs,e) ->
        set_lists xs vs (def_funs fl fl rho' rho') = Some rho'' ->
        bstep_fuel rho'' e v cin ->
        bstep rho (Eapp f t ys) v cin
  | BStept_letapp :
      forall (rho' : env) (fl : fundefs) (f' : var) (vs : list val)
             (xs : list var) (e_body e : exp) (rho'' rho : env) (x f : var)
             (t : ctor_tag) (ys : list var) (v : val) (v' : res) (cin1 cin2 : steps),
        (* evaluate application *)
        M.get f rho = Some (Vfun rho' fl f') ->
        get_list ys rho = Some vs ->
        find_def f' fl = Some (t,xs,e_body) ->
        set_lists xs vs (def_funs fl fl rho' rho') = Some rho'' ->
        bstep_fuel rho'' e_body (Res v) cin1 -> (* body evaluates to v *)
        (* evaluate let continuation *)
        bstep_fuel (M.set x v rho) e v' cin2 ->
        bstep rho (Eletapp x f t ys e) v' (cin1 <+> cin2)
  | BStept_letapp_oot :
      forall (rho' : env) (fl : fundefs) (f' : var) (vs : list val)
             (xs : list var) (e_body e : exp) (rho'' rho : env) (x f : var)
             (t : ctor_tag) (ys : list var) (cin : steps),
        M.get f rho = Some (Vfun rho' fl f') ->
        get_list ys rho = Some vs ->
        find_def f' fl = Some (t,xs,e_body) ->
        set_lists xs vs (def_funs fl fl rho' rho') = Some rho'' ->
        bstep_fuel rho'' e_body OOT cin -> (* body times out*)
        bstep rho (Eletapp x f t ys e) OOT cin
  | BStept_fun :
      forall (rho : env) (B : fundefs) (e : exp) (v : res) (cin : steps),
        bstep_fuel (def_funs B B rho rho) e v cin ->
        (* The definition of a function incur cost proportional to the number of FVs
        (to make the bound of the current cc independent of the term) *)
        bstep rho (Efun B e) v cin
  (* | BStept_prim :
      forall (vs : list val) (rho' rho : env) (x : var) (f : prim)
        (f' : list val -> option val) (ys : list var) (e : exp)
        (v : val) (v' : res) (cin : nat),
          get_list ys rho = Some vs ->
          M.get f pr = Some f' ->
          f' vs = Some v ->
          M.set x v rho = rho' ->
          bstep_fuel rho' e v' cin ->
          bstep rho (Eprim x f ys e) v' cin *)
  | BStept_halt :
      forall x v rho,
        M.get x rho = Some v ->
        bstep rho (Ehalt x) (Res v) <0>
  with bstep_fuel :  env -> exp -> @res val -> steps -> Prop :=
  | BStepf_OOT : (* not enought time units to take astep *)
      forall rho (e : exp) (c : steps),
        (c <<_{ e } <1> e) -> (* not enough steps *)
        bstep_fuel rho e OOT c
  | BStepf_run : (* take a step *)
      forall rho e r (c : steps),
        bstep rho e r c ->
        bstep_fuel rho e r (c <+> (<1> e)).

  Scheme bstep_ind' := Minimality for bstep Sort Prop
    with bstep_fuel_ind' := Minimality for bstep_fuel Sort Prop.
  
  Definition not_stuck (rho : env) (e : exp) :=
    (exists c v, bstep_fuel rho e (Res v) c) \/
    (forall c, bstep_fuel rho e OOT c).

  Ltac destruct_bstep :=
    match goal with
    | [ H : bstep _ _ _ _ |- _ ] => inv H
    end.

  Lemma cost_gt_0 e : 
    (0 < cost e)%nat.
  Proof.  
    destruct e; simpl; omega. 
  Qed.

  (** * Lemmas about bstep_fuel *)
  Lemma step_deterministic_aux rho e r v c r' v' c' :
    bstep rho e r c ->
    bstep rho e r' c' ->
    r = Res v -> r' = Res v' ->
    v = v' /\ c = c'.
  Proof.
    set (P := fun rho e r c =>
                forall v r' v' c',
                  bstep rho e r' c' ->
                  r = Res v -> r' = Res v' ->
                  v = v' /\ c = c').
    set (P0 := fun rho e r c =>
                 forall v r' v' c',
                   bstep_fuel rho e r' c' ->
                   r = Res v -> r' = Res v' ->
                   v = v' /\ c = c').
    intros Hstep.
    revert v r' v' c'.
    induction Hstep using bstep_ind' with (P := P) (P0 := P0); unfold P, P0 in *;
      intros v1 r2 v2 c2 Hstep2 Heq1 Heq2; subst;
        try now (inv Hstep2; repeat subst_exp; eapply IHHstep; eauto).
    - inv Hstep2. repeat subst_exp.
      eapply find_tag_nth_deterministic in H1; [| eapply H8 ]. inv H1.
      eapply IHHstep; eauto.
    - inv Hstep2. repeat subst_exp. eapply IHHstep in H17; eauto. inv H17.
      eapply IHHstep0 in H18; eauto. inv H18. eauto.
    - inv Hstep2. inv Heq1. repeat subst_exp. eauto.
    - inv Heq1.
    - inv Hstep2. eapply IHHstep in H; eauto. inv H.
      split; eauto.
  Qed.

  Lemma bstep_fuel_deterministic rho e v c v' c' :
    bstep_fuel rho e (Res v) c ->
    bstep_fuel rho e (Res v') c' ->
    v = v' /\ c = c'.
  Proof.
    intros H1 H2; inv H1; inv H2; eauto.
    eapply step_deterministic_aux in H0; [ | eapply H | reflexivity | reflexivity ].
    inv H0. split; eauto.
  Qed.

  Lemma bstep_deterministic rho e v c v' c' :
    bstep rho e (Res v) c ->
    bstep rho e (Res v') c' ->
    v = v' /\ c = c'.
  Proof.
    intros H1 H2. eapply step_deterministic_aux; eauto.
  Qed.

  Lemma bstep_lt_OOT_aux rho e r c (v : val) c' i:
    bstep rho e r c ->
    r = Res v ->
    (c' <<_{ i } c) -> (* the resource is smaller in any dimention *)
    bstep rho e OOT c'.
  Proof.
    set (P := fun rho e r c =>
                forall i (v : val) c',
  		  r = Res v -> c' <<_{ i } c ->
		  bstep rho e OOT c').
    set (P0 := fun rho e r c =>
                 forall i (v : val) c',
  		   r = Res v -> c' <<_{ i } c ->
		   bstep_fuel rho e OOT c').
    intros Hstep. revert i v c'.
    induction Hstep using bstep_ind' with (P := P) (P0 := P0); unfold P, P0 in *;
      intros i v1 c' Heq Hlt; subst; try now (econstructor; eauto).
    - edestruct (lt_all_dec_exp c' cin1).
      + inv H5. eapply BStept_letapp_oot; eauto.
      + inv H5. 
        rewrite plus_comm. eapply BStept_letapp; eauto. eapply IHHstep0. reflexivity.
        rewrite (plus_comm cin1) in Hlt. eapply plus_stable in Hlt. eassumption.
    - eapply lt_zero in Hlt. contradiction.
    - edestruct (lt_dec_i c' (exp_to_fin e)).
      + econstructor 1; eauto.
      + inv H. econstructor 2. eapply IHHstep. reflexivity.
        eapply plus_stable in Hlt. eassumption.
  Qed.

  Lemma bstep_lt_OOT rho e v c c' i :
    bstep rho e (Res v) c ->
    c' <<_{ i } c ->
    bstep rho e OOT c'.
  Proof.
    intros; eapply bstep_lt_OOT_aux; eauto.
  Qed.

  Lemma bstep_fuel_lt_OOT rho e v c c' i :
    bstep_fuel rho e (Res v) c ->
    c' <<_{ i } c ->
    bstep_fuel rho e OOT c'.
  Proof.
    intros H1 Hlt; inv H1.
    edestruct (lt_dec_i c' (exp_to_fin e)).
    + econstructor 1; eauto.
    + inv H0. econstructor 2. eapply bstep_lt_OOT. eassumption.
      eapply plus_stable in Hlt. eassumption.
  Qed.        

  Lemma bstep_OOT_determistic_aux rho e (r r' : @res val) c1 c2 c :
    bstep rho e r c ->
    r = OOT ->
    c = (c1 <+> c2) ->
    bstep rho e r' c1 -> r' = OOT.
  Proof.
    set (P := fun rho e (r : @res val) c =>
                forall r' c1 c2,
                  r = OOT ->
                  c = (c1 <+> c2) ->
                  bstep rho e r' c1 -> r' = OOT).
    set (P0 := fun rho e (r : @res val) c =>
                 forall r' c1 c2,
                   r = OOT ->
                   c = (c1 <+> c2) ->
                   bstep_fuel rho e r' c1 -> r' = OOT).
    intros Hstep. revert r' c1 c2.
    induction Hstep using bstep_ind' with (P := P) (P0 := P0); unfold P, P0 in *;
      intros r' c1 c2 Heq Hleq Hs'; subst; try now (inv Hs'; repeat subst_exp; eauto).
    - inv Hs'; repeat subst_exp. eapply find_tag_nth_deterministic in H8; [| clear H8; eauto ]. inv H8.
      eapply IHHstep; eauto.
    - inv Hs'; repeat subst_exp; eauto.
      eapply bstep_fuel_deterministic in H17; [| clear H17; eauto ]; inv H17.
      eapply IHHstep0; [| | eassumption ]; eauto. rewrite plus_assoc, !(plus_comm cin0) in Hleq.
      eapply plus_inv in Hleq. subst. reflexivity.
    - inv Hs'; repeat subst_exp; eauto. exfalso.
      eapply IHHstep in H16; eauto. congruence. rewrite plus_assoc. reflexivity.
    - inv Hs'; eauto. eapply plus_lt in H. rewrite plus_comm in H. eapply plus_lt in H.
      eapply lt_antisym in H. contradiction. 
    - inv Hs'; eauto. eapply IHHstep; [| | eassumption ]; eauto.
      rewrite plus_assoc, !(plus_comm _ c2), <- plus_assoc in Hleq.
      eapply plus_inv in Hleq. subst. reflexivity.
  Qed.

  Lemma bstep_OOT_determistic rho e r' c1 c2 :
    bstep rho e OOT (c1 <+> c2) ->
    bstep rho e r' c1 -> r' = OOT.
  Proof.
    intros; eapply bstep_OOT_determistic_aux; [ | reflexivity | | ]; eauto.
  Qed.

  Lemma bstep_fuel_OOT_determistic rho e r' c1 c2 :
    bstep_fuel rho e OOT (c1 <+> c2) ->
    bstep_fuel rho e r' c1 -> r' = OOT.
  Proof.
    intros Hs Hs'; inv Hs'; inv Hs; eauto.
    - eapply plus_lt in H0. rewrite plus_comm in H0. eapply plus_lt in H0.
      eapply lt_antisym in H0. contradiction. 
    - rewrite plus_assoc, !(plus_comm _ c2), <- plus_assoc in H0.
      eapply plus_inv in H0. subst.
      eapply bstep_OOT_determistic; eauto.
  Qed.

  Lemma bstep_gt_aux rho e r c (v : val) r' c' :
    bstep rho e r c ->
    r = Res v -> (forall i, c <<_{ i } c') ->
    ~ bstep rho e r' c'.
  Proof.
    set (P := fun rho e r c =>
                forall (v : val) r' c',
                  r = Res v -> (forall i, c <<_{ i } c') ->
                  ~ bstep rho e r' c').
    set (P0 := fun rho e r c =>
                 forall (v : val) r' c',
                   r = Res v -> (forall i, c <<_{ i } c') ->
                   ~ bstep_fuel rho e r' c').
    intros Hstep. revert v r' c'.
    induction Hstep using bstep_ind' with (P := P) (P0 := P0); unfold P, P0 in *;
      intros v1 r' c' Heq Hlt Hstep'; subst; (try now (inv Hstep'; repeat subst_exp; eauto));
        try now (inv Hstep'; repeat subst_exp; eauto; eapply IHHstep; eauto).
    - inv Hstep'; repeat subst_exp; eauto.
      eapply find_tag_nth_deterministic in H8; [| clear H8; eauto ]. inv H8.
      eapply IHHstep; eauto.
    - inv Hstep'; repeat subst_exp; eauto. 
      + eapply bstep_fuel_deterministic in H17; [| clear H17; eauto ]; inv H17; subst.             
        eapply IHHstep0; [| | eapply H18 ]. reflexivity.
        intros i. specialize (Hlt i). rewrite !(plus_comm cin0) in Hlt. eapply plus_stable in Hlt. 
        eassumption.
      + eapply IHHstep; [| | eassumption ]. reflexivity.
        intros i. eapply plus_lt. eapply Hlt.
    - inv Hstep'. eapply lt_antisym. eapply Hlt.
    - inv Hstep'.
      + eapply lt_antisym. eapply lt_trans. eassumption.
        eapply plus_lt. rewrite plus_comm. eapply Hlt. 
      + eapply IHHstep; [| | eassumption ]. reflexivity.
        intros i. specialize (Hlt i). eapply plus_stable in Hlt. eassumption.

        Grab Existential Variables. exact (Ehalt xH). 
  Qed.

  Lemma bstep_gt rho e r c v c' :
    bstep rho e (Res v) c ->
    (forall i, c <<_{ i } c') ->
    ~ bstep rho e r c'.
  Proof.
    intros; eapply bstep_gt_aux; eauto.
  Qed.
  
  Lemma bstep_fuel_gt rho e r c v c' :
    bstep_fuel rho e (Res v) c ->
    (forall i, c <<_{ i } c') ->
    ~ bstep_fuel rho e r c'.
  Proof.
    intros Hstep Hlt Hstep'. inv Hstep. inv Hstep'.
    - eapply lt_antisym. eapply lt_trans. eassumption.
        eapply plus_lt. rewrite plus_comm. eapply Hlt. 
    - eapply bstep_gt; [ eassumption | | eassumption ].
      intros i. specialize (Hlt i). eapply plus_stable in Hlt. eassumption.
  Qed.

  Lemma bstep_OOT_monotonic_aux rho e r (c c1 c2 : steps):
    bstep rho e r c ->
    r = OOT ->
    c = (c1 <+> c2) ->
    bstep rho e OOT c1.
  Proof.
    set (P := fun rho e (r : @res val) c =>
                forall c1 c2,
                  r = OOT ->
                  c = (c1 <+> c2) ->
                  bstep rho e OOT c1).
    set (P0 := fun rho e (r : @res val) c =>
                 forall c1 c2,
                   r = OOT ->
                   c = (c1 <+> c2) ->
                   bstep_fuel rho e OOT c1).
    intros Hstep. revert c1 c2. 
    induction Hstep using bstep_ind' with (P := P) (P0 := P0); unfold P, P0 in *;
    intros c1 c2 Heq Hleq; subst; try now (econstructor; eauto).
    - edestruct (lt_all_dec_exp c1 cin1).
      + inv H5. eapply BStept_letapp_oot; eauto.
        eapply bstep_fuel_lt_OOT. eassumption. eassumption.
      + inv H5. rewrite (plus_comm x0), plus_assoc in Hleq.
        rewrite !(plus_comm cin1) in Hleq. eapply plus_inv in Hleq. subst.
        rewrite plus_comm. eapply BStept_letapp; eauto.
    - inv Heq.
    - econstructor. eapply plus_lt. eassumption.
    - edestruct (lt_dec_i c1 (exp_to_fin e)).
      now econstructor; eauto. inv H.
      rewrite plus_assoc, (plus_comm _ c2), <- plus_assoc in Hleq.
      eapply plus_inv in Hleq. econstructor 2; eauto.
  Qed.

  Lemma bstep_OOT_monotonic rho e c1 c2 :
    bstep rho e OOT (c1 <+> c2) ->
    bstep rho e OOT c1.
  Proof.
    intros; eapply bstep_OOT_monotonic_aux; eauto.
  Qed.
  
  Lemma bstep_fuel_OOT_monotonic rho e c1 c2 :
    bstep_fuel rho e OOT (c1 <+> c2) ->   
    bstep_fuel rho e OOT c1.
  Proof.
    intros H1. inv H1.
    - econstructor. eapply plus_lt. eassumption.
    - edestruct (lt_dec_i c1 (exp_to_fin e)).
      now econstructor; eauto. inv H0.
      rewrite plus_assoc, (plus_comm _ c2), <- plus_assoc in H.
      eapply plus_inv in H. econstructor 2. subst. eapply bstep_OOT_monotonic; eauto.
  Qed. 

  Lemma bstep_fuel_zero_OOT rho e :
    bstep_fuel rho e OOT <0>.
  Proof.
    econstructor. eapply zero_one_lt_i.
  Qed.
    
  Lemma bstep_deterministic_res rho e r c r' :
    bstep rho e r c ->
    bstep rho e r' c ->
    r = r'.
  Proof.
    set (P := fun rho e r c =>
                forall r',
                  bstep rho e r' c ->
                  r = r').
    set (P0 := fun rho e r c =>
                 forall r',
                   bstep_fuel rho e r' c ->
                   r = r').
    intros Hstep.
    revert r'.
    induction Hstep using bstep_ind' with (P := P) (P0 := P0); unfold P, P0 in *; intros r' Hstep';
      try now (inv Hstep'; repeat subst_exp; eapply IHHstep; eauto). 
    - inv Hstep'. repeat subst_exp.
      eapply find_tag_nth_deterministic in H1; [| eapply H8 ]. inv H1.
      eapply IHHstep; eauto.
    - inv Hstep'; repeat subst_exp.
      + eapply bstep_fuel_deterministic in H17; [| clear H17; eauto ]. inv H17; subst. repeat subst_exp.
        rewrite !(plus_comm cin0) in H10. 
        eapply plus_inv in H10. subst. eapply IHHstep0; eauto.
      + eapply bstep_fuel_OOT_monotonic in H17. eapply IHHstep in H17. congruence. 
    - inv Hstep'; repeat subst_exp; eauto. 
      eapply bstep_fuel_OOT_determistic in H16; [| eassumption ]. congruence. 
    - inv Hstep'. repeat subst_exp; eauto.
    - inv Hstep'; eauto. rewrite plus_comm in H. eapply plus_lt in H. eapply lt_antisym in H.
      contradiction.
    - inv Hstep'; eauto.
      rewrite plus_comm in H. eapply plus_lt in H. eapply lt_antisym in H. contradiction.
      eapply plus_inv in H. subst. eapply IHHstep. eassumption. 
  Qed.

  Lemma bstep_fuel_deterministic_res rho e r c r' :
    bstep_fuel rho e r c ->
    bstep_fuel rho e r' c ->
    r = r'.
  Proof.
    intros H1 H2. inv H1; inv H2; eauto.
    rewrite plus_comm in H. eapply plus_lt in H. eapply lt_antisym in H. contradiction.
    rewrite plus_comm in H0. eapply plus_lt in H0. eapply lt_antisym in H0. contradiction.
    eapply plus_inv in H0. subst. eapply bstep_deterministic_res. eassumption. eassumption.
  Qed.
  
  
  Definition diverge (rho : env) (e: exp) : Prop :=
    forall c, bstep_fuel rho e OOT c.

  (** * Interpretation of (certain) evaluation contexts as environments *)

  Inductive ctx_to_rho : exp_ctx -> env -> env -> Prop :=
  | Hole_c_to_rho :
      forall rho,
        ctx_to_rho Hole_c rho rho
  | Eproj_c_to_rho :
      forall rho rho' t y N Γ C vs v,
        M.get Γ rho = Some (Vconstr t vs) ->
        nthN vs N = Some v ->
        ctx_to_rho C (M.set y v rho) rho' ->
        ctx_to_rho (Eproj_c y t N Γ C) rho rho'
  | Econstr_c_to_rho :
      forall rho rho' x t ys C vs,
        get_list ys rho = Some vs ->
        ctx_to_rho C (M.set x (Vconstr t vs) rho) rho' ->
        ctx_to_rho (Econstr_c x t ys C) rho rho'
  | Efun_c_to_rho :
      forall rho rho' C B,
        ctx_to_rho C (def_funs B B rho rho) rho' ->
        ctx_to_rho (Efun1_c B C) rho rho'.


  (** * Lemmas about [ctx_to_rho] *)

  Lemma ctx_to_rho_comp_ctx_l C C1 C2 rho rho' :
    ctx_to_rho C rho rho' ->
    comp_ctx C1 C2 C ->
    exists rho'',
      ctx_to_rho C1 rho rho'' /\
      ctx_to_rho C2 rho'' rho'.
  Proof.
    intros Hctx. revert C1 C2.
    induction Hctx; intros C1 C2 Hcomp.
    - inv Hcomp. eexists; split; constructor.
    - inv Hcomp.
      + edestruct IHHctx as [rho'' [H1 H2]].
        constructor. inv H1.
        eexists; split. constructor.
        econstructor; eauto.
      + edestruct IHHctx as [rho'' [H1 H2]]. eassumption.
        eexists; split. econstructor; eauto.
        eassumption.
    - inv Hcomp.
      + edestruct IHHctx as [rho'' [H1 H2]].
        constructor. inv H1.
        eexists; split. constructor.
        econstructor; eauto.
      + edestruct IHHctx as [rho'' [H1 H2]]. eassumption.
        eexists; split. econstructor; eauto.
        eassumption.
    - inv Hcomp.
      eexists; split. econstructor; eauto. econstructor. now eauto.
      edestruct IHHctx as [rho'' [H1 H2']]. eassumption.
      eexists; split. econstructor; eauto.
      eassumption.
  Qed.

  Lemma ctx_to_rho_comp_ctx_f_r C1 C2 rho1 rho2 rho3 :
    ctx_to_rho C1 rho1 rho2 ->
    ctx_to_rho C2 rho2 rho3 ->
    ctx_to_rho (comp_ctx_f C1 C2) rho1 rho3.
  Proof.
    revert C2 rho1 rho2 rho3.
    induction C1; intros C2 rho1 rho2 rho3 Hctx1 GHctx2; inv Hctx1.
    - eassumption.
    - simpl; econstructor; eauto.
    - simpl; econstructor; eauto.
    - simpl; econstructor; eauto.
  Qed.


  (** * Interpretation of interprable evaluation contexts as environments *)

  Fixpoint interprable (C : exp_ctx) : bool :=
    match C with
    | Hole_c => true
    | Econstr_c _ _ _ C
    | Eproj_c _ _ _ _ C
    | Eprim_c _ _ _ C
    | Efun1_c _ C
    | Eletapp_c _ _ _ _ C => interprable C
    | Ecase_c _ _ _ _ _
    | Efun2_c _ _ => false
    end.


  Definition cost_ctx (c : exp_ctx) : nat :=
    match c with
    | Econstr_c x t ys c => 1 (* + length ys *)
    | Eproj_c x t n y c => 1
    | Ecase_c _ _ _ _ _ => 1
    | Eletapp_c x f t ys c => 1 (* + length ys *)
    | Efun1_c B c => 1
    | Efun2_c _ _ => 1
    | Eprim_c x f ys c => 1 (* + length ys *)
    | Ehole_c => 0
    end.

  Inductive interpret_ctx : exp_ctx -> env -> @res env -> steps -> Prop :=
  | Eproj_c_i :
      forall rho r t y N Γ C vs v (n : steps),
        M.get Γ rho = Some (Vconstr t vs) ->
        nthN vs N = Some v ->
        interpret_ctx_fuel C (M.set y v rho) r n ->
        interpret_ctx (Eproj_c y t N Γ C) rho r n
  | Econstr_c_i :
      forall rho r x t ys C vs n,
        get_list ys rho = Some vs ->
        interpret_ctx_fuel C (M.set x (Vconstr t vs) rho) r n ->
        interpret_ctx (Econstr_c x t ys C) rho r n
  | Efun_c_i :
      forall rho r C B n,
        interpret_ctx_fuel C (def_funs B B rho rho) r n ->
        interpret_ctx (Efun1_c B C) rho r n
  | Eletapp_c_i :
      forall rho fl rhoc rhoc' f' vs xs e_body c x f t ys v r n1 n2,
        rho ! f = Some (Vfun rhoc fl f') ->
        get_list ys rho = Some vs ->
        find_def f' fl = Some (t, xs, e_body) ->
        set_lists xs vs (def_funs fl fl rhoc rhoc) = Some rhoc' ->
        bstep_fuel rhoc' e_body (Res v) n1 ->
        interpret_ctx_fuel c (M.set x v rho) r n2 ->
        interpret_ctx (Eletapp_c x f t ys c) rho r (n1 <+> n2)
  | Eletapp_c_i_OOT :
      forall rho fl rhoc rhoc' f' vs xs e_body c x f t ys n,
        rho ! f = Some (Vfun rhoc fl f') ->
        get_list ys rho = Some vs ->
        find_def f' fl = Some (t, xs, e_body) ->
        set_lists xs vs (def_funs fl fl rhoc rhoc) = Some rhoc' ->
        bstep_fuel rhoc' e_body OOT n ->
        interpret_ctx (Eletapp_c x f t ys c) rho OOT n
  with interpret_ctx_fuel : exp_ctx -> env -> @res env -> steps -> Prop :=
  | ctx_hole:
      forall rho,
        interpret_ctx_fuel Hole_c rho (Res rho) <0>
  | ctx_OOT :
      forall c rho n,
        lt_i (exp_ctx_to_fin c) n (one_ctx c) ->
        c <> Hole_c ->
        interpret_ctx_fuel c rho OOT n
  | ctx_step :
      forall c rho r (n : steps),
        c <> Hole_c ->
        interpret_ctx c rho r n  ->
        interpret_ctx_fuel c rho r (n <+> one_ctx c).
  

  Lemma interpret_ctx_bstep_l C e rho v n:
    bstep_fuel rho (C|[ e ]|) (Res v) n ->
    interprable C = true ->
    exists rho' n1 n2,
      (n1 <+> n2) = n /\
      interpret_ctx_fuel C rho (Res rho') n1 /\
      bstep_fuel rho' e (Res v) n2.
  Proof.
    revert e rho v n; induction C; intros e1 rho v1 c1 Hb Hi; try now inv Hi.
    - simpl in Hb. exists rho, <0>, c1. split; [| split; eauto ].
      rewrite plus_zero. reflexivity. econstructor.
    - simpl in Hb, Hi. inv Hb. inv H.
      edestruct IHC as (rho' & n1 & n2 & Hadd & Hi' & Hstep); [ eassumption | eassumption | ].
      eexists. exists (n1 <+> one_ctx (Econstr_c v c l C)). eexists. split; [| split; eauto ].
      2:{ econstructor; eauto. congruence. econstructor; eauto. }
      rewrite plus_assoc, (plus_comm _ n2), <- plus_assoc. rewrite <- Hadd. reflexivity.
    - simpl in Hb, Hi. inv Hb. inv H.
      edestruct IHC as (rho' & n1 & n2 & Hadd & Hi' & Hstep); [ eassumption | eassumption | ].
      simpl in Hadd.
      eexists. exists (n1 <+> one_ctx (Eproj_c v c n v0 C)). eexists. split; [| split; eauto ].
      2:{ econstructor; eauto. congruence. econstructor; eauto. }
      rewrite <- Hadd.
      rewrite plus_assoc, (plus_comm _ n2), <- plus_assoc. simpl. reflexivity.
    - simpl in Hb, Hi. inv Hb. inv H.
    - simpl in Hb, Hi. inv Hb. inv H.
      edestruct IHC as (rho1 & n1 & n2 & Hadd & Hi' & Hstep); [ eassumption | eassumption | ].
      eexists. exists (cin1 <+> n1 <+> one_ctx (Eletapp_c v v0 f l C))%nat.
      eexists. split; [| split; eauto ].
      2:{ econstructor; eauto. congruence. econstructor; eauto. }
      rewrite <- Hadd.
      rewrite plus_assoc, (plus_comm _ n2), <- !plus_assoc. simpl. reflexivity.      
    - simpl in Hb, Hi. inv Hb. inv H.
      edestruct IHC as (rho' & n1 & n2 & Hadd & Hi' & Hstep); [ eassumption | eassumption | ].
      simpl in Hadd.
      eexists. exists (n1 <+> one_ctx (Efun1_c f C)). eexists. split; [| split; eauto ].
      2:{ econstructor; eauto. congruence. econstructor; eauto. }
      simpl in *.
      rewrite <- Hadd.
      rewrite plus_assoc, (plus_comm _ n2), <- plus_assoc. simpl. reflexivity.
  Qed.

  Lemma interpret_ctx_bstep_r C e rho rho' r n1 n2:
    interpret_ctx_fuel C rho (Res rho') n1 ->
    bstep_fuel rho' e r n2 ->
    bstep_fuel rho (C|[ e ]|) r (n1 <+> n2).
  Proof.
    revert e rho rho' r n1 n2; induction C; intros e1 rho rho' r n1 n2 Hi Hs1; (try now inv Hi);
      try (now (inv Hi; inv H0;
                rewrite plus_assoc, (plus_comm (one_ctx _)), <- plus_assoc;
                econstructor; econstructor; eauto)).
    - inv Hi. simpl. rewrite plus_zero. eassumption. simpl.
      inv H0.
    - inv Hi. inv H0. simpl in *.
      rewrite plus_assoc, (plus_comm (one_ctx _)), <- plus_assoc.
      econstructor. rewrite plus_assoc. econstructor; eauto.       
  Qed.

  Lemma interpret_ctx_OOT_bstep C e rho n:
    interpret_ctx_fuel C rho OOT n ->
    bstep_fuel rho (C|[ e ]|) OOT n.
  Proof.
    revert e rho n; induction C; intros e1 rho n1 Hi; (try now inv Hi);
      try now (inv Hi; simpl in *;
               [ econstructor 1; eassumption |
                 inv H0; econstructor 2; econstructor; eauto
              ]).
  Qed.

  Lemma interprable_comp_f_l C1 C2:
    interprable C1 = true -> interprable C2 = true ->
    interprable (comp_ctx_f C1 C2) = true.
  Proof.
    induction C1; intros H1 H2; simpl in *; eauto.
  Qed.

  Lemma interprable_comp_f_r C1 C2:
    interprable (comp_ctx_f C1 C2) = true ->
    interprable C1 = true /\ interprable C2 = true.
  Proof.
    induction C1; intros H1; simpl in *; eauto.
    congruence. congruence.
  Qed.

  Lemma interprable_inline_letapp e x C z :
    inline_letapp e x = Some (C, z) ->
    interprable C = true.
  Proof.
    revert x C z; induction e; intros x C z Hin; simpl in *;
      try match goal with
          | [ _ : context[inline_letapp ?E ?X] |- _] =>
            destruct (inline_letapp E X) as [ [C' z'] |] eqn:Hin'; inv Hin; simpl; eauto
          end.
    now inv Hin. inv Hin. reflexivity. inv Hin. reflexivity.
  Qed.


  (* 
  Lemma eval_ctx_app_OOT_Ehalt rho C e n x :
    bstep_fuel rho (C |[ Ehalt x ]|) OOT n ->
    interprable C = true ->
    bstep_fuel rho (C |[ e ]|) OOT n.
  Proof.
    revert rho e n.
    induction C; intros rho e1 cin Hs Hi; eauto;
      try congruence;
      try now (simpl in *; inv Hs; 
               [ econstructor; eassumption |
                 inv H; unfold one; simpl; constructor 2; econstructor; eauto ]).
    
    - simpl in *. inv Hs. econstructor. eapply lt_zero_one in H. subst. eapply zero_one_lt_i.
      inv H.

      Unshelve. exact 0%nat.
  Qed.
  
  Lemma eval_ctx_app_OOT_Eapp rho C e n x f t xs :
    bstep_fuel rho (C |[ Eapp f t xs ]|) OOT n ->
    interprable C = true ->
    bstep_fuel rho (C |[ Eletapp x f t xs e ]|) OOT n.
  Proof.
    revert rho e n.
    induction C; intros rho e1 cin Hs Hi; eauto;
      try congruence;
      try now (inv Hs; 
               [ econstructor; eassumption |
                 inv H; unfold one; simpl; constructor 2; econstructor; eauto ]).

    simpl in *. inv Hs. econstructor. eapply lt_zero_one in H. subst. eapply zero_one_lt_i.
    inv H. erewrite <- one_letapp. econstructor 2. econstructor; eauto.    
    
    Unshelve. exact 0%nat.
  Qed.

  
  Lemma eval_ctx_app_OOT_Eprim rho C x p xs e1 e2 n :
    bstep_fuel rho (C |[ Eprim x p xs e1 ]|) OOT n ->
    interprable C = true ->
    bstep_fuel rho (C |[ Eprim x p xs e2 ]|) OOT n.
  Proof.       
    revert rho n.
    induction C; intros rho cin Hs Hi; eauto;
      try congruence;
      try now (inv Hs; 
               [ econstructor; eassumption |
                 inv H; unfold one; simpl;
                 constructor 2; econstructor; eauto ]).

    Unshelve. exact 0%nat.
  Qed.
  *)
  
  Lemma bstep_cost_deterministic e rho v1 v2 c1 c2 :
    bstep_cost rho e v1 c1 ->
    bstep_cost rho e v2 c2 ->
    v1 = v2 /\ c1 = c2.
  Proof.
    intros Heval1 Heval2.
    revert v2 c2 Heval2; induction Heval1; intros v2 c2 Heval2;
      inv Heval2; repeat subst_exp; eauto;
        try now edestruct IHHeval1 as [Heq1 Heq2]; eauto.
    + eapply find_tag_nth_deterministic in H7; [| clear H7; eauto ]; inv H7.
      eapply IHHeval1 in H10. inv H10. split; congruence.
    + eapply IHHeval1_1 in H15. inv H15.
      eapply IHHeval1_2 in H16. inv H16.
      split; congruence.
  Qed.

  Lemma interpret_ctx_eq_env_P S C rho rho' n :
    interpret_ctx_fuel C rho (Res rho') n ->
    Disjoint _ (bound_var_ctx C) S ->
    eq_env_P S rho rho'.
  Proof.
    revert rho rho' n; induction C; intros rho rho' cost Hin Hd; inv Hin.
    - eapply eq_env_P_refl.
    - inv H0.
    - inv H0. rewrite bound_var_Econstr_c in *.
      eapply eq_env_P_trans; [| eapply IHC; [ eassumption | now sets ] ].
      eapply eq_env_P_sym. eapply eq_env_P_set_not_in_P_l; eauto.
      eapply eq_env_P_refl. eapply Disjoint_In_l. sets. sets.
    - inv H0. rewrite bound_var_Eproj_c in *.
      eapply eq_env_P_trans; [| eapply IHC; [ eassumption | now sets ] ].
      eapply eq_env_P_sym. eapply eq_env_P_set_not_in_P_l; eauto.
      eapply eq_env_P_refl. eapply Disjoint_In_l. sets. sets.
    - inv H0.
    - inv H0. rewrite bound_var_Eletapp_c in *.
      eapply eq_env_P_trans; [| eapply IHC; [ eassumption | now sets ] ].
      eapply eq_env_P_sym. eapply eq_env_P_set_not_in_P_l; eauto.
      eapply eq_env_P_refl. eapply Disjoint_In_l. sets. sets.
    - inv H0.
    - inv H0. rewrite bound_var_Fun1_c in *.
      eapply eq_env_P_trans; [| eapply IHC; [ eassumption | now sets ] ].
      eapply eq_env_P_def_funs_not_in_P_r. eapply eq_env_P_refl.
      eapply Disjoint_Included_r. eapply name_in_fundefs_bound_var_fundefs. sets.
    - inv H0.
  Qed.


  Scheme interpret_ctx_ind' := Minimality for interpret_ctx Sort Prop
    with interpret_ctx_fuel_ind' := Minimality for interpret_ctx_fuel Sort Prop.

  Lemma interpret_ctx_deterministic_aux rho C r v c r' v' c' :
    interpret_ctx C rho r c ->
    interpret_ctx C rho r' c' ->
    r = Res v -> r' = Res v' ->
    v = v' /\ c = c'.
  Proof.
    set (R := fun C rho r c =>
                forall v r' v' c',
                  interpret_ctx C rho r' c' ->
                  r = Res v -> r' = Res v' ->
                  v = v' /\ c = c').
    set (R0 := fun C rho r c =>
                 forall v r' v' c',
                   interpret_ctx_fuel C rho r' c' ->
                   r = Res v -> r' = Res v' ->
                   v = v' /\ c = c').
    intros Hint.
    revert v r' v' c'.
    induction Hint using interpret_ctx_ind' with (P := R) (P0 := R0); unfold R, R0 in *;
      intros v1 r2 v2 c2 Hint2 Heq1 Heq2; subst;
        (try now inv Hint2; repeat subst_exp; eapply IHHint; [ eassumption | reflexivity | reflexivity ]).
    - inv Hint2. repeat subst_exp.
      eapply bstep_fuel_deterministic in H17; [| clear H17; eassumption ]. destructAll.
      eapply IHHint in H18; eauto. destructAll. split; eauto.
    - inv Heq1.
    - inv Hint2. inv Heq1; eauto. inv H0.
    - inv Heq1.
    - inv Hint2. congruence.
      eapply IHHint in H1; eauto. destructAll. split; eauto.
  Qed.

  Lemma interpret_ctx_fuel_deterministic C rho v c v' c' :
    interpret_ctx_fuel C rho (Res v) c ->
    interpret_ctx_fuel C rho (Res v') c' ->
    v = v' /\ c = c'.
  Proof.
    intros H1 H2; inv H1; inv H2; eauto.
    - congruence.
    - congruence.
    - eapply interpret_ctx_deterministic_aux in H0; [ | clear H0; eassumption | reflexivity | reflexivity ].
      inv H0. eauto.
  Qed.

  Lemma interpret_ctx_deterministic C rho v c v' c' :
    interpret_ctx C rho (Res v) c ->
    interpret_ctx C rho (Res v') c' ->
    v = v' /\ c = c'.
  Proof.
    intros H1 H2.
    eapply interpret_ctx_deterministic_aux; eauto.
  Qed.

  Lemma bstep_fuel_ctx_OOT rho C e c :
    bstep_fuel rho (C |[ e ]|) OOT c ->
    interprable C = true ->
    interpret_ctx_fuel C rho OOT c \/
    exists rho' c1 c2,
      interpret_ctx_fuel C rho (Res rho') c1 /\
      bstep_fuel rho' e OOT c2 /\
      c = (c1 <+> c2).
  Proof.
    revert rho e c. induction C; intros rho e1 c1 Hstep Hi; (try now inv Hi); simpl in Hi.
    - simpl in Hstep. right. eexists. exists <0>. eexists.
      split. econstructor. split; eauto. rewrite plus_zero; eauto.
    - inv Hstep.
      + left. econstructor; [| congruence ]. eassumption.
      + inv H. eapply IHC in H9; eauto. inv H9.
        * left. eapply ctx_step; [ congruence | econstructor; eauto ].
        * destructAll. right. do 3 eexists.
          split; [| split ]; [| eassumption |]. econstructor. congruence. econstructor; eauto.
          rewrite (plus_assoc _ _ x1), (plus_comm (one_ctx _) x1), <- plus_assoc. reflexivity.
    - inv Hstep.
      + left. econstructor; [| congruence ]. eassumption.
      + inv H. eapply IHC in H10; eauto. inv H10.
        * left. eapply ctx_step; [ congruence | econstructor; eauto ].
        * destructAll. right. do 3 eexists.
          split; [| split ]; [| eassumption |]. econstructor. congruence. econstructor; eauto.
          rewrite (plus_assoc _ _ x1), (plus_comm (one_ctx _) x1), <- plus_assoc. reflexivity.          
    - inv Hstep.
      + left. econstructor; [| congruence ]. eassumption.
      + inv H.
    - inv Hstep.
      + left. econstructor; [| congruence ]. eassumption.
      + inv H.
        * eapply IHC in H13. inv H13.
          -- left. eapply ctx_step. congruence. econstructor; eauto.
          -- destructAll. right. do 3 eexists.
             split; [| split ].
             econstructor. congruence. now econstructor; eauto. eassumption.
             rewrite !plus_assoc. f_equal. f_equal. rewrite plus_comm. f_equal.
          -- eassumption.
        * left. eapply ctx_step. congruence. econstructor; eauto.
    - inv Hstep.
      + left. econstructor; [| congruence ]. eassumption.
      + inv H. eapply IHC in H5; eauto. inv H5.
        * left. unfold one_ctx. eapply ctx_step; [ congruence | econstructor; eauto ].
        * destructAll. right. do 3 eexists.
          split; [| split ]; [| eassumption |]. econstructor. congruence. econstructor; eauto.
          rewrite (plus_assoc _ _ x1), (plus_comm (one_ctx _) x1), <- plus_assoc. reflexivity.
  Qed.

  
  
  (** Small step semantics -- Relational definition *)
  (* Zoe : How to write small step for letapp? *)
  Inductive step: state -> state -> Prop :=
  | Step_constr: forall vs rho x t ys e,
      get_list ys rho = Some vs ->
      step (rho, Econstr x t ys e) (M.set x (Vconstr t vs) rho, e)
  | Step_proj: forall vs v rho x t n y e,
      M.get y rho = Some (Vconstr t vs) ->
      nthN vs n = Some v ->
      step (rho, Eproj x t n y e) (M.set x v rho, e)
  | Step_case: forall t vl e' rho y cl,
      M.get y rho = Some (Vconstr t vl) ->
      caseConsistent cenv cl t ->
      findtag cl t = Some e' ->
      step (rho, Ecase y cl) (rho, e')
  | Step_fun: forall rho fl e,
      step (rho, Efun fl e) (def_funs fl fl rho rho, e)
  | Step_app: forall rho' fl f' vs xs e rho'' rho f t ys,
      M.get f rho = Some (Vfun rho' fl f') ->
      get_list ys rho = Some vs ->
      find_def f' fl = Some (t,xs,e) ->
      set_lists xs vs (def_funs fl fl rho' rho') = Some rho'' ->
      step (rho, Eapp f t ys) (rho'', e)
  | Step_prim: forall vs v rho' rho x f f' ys e,
      get_list ys rho = Some vs ->
      M.get f pr = Some f' ->
      f' vs = Some v ->
      M.set x v rho = rho' ->
      step (rho, Eprim x f ys e) (rho', e)
  (* need to go from value to exp somehow ... *)
  (* | Step_halt : forall x v rho, *)
  (*                 M.get x rho = Some v -> *)
  (*                 step (rho, Ehalt x) (rho, v) *).

  (* small-step matches big-step *)


  Inductive halt_state: (env * exp) -> val -> Prop :=
  | Chalt :
      forall rho x v,
        M.get x rho = Some v ->
        halt_state (rho, Ehalt x) v.


  Theorem bstep_step_corresp:
    forall n rho e v rho' e',
      step (rho, e) (rho', e') ->
      bstep_e rho e v n ->
      exists n', bstep_e rho' e' v n'.
  Proof.
    intros. inversion H; subst.
    - inversion H0; subst. exists n.
      rewrite H2 in H9. inv H9; auto.
    - inv H0. rewrite H4 in H11. inv H11.
      rewrite H12 in H6. inv H6.
      exists n; auto.
    - inv H0. rewrite H5 in H3. inv H3.
      rewrite H9 in H7; inv H7.
      exists n; auto.
    - inversion H0; subst. eauto.
    - inv H0. rewrite H5 in H4; inv H4.
      rewrite H11 in H7; inv H7.
      rewrite H6 in H9; inv H9.
      rewrite H8 in H14; inv H14.
      eauto.
    - inv H0. rewrite H5 in H8; inv H8.
      rewrite H6 in H10; inv H10.
      rewrite H13 in H7; inv H7.
      eauto.
  Qed.

  Theorem step_pre_bstep_corresp:
    forall n rho e v rho' e',
      step (rho, e) (rho', e') ->
      bstep_e rho' e' v n ->
      exists n', bstep_e rho e v n'.
  Proof.
    intros. inversion H; subst; try solve [eexists; econstructor; eauto].
  Qed.

  (** Correspondence of the two small step semantics definitions *)
  (*  Lemma sstep_f_complete:
    forall (rho : env) (e : exp) (rho':env) (e':exp),  step (rho,e) (rho', e') -> sstep_f rho e = Ret (rho', e').
  Proof.
    intros rho e rho' e' H;
    inv H; simpl;
    repeat match goal with
             | H: ?A = Some _ |- context [ l_opt ?A] => rewrite H; simpl; clear H
             | H: ?A= _ |- match ?A with _ => _ end = _ => rewrite H
             | [ |- context [(?A =? ?A)%positive]] => rewrite Pos.eqb_refl
           end; auto.
    apply caseConsistent_c in H5. rewrite H5. auto.
  Qed.


  Theorem sstep_f_sound:
    forall (rho : env) (e : exp) (rho':env) (e':exp), sstep_f rho e = Ret (rho', e') -> step (rho,e) (rho', e').
  Proof.
    intros rho e rho' e' H.
    destruct e; simpl in H;
    repeat
      match goal with
        | H: match ?A with _ => _ end = Ret _ |- _ => destruct A eqn:?; inv H
        | H: exceptionMonad.bind ?A _ = Ret _ |- _ => destruct A eqn:?; try (solve [inv H]); simpl in H
        | H: l_opt ?A _ = Ret _ |- _ => destruct A eqn:?; try (solve [inv H]); simpl in H
        | H: Some _ = Some _ |- _ => inv H
        | H: Ret _ = Ret _ |- _ => inv H
        | H : (_ =? _)%positive = true |- _ => apply Peqb_true_eq in H; subst
      end;
    try solve [econstructor; eauto].
    - apply caseConsistent_c in Heqb.
      econstructor; eauto.
    - inv H.
  Qed.


   *)

  (** Reflexive transitive closure of the small-step relation *)
  Definition mstep : relation state := clos_refl_trans_1n state step.

  (** The evalutation semantics is deterministic *)
  Lemma bstep_e_deterministic e rho v1 v2 c1 c2 :
    bstep_e rho e v1 c1 ->
    bstep_e rho e v2 c2 ->
    v1 = v2 /\ c1 = c2.
  Proof.
    intros Heval1 Heval2.
    revert v2 c2 Heval2; induction Heval1; intros v2 c2 Heval2;
      inv Heval2; repeat subst_exp; eauto.
    split; f_equal; eapply IHHeval1; eauto.

    eapply IHHeval1_1 in H15. inv H15.
    eapply IHHeval1_2 in H16. inv H16.
    split; congruence.
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
             end;
      try now (repeat subst_exp; reflexivity).
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

  (* proof of equivalence of small and big step semantics *)
  Lemma bstep_then_mstep:
    forall rho e v n,
      bstep_e rho e v n ->
      exists rho' x,
        mstep (rho, e) (rho', Ehalt x) /\ M.get x rho' = Some v.
  Proof.
    intros. induction H.
    - destruct IHbstep_e. destruct H2. destruct H2.
      exists x0, x1. split. econstructor 2. constructor; eauto. rewrite H0.
      apply H2. auto.
    - destruct IHbstep_e. destruct H2. inv H2. exists x0, x1.
      split. econstructor 2. econstructor; eauto.
      apply H3. auto.
    - destruct IHbstep_e. destruct H3. inv H3. exists x, x0. split.
      econstructor 2. econstructor; eauto. apply H4. auto.
    - destruct IHbstep_e. destruct H4. inv H4.
      exists x, x0. split; auto.
      econstructor 2. econstructor; eauto. auto.
    - admit. (* No case for letapp *)
    - destruct IHbstep_e. destruct H0. destruct H0. exists x, x0.
      split; auto. econstructor 2.
      econstructor; eauto. auto.
    - destruct IHbstep_e. destruct H4. destruct H4.
      exists x0, x1. split; auto.
      econstructor 2. econstructor; eauto. auto.
    - exists rho, x.
      split; auto.
      constructor.
  Abort.

  Lemma mstep_then_bstep:
    forall s s',
      mstep s s' ->
      forall v,
        halt_state s' v ->
        exists n, bstep_e (fst s) (snd s) v n.
  Proof.
    intros s s' H.
    induction H; intros.
    - inv H. exists 0%nat; simpl.
      constructor; auto.
    - apply IHclos_refl_trans_1n in H1.
      destruct H1.
      destruct x; destruct y; simpl in *.
      eapply step_pre_bstep_corresp; eauto.
  Qed.

  Theorem bstep_mstep_equiv:
    forall s v,
      (exists s', mstep s s' /\ halt_state s' v) <-> (exists n, bstep_e (fst s) (snd s) v n).
  Proof.
    intros. split; intros.
    - do 2 (destruct H).
      eapply mstep_then_bstep; eauto.
    - destruct H. destruct s. simpl in H.
      (* apply bstep_then_mstep in H. do 3 (destruct H). *)
      (* exists (x0, Ehalt x1). split; auto. *)
      (* constructor; auto. *)
  Abort.

End EVAL.



Ltac destruct_bstep :=
  match goal with
  | [ H : bstep _ _ _ _ _ |- _ ] => inv H
  end.


(** The following are not used anywhere. They have to do either with "well-typedness"
 * or observable values. We need to go through them to decide if can can throw them
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

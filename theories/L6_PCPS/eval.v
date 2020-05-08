From Coq Require Import NArith.BinNat Relations.Relations MSets.MSets
         MSets.MSetRBT Lists.List omega.Omega Sets.Ensembles
         Relations.Relations.
Import ListNotations.
Require Import Coq.Strings.String.
From CertiCoq.Common Require Import AstCommon exceptionMonad.
From CertiCoq.L6 Require Import cps List_util size_cps ctx cps_util set_util map_util identifiers tactics.
Require Import compcert.lib.Coqlib.



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

  Inductive res : Type := 
  | OOT 
  | Res : val -> res. 

  Definition cost (e : exp) : nat := 
  match e with 
  | Econstr x t ys e => 1 + length ys
  | Eproj x t n y e => 1
  | Ecase y cl => 1
  | Eapp f t ys => 1 + length ys
  | Eletapp x f t ys e => 1 + length ys 
  | Efun B e => 1 + PS.cardinal (fundefs_fv B)
  | Eprim x f ys e => 1 + length ys
  | Ehalt x => 1
  end.

  Inductive bstep :  env -> exp -> res -> nat -> Prop :=
  | BStept_constr :
    forall (x : var) (t : ctor_tag) (ys :list var) (e : exp) 
      (rho rho' : env) (vs : list val) (v : res) (cin : nat),
        get_list ys rho = Some vs ->
        M.set x (Vconstr t vs) rho = rho' ->
        bstep_fuel rho' e v cin ->
        bstep rho (Econstr x t ys e) v cin
  | BStept_proj :
      forall (t : ctor_tag) (vs : list val) 
        (rho : env) (x : var) (n : N) (y : var)
        (e : exp) (v : val) (v' : res) (cin : nat),
          M.get y rho = Some (Vconstr t vs) ->
          nthN vs n = Some v -> 
          bstep_fuel (M.set x v rho) e v' cin ->
          bstep rho (Eproj x t n y e) v' cin
  | BStept_case :
      forall (y : var) (v : res) (e : exp) (t : ctor_tag) (cl : list (ctor_tag * exp))
        (vl : list val) (rho : env) (n cin : nat),
        M.get y rho = Some (Vconstr t vl) ->
        caseConsistent cenv cl t ->
        find_tag_nth cl t e n ->
        bstep_fuel rho e v cin ->
        bstep rho (Ecase y cl) v cin
  | BStept_app :
      forall (rho' : env) (fl : fundefs) (f' : var) (vs : list val) 
        (xs : list var) (e : exp) (rho'' rho : env) (f : var)
        (t : ctor_tag) (ys : list var) (v : res) (cin : nat),
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
        (t : ctor_tag) (ys : list var) (v : val) (v' : res) (cin1 cin2 : nat),
         (* evaluate application *)
          M.get f rho = Some (Vfun rho' fl f') ->
          get_list ys rho = Some vs ->
          find_def f' fl = Some (t,xs,e_body) ->
          set_lists xs vs (def_funs fl fl rho' rho') = Some rho'' ->
          bstep_fuel rho'' e_body (Res v) cin1 -> (* body evaluates to v *)
          (* evaluate let continuation *)
          bstep_fuel (M.set x v rho) e v' cin2 ->
          bstep rho (Eletapp x f t ys e) v' (cin1 + cin2)
  | BStept_letapp_oot :
      forall (rho' : env) (fl : fundefs) (f' : var) (vs : list val)
        (xs : list var) (e_body e : exp) (rho'' rho : env) (x f : var)
        (t : ctor_tag) (ys : list var) (cin : nat),
          M.get f rho = Some (Vfun rho' fl f') ->
          get_list ys rho = Some vs ->
          find_def f' fl = Some (t,xs,e_body) ->
          set_lists xs vs (def_funs fl fl rho' rho') = Some rho'' ->
          bstep_fuel rho'' e_body OOT cin -> (* body times out*)
          bstep rho (Eletapp x f t ys e) OOT cin
  | BStept_fun :
      forall (rho : env) (B : fundefs) (e : exp) (v : res) (cin : nat),
        bstep_fuel (def_funs B B rho rho) e v cin ->
        (* The definition of a function incur cost proportional to the number of FVs
        (to make the bound of the current cc independent of the term) *)
        bstep rho (Efun B e) v cin
  | BStept_prim :
      forall (vs : list val) (rho' rho : env) (x : var) (f : prim) 
        (f' : list val -> option val) (ys : list var) (e : exp)
        (v : val) (v' : res) (cin : nat),
          get_list ys rho = Some vs ->
          M.get f pr = Some f' ->
          f' vs = Some v ->
          M.set x v rho = rho' ->
          bstep_fuel rho' e v' cin ->
          bstep rho (Eprim x f ys e) v' cin
  | BStept_halt :
      forall x v rho,
        M.get x rho = Some v ->
        bstep rho (Ehalt x) (Res v) 0
  with bstep_fuel :  env -> exp -> res -> nat -> Prop :=       
  | BStepf_OOT : (* not enought time units to take astep *)
    forall rho e c, 
      (c < cost e)%nat ->
      bstep_fuel rho e OOT c
  | BStepf_run : (* take a step *)
    forall rho e r cin, 
      (cin >= cost e)%nat ->
      bstep rho e r (cin - cost e) ->
      bstep_fuel rho e r cin.
  
  Scheme bstep_ind' := Minimality for bstep Sort Prop
  with bstep_fuel_ind' := Minimality for bstep_fuel Sort Prop.

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
  - inv Hstep2. eapply IHHstep in H1; eauto. inv H1.
    split; eauto. omega.
Qed. 

Lemma bstep_fuel_deterministic rho e v c v' c' : 
    bstep_fuel rho e (Res v) c -> 
    bstep_fuel rho e (Res v') c' ->
    v = v' /\ c = c'. 
Proof.
  intros H1 H2; inv H1; inv H2; eauto. 
  eapply step_deterministic_aux in H0; [ | eapply H3 | reflexivity | reflexivity ].
  inv H0. split; eauto. omega.
Qed.   

Lemma bstep_deterministic rho e v c v' c' : 
  bstep rho e (Res v) c -> 
  bstep rho e (Res v') c' ->
  v = v' /\ c = c'.
Proof.
  intros H1 H2. eapply step_deterministic_aux; eauto. 
Qed.

  (** * Interpretation of (certain) evaluation contexts as environments *)

  (* TODO move to more appropriate file *)

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

  Ltac subst_exp :=
    match goal with
    | [H1 : ?e = ?e1, H2 : ?e = ?e2 |- _ ] =>
      rewrite H1 in H2; inv H2
    end.
  
  Unset Regular Subst Tactic.

  Lemma bstep_cost_deterministic e rho v1 v2 c1 c2 :
    bstep_cost rho e v1 c1 ->
    bstep_cost rho e v2 c2 ->
    v1 = v2 /\ c1 = c2.
  Proof.
    intros Heval1 Heval2.
    revert v2 c2 Heval2; induction Heval1; intros v2 c2 Heval2;
    inv Heval2; repeat subst_exp; eauto;
      try now edestruct IHHeval1 as [Heq1 Heq2]; eauto.
    + eapply IHHeval1 in H10. inv H10. split; congruence.
    + eapply find_tag_nth_deterministic in H7; eauto; inv H7.
      eapply IHHeval1 in H10. inv H10. split; congruence.
    + eapply IHHeval1 in H13. inv H13. split; congruence.
    + eapply IHHeval1_1 in H15. inv H15.
      eapply IHHeval1_2 in H16. inv H16.
      split; congruence.
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
           end.
    + rewrite H6 in H2.  inversion H2; subst. reflexivity.
    + inv H6. rewrite H8 in H3; inv H3. reflexivity.
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
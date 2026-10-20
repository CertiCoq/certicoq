From Stdlib Require Import ZArith.
Require Import Common.
From CertiRocq Require Import
     LambdaANF.term LambdaANF.term_util LambdaANF.state LambdaANF.eval LambdaANF.shrink_cps
     LambdaANF.inline LambdaANF.uncurry_proto LambdaANF.closure_conversion
     LambdaANF.closure_conversion LambdaANF.hoisting LambdaANF.dead_param_elim LambdaANF.lambda_lifting.
From CertiRocq.LambdaBox_to_LambdaANF Require Import common anf_convert_env.
From CertiRocq.LambdaBox_to_LambdaANF Require anf cps.
(* From CertiRocq.Codegen Require Import LambdaANF_to_Clight. *)

Require Import Common.Common Common.compM Common.Pipeline_utils.
Require Import ExtLib.Structures.Monad.

Import Monads.

Import MonadNotation.

Definition prim_env := M.t primitive.

Definition LambdaANFenv : Type := eval.prims * prim_env * ctor_env * ctor_tag * ind_tag * name_env * fun_env * eval.env.

Definition LambdaANFterm : Type := term.exp.
Definition LambdaANFval : Type := term.val.
Definition LambdaANF_FullTerm : Type := LambdaANFenv * LambdaANFterm.
Definition LambdaBoxEAstTerm : Type := EAst.global_declarations * EAst.term.

Section IDENT.

  Context (next_var : positive).

  Instance LambdaANF_Lang : Lang LambdaANF_FullTerm :=
    { Value := LambdaANFval;
      TermWf := fun p =>
                  let '(_, e) := p in
                  identifiers.closed_exp e /\
                  identifiers.unique_bindings e ;
      BigStep := fun p v =>
                   let '(pr, prims, cenv, ctag, itag, nenv, fenv, rho, e) := p in
                   exists c, bstep_cost pr cenv rho e v c
    }.


  (* starting tags for L5_to_LambdaANF, anything under default is reserved for special
   constructors/types *)
  Definition default_ctor_tag := 99%positive.
  Definition default_ind_tag := 99%positive.
  (* assigned for the constructor and the type of closures *)
  Definition clo_tag := 15%positive.
  Definition clo_ind_tag := 16%positive.
  (* tags for functions and continuations *)
  Definition fun_fun_tag := 3%positive.
  Definition kon_fun_tag := 2%positive.


  Definition make_prim_env (prims : list (primitive * positive)) : prim_env :=
    List.fold_left (fun map '(p, pos) => M.set pos p map) prims (M.empty _).

  Definition compile_LambdaANF_CPS prims : CertiRocqTrans LambdaBoxEAstTerm LambdaANF_FullTerm :=
    fun src =>
      debug_msg "Translating from LambdaBox (EAst) to LambdaANF (CPS)" ;;
      LiftErrorCertiRocqTrans "LambdaANF CPS"
                             (fun (p : LambdaBoxEAstTerm) =>
                                let prim_env := make_prim_env prims in
                                let ie := inductive_env_east (fst p) in
                                match cps.convert_top_cps prim_env fun_fun_tag kon_fun_tag default_ctor_tag default_ind_tag next_var
                                                          prims (fun _ => None) ie (List.rev (fst p)) (snd p) with
                                | (compM.Ret e, data) =>
                                  let (_, ctag, itag, ftag, cenv, fenv, nenv, _, _) := data in
                                  Ret (M.empty _, prim_env, cenv, ctag, itag, nenv, fenv, M.empty _, e)
                                | (compM.Err s, _) => Err s
                                end) src.

  Definition compile_LambdaANF_ANF prims : CertiRocqTrans LambdaBoxEAstTerm LambdaANF_FullTerm :=
    fun src =>
      debug_msg "Translating from LambdaBox (EAst) to LambdaANF (ANF)" ;;
      LiftErrorCertiRocqTrans "LambdaANF ANF"
                             (fun (p : LambdaBoxEAstTerm) =>
                                let prim_env := make_prim_env prims in
                                let ie := inductive_env_east (fst p) in
                                let '(_, _, _, _, dcm) :=
                                  CertiRocq.LambdaBox_to_LambdaANF.common.convert_env default_ctor_tag default_ind_tag ie in
                                match CertiRocq.LambdaBox_to_LambdaANF.anf.convert_top_anf
                                        fun_fun_tag default_ctor_tag prim_env
                                        default_ind_tag next_var dcm
                                        prims (fun _ => None) ie (List.rev (fst p)) (snd p) with
                                | (compM.Ret e, data) =>
                                  let (_, ctag, itag, ftag, cenv, fenv, nenv, _, _) := data in
                                  Ret (M.empty _, prim_env, cenv, ctag, itag, nenv, fenv, M.empty _, e)
                                | (compM.Err s, _) => Err s
                                end) src.

  (** * Definition of LambdaANF backend pipelines *)

  (* Add all names to name env *)
  Definition update_var (names : term_util.name_env) (x : var)
    : term_util.name_env :=
    match M.get x names with
    | Some (nNamed _) => names
    | Some nAnon => M.set x (nNamed "x") names
    | None => M.set x (nNamed "x") names
    end.

  Definition update_vars names xs :=
    List.fold_left update_var xs names.

  (** Adds missing names to name environment for the C translation *)
  Fixpoint add_binders_exp (names : term_util.name_env) (e : exp)
    : name_env :=
    match e with
    | Econstr x _ _ e
    | Eprim_val x _ e
    | Eprim x _ _ e
    | Eletapp x _ _ _ e
    | Eproj x _ _ _ e => add_binders_exp (update_var names x) e
    | Ecase _ pats =>
      List.fold_left (fun names p => add_binders_exp names (snd p)) pats names
    | Eapp _ _ _
    | Ehalt _ => names
    | Efun B e => add_binders_exp (add_binders_fundefs names B) e
    end
  with add_binders_fundefs (names : term_util.name_env) (B : fundefs) : term_util.name_env :=
         match B with
         | Fcons f _ xs e1 B1 =>
           add_binders_fundefs (add_binders_exp (update_vars (update_var names f) xs) e1) B1
         | Fnil => names
         end.

  Definition log_prog (e : exp) (c_data : comp_data) : comp_data :=
    match c_data with
    | mkCompData nv nc ni nf cenv fenv nenv imap log =>
      let msg := cps_show.show_exp nenv cenv false e in
      mkCompData nv nc ni nf cenv fenv nenv imap ("term" :: msg :: log)
    end.


  Record anf_options :=
    { time            : bool;    (* Keep ANF per phase timing *)
      cps             : bool;    (* CPS *)
      do_lambda_lift  : bool;    (* Optimize closure allocation with lambda lifting *)
      args            : nat;     (* Arg threshold for lambda lifting *)
      no_push         : nat;     (* *)
      inl_wrappers    : bool;    (* If true, all known calls to lambda lifted functions are inlined *)
      inl_known       : bool;    (* If true, lambda lifting inlines known calls inside wrappers *)
      inl_before      : bool;    (* Perform shrink/inline loop before closure conversion *)
      inl_after       : bool;    (* Perform shrink/inline loop after closure conversion *)
      dpe             : bool;    (* Turn it off for the top-level theorm because it does not have a proof yet *)
    }.


  Definition anf_state (A : Type) := comp_data -> error A * comp_data.


  Definition anf_trans : Type := exp -> anf_state exp.


  Global Instance MonadState : Monad anf_state :=
    { ret A x := (fun c_data  => (Ret x, c_data));
      bind A B m f :=
        (fun c_data =>
           let (a_err, c_data') := m c_data in
           match a_err with
           | Ret a => f a c_data'
           | Err s => (Err s, c_data')
           end)
    }.


  Definition id_trans : anf_trans := fun e c => (Ret e, c).

  (** Merge alpha-equivalent closed top-level functions, after hoisting. Erasure implements
      every [□] as its own copy of [fix reccall _ := reccall]; this keeps a single copy.
      TODO: prove [merge_dup_funs] correct. *)
  Section MergeDupFuns.

    Local Open Scope bool_scope.

    Definition rn (σ : M.t var) (x : var) : var :=
      match M.get x σ with Some y => y | None => x end.

    Fixpoint rename_exp (σ : M.t var) (e : exp) {struct e} : exp :=
      match e with
      | Econstr x c ys k => Econstr x c (List.map (rn σ) ys) (rename_exp σ k)
      | Ecase x bs => Ecase (rn σ x) (List.map (fun b => (fst b, rename_exp σ (snd b))) bs)
      | Eproj x c n y k => Eproj x c n (rn σ y) (rename_exp σ k)
      | Eletapp x f t ys k => Eletapp x (rn σ f) t (List.map (rn σ) ys) (rename_exp σ k)
      | Efun fds k => Efun (rename_fds σ fds) (rename_exp σ k)
      | Eapp f t ys => Eapp (rn σ f) t (List.map (rn σ) ys)
      | Eprim_val x p k => Eprim_val x p (rename_exp σ k)
      | Eprim x p ys k => Eprim x p (List.map (rn σ) ys) (rename_exp σ k)
      | Ehalt x => Ehalt (rn σ x)
      end
    with rename_fds (σ : M.t var) (fds : fundefs) {struct fds} : fundefs :=
      match fds with
      | Fcons f t xs e fds' => Fcons f t xs (rename_exp σ e) (rename_fds σ fds')
      | Fnil => Fnil
      end.

    (* Alpha-equivalence up to a bijection: [σ] maps left binders to right ones, [ρ] back. *)
    Definition var_eqb (σ ρ : M.t var) (x y : var) : bool :=
      match M.get x σ, M.get y ρ with
      | Some y', Some x' => Pos.eqb y' y && Pos.eqb x' x
      | None, None => Pos.eqb x y
      | _, _ => false
      end.

    Fixpoint vars_eqb (σ ρ : M.t var) (xs ys : list var) : bool :=
      match xs, ys with
      | nil, nil => true
      | x :: xs, y :: ys => var_eqb σ ρ x y && vars_eqb σ ρ xs ys
      | _, _ => false
      end.

    Fixpoint exp_alpha_eqb (σ ρ : M.t var) (e1 e2 : exp) {struct e1} : bool :=
      match e1, e2 with
      | Econstr x1 c1 ys1 k1, Econstr x2 c2 ys2 k2 =>
        Pos.eqb c1 c2 && vars_eqb σ ρ ys1 ys2 &&
        exp_alpha_eqb (M.set x1 x2 σ) (M.set x2 x1 ρ) k1 k2
      | Ecase x1 bs1, Ecase x2 bs2 =>
        var_eqb σ ρ x1 x2 &&
        (fix go (bs1 bs2 : list (ctor_tag * exp)) : bool :=
           match bs1, bs2 with
           | nil, nil => true
           | (c1, b1) :: bs1, (c2, b2) :: bs2 =>
             Pos.eqb c1 c2 && exp_alpha_eqb σ ρ b1 b2 && go bs1 bs2
           | _, _ => false
           end) bs1 bs2
      | Eproj x1 c1 n1 y1 k1, Eproj x2 c2 n2 y2 k2 =>
        Pos.eqb c1 c2 && N.eqb n1 n2 && var_eqb σ ρ y1 y2 &&
        exp_alpha_eqb (M.set x1 x2 σ) (M.set x2 x1 ρ) k1 k2
      | Eletapp x1 f1 t1 ys1 k1, Eletapp x2 f2 t2 ys2 k2 =>
        var_eqb σ ρ f1 f2 && Pos.eqb t1 t2 && vars_eqb σ ρ ys1 ys2 &&
        exp_alpha_eqb (M.set x1 x2 σ) (M.set x2 x1 ρ) k1 k2
      | Eapp f1 t1 ys1, Eapp f2 t2 ys2 =>
        var_eqb σ ρ f1 f2 && Pos.eqb t1 t2 && vars_eqb σ ρ ys1 ys2
      | Eprim x1 p1 ys1 k1, Eprim x2 p2 ys2 k2 =>
        Pos.eqb p1 p2 && vars_eqb σ ρ ys1 ys2 &&
        exp_alpha_eqb (M.set x1 x2 σ) (M.set x2 x1 ρ) k1 k2
      | Ehalt x1, Ehalt x2 => var_eqb σ ρ x1 x2
      | _, _ => false (* [Efun] and [Eprim_val] are conservatively treated as distinct *)
      end.

    Definition fundef : Type := var * fun_tag * list var * exp.

    Fixpoint fds_to_list (fds : fundefs) : list fundef :=
      match fds with
      | Fcons f t xs e fds' => (f, t, xs, e) :: fds_to_list fds'
      | Fnil => nil
      end.

    Fixpoint list_to_fds (l : list fundef) : fundefs :=
      match l with
      | (f, t, xs, e) :: l' => Fcons f t xs e (list_to_fds l')
      | nil => Fnil
      end.

    Fixpoint bind_vars (σ : M.t var) (xs ys : list var) : M.t var :=
      match xs, ys with
      | x :: xs, y :: ys => bind_vars (M.set x y σ) xs ys
      | _, _ => σ
      end.

    (* [f1] can be replaced by [f2] if they have the same tag and arity, and the body of
       [f1], with [f1] renamed to [f2], is alpha-equivalent to the body of [f2]. *)
    Definition fundef_eqb (d1 d2 : fundef) : bool :=
      let '(f1, t1, xs1, e1) := d1 in
      let '(f2, t2, xs2, e2) := d2 in
      Pos.eqb t1 t2 && Nat.eqb (length xs1) (length xs2) &&
      exp_alpha_eqb (bind_vars (M.empty _) xs1 xs2) (bind_vars (M.empty _) xs2 xs1)
                    (rename_exp (M.set f1 f2 (M.empty _)) e1) e2.

    Definition fundef_name (d : fundef) : var := let '(f, _, _, _) := d in f.

    Fixpoint find_dup (d : fundef) (reps : list fundef) : option var :=
      match reps with
      | nil => None
      | r :: reps => if fundef_eqb d r then Some (fundef_name r) else find_dup d reps
      end.

    (* Keep the first function of each equivalence class and map the others to it. *)
    Fixpoint merge_list (l reps : list fundef) (σ : M.t var) : list fundef * M.t var :=
      match l with
      | nil => (List.rev reps, σ)
      | d :: l => match find_dup d reps with
                  | Some g => merge_list l reps (M.set (fundef_name d) g σ)
                  | None => merge_list l (d :: reps) σ
                  end
      end.

    (* Iterate, since merging functions can make the functions that use them identical. *)
    Fixpoint merge_dup_funs (fuel : nat) (e : exp) : exp :=
      match fuel, e with
      | S fuel, Efun fds k =>
        let l := fds_to_list fds in
        let '(reps, σ) := merge_list l nil (M.empty _) in
        if Nat.eqb (length reps) (length l) then e
        else merge_dup_funs fuel (Efun (rename_fds σ (list_to_fds reps)) (rename_exp σ k))
      | _, _ => e
      end.

  End MergeDupFuns.

  Definition merge_dup_funs_trans : anf_trans :=
    fun e c => (Ret (merge_dup_funs 10 e), c).

  Section Pipeline.

    Context (anf_opts : anf_options).

    Definition time_anf {A B} (name : string) (f : A -> anf_state B) : A -> anf_state B :=
      fun x s => if time anf_opts then timePhase name (f x) s else f x s.

    (* Optimizing λANF pipeline *)

    Definition anf_pipeline (e : exp) : anf_state exp :=
      e <- time_anf "Shrink" shrink_err e;;
      e <- time_anf "Uncurry" (uncurry_top (cps anf_opts)) e ;;
      e <- time_anf "Inline uncurry wrappers" (inline_uncurry next_var 10 100) e ;;
      e <- (if inl_before anf_opts then
              time_anf "Inline/shrink loop" (inline_shrink_loop next_var 10 100) e
            else id_trans e) ;;
      e <- (if (do_lambda_lift anf_opts) then
              time_anf "Lambda lift" (lambda_lift (args anf_opts) (no_push anf_opts) (inl_wrappers anf_opts)) e
            else id_trans e) ;;
      e <- time_anf "Shrink" shrink_err e;;
      e <- time_anf "Closure conversion and hoisting" (closure_conversion_hoist clo_tag clo_ind_tag) e ;;
      e <- time_anf "Shrink" shrink_err e;;
      e <- (if inl_after anf_opts then
              time_anf "Inline/shrink loop" (inline_shrink_loop next_var 10 100) e
            else id_trans e) ;;
      e <- (if dpe anf_opts then
              time_anf "Dead param elim" dead_param_elim.DPE e
            else id_trans e) ;;
      e <- time_anf "Shrink" shrink_err e;;
      e <- (if inl_known anf_opts then
              time_anf "Inline known functions inside wrappers" (inline_lifted next_var 10 1000) e
            else id_trans e) ;;
      e <- time_anf "Merge duplicate functions" merge_dup_funs_trans e ;;
      ret e.

      Print LambdaANFenv.


    Definition run_anf_pipeline (t : LambdaANF_FullTerm) : error LambdaANF_FullTerm * string :=
      let '(prims, cenv, ctag, itag, nenv, fenv, _, e0) := t in
      (* make compilation state *)
      let c_data :=
          let next_var :=
              ((identifiers.max_var e0 1) + 1)%positive in
          let next_fun_tag := (M.fold (fun cm => fun ft => fun _ => Pos.max cm ft) fenv 1 + 1)%positive in
          pack_data next_var ctag itag next_fun_tag cenv fenv nenv (M.empty nat) nil
      in
      let (res, c_data') := anf_pipeline e0 c_data in
      match res with
      | compM.Err s =>
        (Err ("Failed compiling LambdaANF program: " ++ s)%bs, "")
      | compM.Ret e =>
        let (_, ctag, itag, ftag, cenv, fenv, nenv, _, log) := c_data' in
        (Ret (prims, cenv, ctag, itag, nenv, fenv, M.empty _, e), log_to_string log)
      end%positive.

  End Pipeline.


  (* ANF/Lambda-lifting variants for measuring performance. Passed through the ANF variant option.

0: (DEFAULT)
   - LL: agressive inlining of wrappers at known call cites (always the known function is called)
   - do not inline  wrappers
   - fvs live across 0 calls
1: Like 0, but conservative inlining
2: Like 0, but inline known calls inside wrappers
3: Like 0, but like across 0 call
4: Like 0, but like across 2 calls
5: Like 0, but like across 10 calls
6: Like 0, but do not perform inline/shrink loop before CC
7: Like 0, but do not perform inline/shrink loop after CC
8: Like 0, but do not perform inline/shrink at all
9: Like 0, but non-selective lambda lifting
   *)

  Open Scope nat.

  Definition make_anf_options (opts : Options) : anf_options :=
    let '(inl_wrappers, inl_known, no_push, inl_before, inl_after) :=
        let default := (true, false, 1, true, true) in
        match anf_variant opts with
        | 0 => default
        | 1 => (false, false, 1, true, true)
        | 2 => (true, true, 1, true, true)
        | 3 => (true, false, 0, true, true)
        | 4 => (true, false, 2, true, true)
        | 5 => (true, false, 10, true, true)
        | 6 => (true, false, 1, false, true)
        | 7 => (true, false, 1, true, false)
        | 8 => (true, false, 1, false, false)
        | 9 => (true, false, 1000, true, true)
        | _ => default
        end
    in
    {| time := Pipeline_utils.time_anf opts;
       cps  := negb (Pipeline_utils.direct opts);
       do_lambda_lift := (1 <=? o_level opts);
       args := if anf_variant opts =? 9 then 1000 else Pipeline_utils.c_args opts;
       no_push := no_push;
       inl_wrappers := inl_wrappers;
       inl_known    := inl_known;
       inl_before   := inl_before;
       inl_after    := inl_after;
       dpe          := true;
    |}.


  Definition compile_LambdaANF : CertiRocqTrans LambdaANF_FullTerm LambdaANF_FullTerm :=
    fun src =>
      debug_msg "Compiling LambdaANF" ;;
      opts <- get_options ;;
      (* Make anf_options *)
      let anf_opts := make_anf_options opts in
      LiftErrorLogCertiRocqTrans "LambdaANF Pipeline" (run_anf_pipeline anf_opts) src.


  Definition compile_LambdaANF_debug : CertiRocqTrans LambdaANF_FullTerm LambdaANF_FullTerm :=
    fun src =>
      debug_msg "Compiling LambdaANF" ;;
      opts <- get_options ;;
      (* Make anf_options *)
      let anf_opts := make_anf_options opts in
      LiftErrorLogCertiRocqTrans "LambdaANF Pipeline" (run_anf_pipeline anf_opts) src.

End IDENT.

Require Import ZArith.
From CertiCoq Require Import
     L6.cps L6.cps_util L6.state L6.eval L6.shrink_cps L6.L4_to_L6_anf L6.L5_to_L6
     L6.beta_contraction L6.uncurry L6.closure_conversion
     L6.closure_conversion L6.hoisting L6.dead_param_elim L6.lambda_lifting.
From CertiCoq Require Import L4.toplevel.
(* From CertiCoq.L7 Require Import L6_to_Clight. *)

Require Import Common.Common Common.compM Common.Pipeline_utils.
Require Import ExtLib.Structures.Monad.

Import Monads.

Import MonadNotation.

Let L6env : Type := prims * ctor_env * ctor_tag * ind_tag * name_env * fun_env * eval.env.
Let L6term : Type := cps.exp.
Let L6val : Type := cps.val.
Let L6_FullTerm : Type := L6env * L6term.

Instance L6_Lang : Lang L6_FullTerm :=
  { Value := L6val;
    TermWf := fun p =>
                let '(_, e) := p in
                identifiers.closed_exp e /\
                identifiers.unique_bindings e ;
    BigStep := fun p v =>
                 let '(pr, cenv, ctag, itag, nenv, fenv, rho, e) := p in
                 exists c, bstep_cost pr cenv rho e v c
  }.


(* starting tags for L5_to_L6, anything under default is reserved for special
   constructors/types *)
Definition default_ctor_tag := 99%positive.
Definition default_ind_tag := 99%positive.
(* assigned for the constructor and the type of closures *)
Definition bogus_closure_tag := 15%positive.
Definition bogus_cloind_tag := 16%positive.
(* tags for functions and continuations *)
Definition fun_fun_tag := 3%positive.
Definition kon_fun_tag := 2%positive.

Definition compile_L6_CPS : CertiCoqTrans L5_FullTerm L6_FullTerm :=
  fun src => 
      debug_msg "Translating from L5 to L6 (CPS)" ;;
      LiftErrorCertiCoqTrans "L6 CPS"
        (fun (p : L5_FullTerm) =>
           match convert_top default_ctor_tag default_ind_tag fun_fun_tag kon_fun_tag p with
           | Some (cenv, nenv, fenv, ctag, itag, e) =>
             Ret (M.empty _, cenv, ctag, itag, nenv, fenv, M.empty _, e)

           | None => Err "Failed translating from L5 to L6"
           end) src.

Definition compile_L6_ANF : CertiCoqTrans toplevel.L4Term L6_FullTerm :=
  fun src => 
      debug_msg "Translating from L4 to L6 (ANF)" ;;
      LiftErrorCertiCoqTrans "L6 ANF"
        (fun (p : toplevel.L4Term) =>
           match convert_top_anf fun_fun_tag default_ctor_tag default_ind_tag p with
           | (state.Ret e, data) =>
              let (_, ctag, itag, ftag, cenv, fenv, nenv, _) := data in
              Ret (M.empty _, cenv, ctag, itag, nenv, fenv, M.empty _, e)
           | (state.Err s, _) => Err s
           end) src.

(** * Definition of L6 backend pipelines *)

(* Add all names to name env *)
Definition update_var (names : cps_util.name_env) (x : var)
  : cps_util.name_env :=
  match M.get x names with
  | Some (nNamed _) => names
  | Some nAnon => M.set x (nNamed "x") names
  | None => M.set x (nNamed "x") names
  end.

Definition update_vars names xs :=
  List.fold_left update_var xs names.

(** Adds missing names to name environment for the C translation *)
Fixpoint add_binders_exp (names : cps_util.name_env) (e : exp)
  : name_env :=
  match e with
  | Econstr x _ _ e
  | Eprim x _ _ e
  | Eletapp x _ _ _ e          
  | Eproj x _ _ _ e => add_binders_exp (update_var names x) e
  | Ecase _ pats =>
    List.fold_left (fun names p => add_binders_exp names (snd p)) pats names
  | Eapp _ _ _
  | Ehalt _ => names
  | Efun B e => add_binders_exp (add_binders_fundefs names B) e
  end
with add_binders_fundefs (names : cps_util.name_env) (B : fundefs) : cps_util.name_env :=
  match B with
  | Fcons f _ xs e1 B1 =>
    add_binders_fundefs (add_binders_exp (update_vars (update_var names f) xs) e1) B1
  | Fnil => names
  end.


(* Optimizing L6 pipeline *)
Definition L6_pipeline  (opt cps : bool) (t : L6_FullTerm) : error L6_FullTerm :=
  let '(prims, cenv, ctag, itag, nenv, fenv, _, e) := t in
  (* make compilation state *)
  let c_data :=
      let next_var := ((identifiers.max_var e 1) + 1)%positive in
      let next_fun_tag := M.fold (fun cm => fun ft => fun _ => Pos.max cm ft) fenv 1 + 1 in
      pack_data next_var ctag itag next_fun_tag cenv fenv nenv nil
  in
  let res : state.error (exp * comp_data):=
      (* uncurring *)
      let '(e_err, s, c_data) := if cps then uncurry_fuel_cps 100 (shrink_cps.shrink_top e) c_data 
                                 else uncurry_fuel_anf 100 (shrink_cps.shrink_top e) c_data in
      (* inlining *)
      e <- e_err ;;
      let (e_err, c_data) := if cps then inline_uncurry e s 10 10 c_data
                             else inline_uncurry_marked_anf e s 10 10 c_data in
      e <- e_err ;;
      (* Shrink reduction *)
      let e := shrink_cps.shrink_top e in
      (* lambda lifting *)
      let (e_rr, c_data) := if opt then lambda_lift e c_data else (state.Ret e, c_data)in
      e <- e_rr ;;
      (* Shrink reduction *)
      let e := shrink_cps.shrink_top e in
      (* Closure conversion *)
      let (e_err, c_data) := closure_conversion.closure_conversion_hoist bogus_closure_tag (* bogus_cloind_tag *) e c_data in
      let '(mkCompData next ctag itag ftag cenv fenv names log) := c_data in
      let c_data :=
          let next_var := ((identifiers.max_var e 1) + 1)%positive in (* ΧΧΧ check why this is needed *)
          pack_data next_var ctag itag ftag (add_closure_tag bogus_closure_tag bogus_cloind_tag cenv) fenv (add_binders_exp names e) log
      in
      e <- e_err ;;
      (* Shrink reduction *)
      let e := shrink_cps.shrink_top e in
      (* Dead parameter elimination *)
      let e := dead_param_elim.eliminate e in
      (* Shrink reduction *)
      let e := shrink_cps.shrink_top e in
      ret (e, c_data)
  in
  match res with
  | state.Err s =>
    Err ("Failed compiling L6 program: " ++ s)%string
  | state.Ret (e, c_data) =>
    let (_, ctag, itag, ftag, cenv, fenv, nenv, log) := c_data in
    Ret (prims, cenv, ctag, itag, nenv, fenv, M.empty _, e) 
  end.

Definition L6_trans : CertiCoqTrans L6_FullTerm L6_FullTerm :=
  fun src => 
    debug_msg "Compiling L6" ;;
    opts <- get_options ;;
    let cps := negb (direct opts) in
    let o := (0 <? (o_level opts))%nat in
    LiftErrorCertiCoqTrans "L6 Pipeline" (L6_pipeline cps o) src.

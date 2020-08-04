Require Import ZArith.
Require Import Common.compM.
From CertiCoq Require Import
     L6.cps L6.cps_util L6.state L6.eval L6.shrink_cps L6.L4_to_L6_anf L6.L5_to_L6
     L6.inline L6.uncurry L6.closure_conversion
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
           | (compM.Ret e, data) =>
              let (_, ctag, itag, ftag, cenv, fenv, nenv, _) := data in
              Ret (M.empty _, cenv, ctag, itag, nenv, fenv, M.empty _, e)
           | (compM.Err s, _) => Err s
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
Definition L6_pipeline  (opt cps : bool) (args : nat) (no_push : nat) (t : L6_FullTerm) : error L6_FullTerm * string :=
  let '(prims, cenv, ctag, itag, nenv, fenv, _, e0) := t in
  (* make compilation state *)
  let c_data :=
      let next_var :=
          ((identifiers.max_var e0 1) + 1)%positive in
      let next_fun_tag := M.fold (fun cm => fun ft => fun _ => Pos.max cm ft) fenv 1 + 1 in
      pack_data next_var ctag itag next_fun_tag cenv fenv nenv nil
  in
  let res : error (exp * comp_data):=
      (* uncurring *)
      let '(e_err1, s, c_data) := uncurry_fuel cps 100 (fst (shrink_cps.shrink_top e0)) c_data in
      (* inlining *)
      e1 <- e_err1 ;;
      let (e_err2, c_data) := if cps then inline_uncurry e1 s 10 10 c_data true 
                              else inline_uncurry_marked_anf e1 s 10 10 c_data true in
      e2 <- e_err2 ;;
      (* Shrink reduction *)
      let (e3, _) := shrink_cps.shrink_top e2 in
      (* lambda lifting *)
      let (e_rr4, c_data) := if opt then lambda_lift e3 args no_push c_data else (compM.Ret e3, c_data) in
      e4 <- e_rr4 ;;
      (* Shrink reduction *)
      let (e5, _) := shrink_cps.shrink_top e4 in
      (* Closure conversion *)
      let (e_err5, c_data) := closure_conversion.closure_conversion_hoist bogus_closure_tag (* bogus_cloind_tag *) e5 c_data in
      let '(mkCompData next ctag itag ftag cenv fenv names log) := c_data in
      e5 <- e_err5 ;;
      let c_data :=
          let next_var := ((identifiers.max_var e5 1) + 1)%positive in (* ΧΧΧ check why this is needed *)
          pack_data next_var ctag itag ftag (add_closure_tag bogus_closure_tag bogus_cloind_tag cenv) fenv (add_binders_exp names e5) log
      in
      (* Shrink reduction *)
      let (e6, _) := shrink_cps.shrink_top e5 in
      (* Dead parameter elimination *)
      let (e_err7, c_data) := dead_param_elim.eliminate e6 c_data in
      e7 <- e_err7 ;;
      (* Shrink reduction *)
      let (e8, _) := shrink_cps.shrink_top e7 in
      ret (e8, c_data)
  in
  match res with
  | compM.Err s =>
    (Err ("Failed compiling L6 program: " ++ s)%string, "")
  | compM.Ret (e, c_data) =>
    let (_, ctag, itag, ftag, cenv, fenv, nenv, log) := c_data in
    (Ret (prims, cenv, ctag, itag, nenv, fenv, M.empty _, e), log_to_string log)
  end.

Definition L6_trans : CertiCoqTrans L6_FullTerm L6_FullTerm :=
  fun src => 
    debug_msg "Compiling L6" ;;
    opts <- get_options ;;
    let cps := negb (direct opts) in
    let args := fv_args opts in
    let no_push := dev opts in (* temporarily use dev for the number of times a var can be pushed on the shadow stack *)
    let o := (0 <? (o_level opts))%nat in
    LiftErrorLogCertiCoqTrans "L6 Pipeline" (L6_pipeline o cps args no_push) src.

(* 
Require Import Common.Pipeline_utils Common.compM Common.
Require Import L1g.toplevel.
Require Import L2k.toplevel.
Require Import L4.toplevel.
Require Import L6.toplevel L6.cps_show L6.state Compiler.pipeline maps_util.
Require Import ExtLib.Structures.Monad Strings.String.

Import MonadNotation.
Open Scope monad_scope.

Open Scope Z_scope.
Require Import ZArith.


Definition debug_ANF (p : Template.Ast.program) :=
  p <- compile_L1g p ;;
  p <- compile_L2k p ;;
  p <- compile_L2k_eta p ;;
  p <- compile_L4 p ;;
  p <- compile_L6_ANF p ;;
  L6_trans p.

Definition compile_L6_ANF_show (e: Template.Ast.program) : string  :=
  match run_pipeline _ _ default_opts e debug_ANF with
  | (compM.Ret (pr, cenv, vtag, itag, nenv, fenv, rho, term), _) =>
    cps_show.show_exp nenv cenv false term
  | (compM.Err s, _) => s
  end.

Fixpoint loop_add n (f : Datatypes.unit -> nat) : nat :=
  match n with
  | 0%nat => f tt
  | S n => f tt + loop_add n f
  end.


Require Import List.
Import ListNotations.

Definition clos_loop (u : Datatypes.unit) : nat :=
  ((fix list_add k1 k2 k3 l : nat :=
      match l with
      | [] => 0%nat
      | x::xs =>
       let clos z := (k1 + k2 + k3 + z)%nat in
       ((clos x) + list_add k1 k2 k3 xs)%nat
      end) 0 0 0 (List.repeat 0 (100*10)))%nat.

(* Quote Recursively Definition clos := (loop_add (1%nat) clos_loop). *)

(* Definition demo1_ANF := Eval native_compute in (compile_L6_ANF_show clos). *)

*) 

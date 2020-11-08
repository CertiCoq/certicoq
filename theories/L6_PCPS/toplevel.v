Require Import ZArith.
Require Import Common.compM.
From CertiCoq Require Import
     L6.cps L6.cps_util L6.state L6.eval L6.shrink_cps L6.L4_to_L6_anf L6.L4_to_L6
     L6.inline L6.uncurry_proto L6.closure_conversion
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
Definition clo_tag := 15%positive.
Definition clo_ind_tag := 16%positive.
(* tags for functions and continuations *)
Definition fun_fun_tag := 3%positive.
Definition kon_fun_tag := 2%positive.

(* First available variable to use *)
(* TODO make param in ANF/CPS translations *)
Definition next_var := 103%positive.

Definition compile_L6_CPS : CertiCoqTrans toplevel.L4Term L6_FullTerm :=
  fun src => 
      debug_msg "Translating from L4 to L6 (CPS)" ;;
      LiftErrorCertiCoqTrans "L6 CPS"
        (fun (p : toplevel.L4Term) =>
           match L4_to_L6.convert_top fun_fun_tag kon_fun_tag default_ctor_tag default_ind_tag p with
           | Some (cenv, nenv, fenv, ctag, itag, e) => 
             (* (compM.Ret e, data) => *)
             Ret (M.empty _, cenv, ctag, itag, nenv, fenv, M.empty _, e)
           | None => Err "Error when compiling from L4 to L6"
           end) src.

Definition compile_L6_ANF : CertiCoqTrans toplevel.L4Term L6_FullTerm :=
  fun src => 
      debug_msg "Translating from L4 to L6 (ANF)" ;;
      LiftErrorCertiCoqTrans "L6 ANF"
        (fun (p : toplevel.L4Term) =>
           match convert_top_anf fun_fun_tag default_ctor_tag default_ind_tag p with
           | (compM.Ret e, data) =>
              let (_, ctag, itag, ftag, cenv, fenv, nenv, _, _) := data in
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

  Definition log_prog (e : exp) (c_data : comp_data) : comp_data :=
  match c_data with
  | mkCompData nv nc ni nf cenv fenv nenv imap log =>
    let msg := cps_show.show_exp nenv cenv false e in
    mkCompData nv nc ni nf cenv fenv nenv imap ("term" :: msg :: log)      
  end.


  Record anf_options :=
    { time            : bool;    (* Keep ANF per phase timing *)
      cps             : bool;    (* CPS *)
      do_lambda_lift  : bool;    (* Do lambda lifting *)
      args            : nat;     (* Arg threshold for lambda lifting *)
      no_push         : nat;     (* *)
      inl_wrappers    : bool;    (* If true, all known calls to lambda lifted functions are inlined *)
      inl_known       : bool;    (* If true, lambda lifting inlines known calls inside wrappers *)
      inl_before      : bool;    (* Perform shrink/inline loop before closure conversion *)
      inl_after       : bool;    (* Perform shrink/inline loop after closure conversion *)
      dead_param_elim : bool;    (* Turn it off for the top-level theorm because it does not have a proof yet *)
    }.


  Definition anf_trans : Type := exp -> comp_data -> error exp * comp_data. 


  Definition anf_state (A : Type) := comp_data -> error A * comp_data.

    
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
  
  Section Pipeline.

    Context (anf_opts : anf_options).

    Definition time_anf {A B} (name : string) (f : A -> B) : A -> B :=
      if time anf_opts then
        timePhase name f
      else
        f.    


    Definition update_c_data : anf_trans :=
      fun e c =>
        let c_data :=
            let '(mkCompData next ctag itag ftag cenv fenv names imap log) := c in
            let cc_var := ((identifiers.max_var e 1) + 1)%positive in (* ΧΧΧ check why this is needed *)
            pack_data cc_var ctag itag ftag (add_closure_tag clo_tag clo_ind_tag cenv) fenv (add_binders_exp names e) imap log
        in
        (Ret e, c_data). 
    
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
      (* Update the names map. TODO find which transformation does not register all names and remove that. *)
      (* e <- update_c_data e ;;  *)
      e <- time_anf "Shrink" shrink_err e;;
      e <- (if inl_after anf_opts then
              time_anf "Inline/shrink loop" (inline_shrink_loop next_var 10 100) e
            else id_trans e) ;;
      e <- (if dead_param_elim anf_opts then
              time_anf "Dead param elim" dead_param_elim.eliminate e
            else id_trans e) ;;
      e <- time_anf "Shrink" shrink_err e;;
      e <- (if inl_known anf_opts then
              time_anf "Inline known functions inside wrappers" (inline_lifted next_var 10 1000) e
            else id_trans e) ;;
      ret e. 


    Definition run_anf_pipeline (t : L6_FullTerm) : error L6_FullTerm * string :=
      let '(prims, cenv, ctag, itag, nenv, fenv, _, e0) := t in
      (* make compilation state *)
      let c_data :=
          let next_var :=
              ((identifiers.max_var e0 1) + 1)%positive in
          let next_fun_tag := M.fold (fun cm => fun ft => fun _ => Pos.max cm ft) fenv 1 + 1 in
          pack_data next_var ctag itag next_fun_tag cenv fenv nenv (M.empty nat) nil
      in
      let (res, c_data') := anf_pipeline e0 c_data in
      match res with
      | compM.Err s =>
        (Err ("Failed compiling L6 program: " ++ s)%string, "")
      | compM.Ret e =>
        let (_, ctag, itag, ftag, cenv, fenv, nenv, _, log) := c_data' in
        (Ret (prims, cenv, ctag, itag, nenv, fenv, M.empty _, e), log_to_string log)
      end.
    
(* The old L6 pipeline. Don't delete yet.

    (* Optimizing L6 pipeline *)
    Definition L6_pipeline               
               (t : L6_FullTerm) : error L6_FullTerm * string :=
      let '(prims, cenv, ctag, itag, nenv, fenv, _, e0) := t in
      (* make compilation state *)
      let c_data :=
          let next_var :=
              ((identifiers.max_var e0 1) + 1)%positive in
          let next_fun_tag := M.fold (fun cm => fun ft => fun _ => Pos.max cm ft) fenv 1 + 1 in
          pack_data next_var ctag itag next_fun_tag cenv fenv nenv nil
      in
      let res : error (exp * comp_data):=
          (* Apply ANF transformations *)
          (* Shrink reduction *)
          let (e, _) := time_anf "Shrink" (fun _ => shrink_cps.shrink_top e0) in
          (* Uncurring *)
          let '(e_err, s, c_data) := time_anf "Uncurry" (fun _ => uncurry_fuel cps 100 e c_data) in
          e <- e_err ;;
          (* Inlining *)
          let (e_err, c_data) := time_anf "Inline uncurry wrappers" (fun _ => inline_uncurry next_var e s 10 100 c_data) in
          e <- e_err ;;
          (* Inline small functions *) 
          let (e_err, c_data) := if inl_before then time_anf "Inline/shrink loop" (fun _ => inline_small next_var e s 10 100 c_data) else (compM.Ret e, c_data) in
          e <- e_err ;;
          (* Shrink reduction *)
          let (e, _) := time_anf "Shrink" (fun _ => shrink_cps.shrink_top e) in
          (* lambda lifting *)
          let (e_rr, c_data) := if ((opt =? 1)%nat)%bool then
                                  time_anf "Lambda lift" (fun _ => lambda_lift e args no_push inl_wrappers c_data) 
                                else (compM.Ret e, c_data) in
          e <- e_rr ;;
          (* Shrink reduction *)
          let (e, _) := if (opt =? 1)%nat then time_anf "Shrink" (fun _ => shrink_cps.shrink_top e) else (e, 0%nat)  in
          (* Closure conversion *)
          let (e_err, c_data) := time_anf "Closure conversion and hoisting"
                                          (fun _ => hoisting.closure_conversion_hoist bogus_closure_tag (* bogus_cloind_tag *) e c_data) in
          let '(mkCompData next ctag itag ftag cenv fenv names log) := c_data in
          e <- e_err ;;
          let c_data :=
              let cc_var := ((identifiers.max_var e 1) + 1)%positive in (* ΧΧΧ check why this is needed *)
              pack_data cc_var ctag itag ftag (add_closure_tag bogus_closure_tag bogus_cloind_tag cenv) fenv (add_binders_exp names e) log
          in
          (* Shrink reduction *)
          let (e, _) := time_anf "Shrink" (fun _ => shrink_cps.shrink_top e) in
          (* Shrink reduction *)
          let (e, _) := if (opt =? 2)%nat then time_anf "Shrink" (fun _ => shrink_cps.shrink_top e) else (e, 0%nat) in
          (* Dead parameter elimination *)
          let (e_err, c_data) := time_anf "Dead param elim" (fun _ => dead_param_elim.eliminate e c_data) in
          e <- e_err ;;
          (* Shrink reduction *)
          let (e, _) := time_anf "Shrink" (fun _ => shrink_cps.shrink_top e) in
          (* Inline small functions *) 
          let (e_err, c_data) := if inl_after then time_anf "Inline/shrink loop" (fun _ => inline_small next_var e s 10 100 c_data) else (compM.Ret e, c_data) in
          e <- e_err ;;
          (* Inline in wrapper functions *)
          let (e_err, c_data) := if inl_known then
                                   let (e, _) := time_anf "Shrink" (fun _ => shrink_cps.shrink_top e) in
                                   time_anf "Inline known functions inside wrappers" (fun _ => inline_lifted next_var e s 10 1000 c_data)
                                 else (compM.Ret e, c_data) in
          e <- e_err ;;

          ret (e, c_data)
      in
      match res with
      | compM.Err s =>
        (Err ("Failed compiling L6 program: " ++ s)%string, "")
      | compM.Ret (e, c_data) =>
        let (_, ctag, itag, ftag, cenv, fenv, nenv, log) := c_data in
        (Ret (prims, cenv, ctag, itag, nenv, fenv, M.empty _, e), log_to_string log)
      end.



    (* Just for debugging *)
    Definition L6_pipeline_print (t : L6_FullTerm) : error L6_FullTerm * string :=
      let '(prims, cenv, ctag, itag, nenv, fenv, _, e0) := t in
      (* make compilation state *)
      let c_data :=
          let next_var :=
              ((identifiers.max_var e0 1) + 1)%positive in
          let next_fun_tag := M.fold (fun cm => fun ft => fun _ => Pos.max cm ft) fenv 1 + 1 in
          pack_data next_var ctag itag next_fun_tag cenv fenv nenv (M.empty _) nil
      in
      let res : error (exp * comp_data):=
          (* Apply ANF transformations *)
          (* Shrink reduction *)
          let (e, _) := time_anf "Shrink" (fun _ => shrink_cps.shrink_top e0) in
          (* Uncurring *)
          let '(e_err, c_data) := time_anf "Uncurry" (fun _ => uncurry_top cps e c_data) in
          (* let '(e_err, s, c_data) := time_anf "Uncurry" (fun _ => uncurry_fuel cps 100 e c_data) in *)
          e <- e_err ;;
          (* Inlining *)
          let (e_err, c_data) := time_anf "Inline uncurry wrappers" (fun _ => inline_uncurry next_var 10 100 e c_data) in
          e <- e_err ;;
          (* Inline small functions *) 
          let (e_err, c_data) := time_anf "Inline/shrink loop" (fun _ => inline_shrink_loop next_var 10 100 e c_data) in
          e <- e_err ;;
          (* Shrink reduction *)
          let (e, _) := time_anf "Shrink" (fun _ => shrink_cps.shrink_top e) in
          (* lambda lifting *)
          let (e_rr, c_data) := if ((opt =? 1)%nat)%bool then
                                  time_anf "Lambda lift" (fun _ => lambda_lift args no_push inl_wrappers e c_data) 
                                else (compM.Ret e, c_data) in

          ret (e, c_data)
      in
      match res with
      | compM.Err s =>
        (Err ("Failed compiling L6 program: " ++ s)%string, "")
      | compM.Ret (e, c_data) =>
        let (_, ctag, itag, ftag, cenv, fenv, nenv, _, log) := c_data in
        (Ret (prims, cenv, ctag, itag, nenv, fenv, M.empty _, e), log_to_string log)
      end.
*)
    
End Pipeline.


(* ANF/Lambda-lifting Configurations for measuring performance. Passed through the anf_conf flag.

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
 *)

Open Scope nat.
  
Definition make_anf_options (opts : Options) : anf_options :=
  let '(inl_wrappers, inl_known, no_push, inl_before, inl_after) :=
      let default := (true, false, 1, true, true) in 
      match anf_conf opts with
      | 0 => default
      | 1 => (false, false, 1, true, true)
      | 2 => (true, true, 1, true, true)
      | 3 => (true, false, 0, true, true)
      | 4 => (true, false, 2, true, true)
      | 5 => (true, false, 10, true, true)
      | 6 => (true, false, 1, false, true)
      | 7 => (true, false, 1, true, false)
      | 8 => (true, false, 1, false, false)
      | _ => default
      end
  in
  {| time := Pipeline_utils.time opts;
     cps  := negb (Pipeline_utils.direct opts);
     do_lambda_lift := (1 <=? o_level opts);
     args := Pipeline_utils.c_args opts;
     no_push := no_push; 
     inl_wrappers := inl_wrappers;
     inl_known    := inl_known;
     inl_before   := inl_before;
     inl_after    := inl_after;
     dead_param_elim := true;
  |}.


Definition compile_L6 : CertiCoqTrans L6_FullTerm L6_FullTerm :=
  fun src => 
    debug_msg "Compiling L6" ;;
    opts <- get_options ;;
    (* Make anf_options *)
    let anf_opts := make_anf_options opts in
    LiftErrorLogCertiCoqTrans "L6 Pipeline" (run_anf_pipeline anf_opts) src.


Definition compile_L6_debug : CertiCoqTrans L6_FullTerm L6_FullTerm :=
  fun src =>
    debug_msg "Compiling L6" ;;
    opts <- get_options ;;
    (* Make anf_options *)
    let anf_opts := make_anf_options opts in
    LiftErrorLogCertiCoqTrans "L6 Pipeline" (run_anf_pipeline anf_opts) src.

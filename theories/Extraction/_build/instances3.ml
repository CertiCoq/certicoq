open BinPos
open Datatypes
open L3_to_L4
open L5_to_L6
open Beta_contraction
open CertiClasses
open CertiClasses2
open Closure_conversion2
open Cps
open Cps_util
open Dead_param_elim
open Eval
open ExceptionMonad
open Identifiers
open Instances2
open Lambda_lifting
open Shrink_cps
open State
open Uncurry

type coq_L6env = ((prims * cEnv) * nEnv) * fEnv

type coq_L6term = env * exp

type coq_L6val = coq_val

(** val default_cTag : int **)

let default_cTag =
  (fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
    ((fun p->1+2*p) 1)))))

(** val default_iTag : int **)

let default_iTag =
  (fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
    ((fun p->1+2*p) 1)))))

(** val bogus_cloTag : int **)

let bogus_cloTag =
  (fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) 1))

(** val bogus_cloiTag : int **)

let bogus_cloiTag =
  (fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1)))

(** val fun_fTag : int **)

let fun_fTag =
  (fun p->1+2*p) 1

(** val kon_fTag : int **)

let kon_fTag =
  (fun p->2*p) 1

(** val coq_L6_pipeline :
    (L3_to_L4.ienv * coq_L5Term, L3_to_L4.ienv * coq_L5Term) cTerm ->
    (coq_L6env * coq_L6term, coq_L6val) cTerm coq_exception **)

let coq_L6_pipeline e =
  match convert_top default_cTag default_iTag fun_fTag kon_fTag e with
  | Some r ->
    let (p, e0) = r in
    let (p0, next_iTag) = p in
    let (p1, next_cTag) = p0 in
    let (p2, f_env) = p1 in
    let (c_env, n_env) = p2 in
    let c_data =
      let next_var = Pos.add (max_var e0 1) 1 in
      let next_fTag =
        Pos.add (M.fold (fun cm ft _ -> Pos.max cm ft) f_env 1) 1
      in
      pack_data next_var next_cTag next_iTag next_fTag c_env f_env n_env []
    in
    let (p3, c_data0) =
      uncurry_fuel (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S
        O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
        (shrink_top e0) c_data
    in
    let (e1, s) = p3 in
    let (e2, c_data1) =
      inline_uncurry e1 s (S (S (S (S (S (S (S (S (S (S O)))))))))) (S (S (S
        (S (S (S (S (S (S (S O)))))))))) c_data0
    in
    let e3 = shrink_top e2 in
    let e4 = shrink_top e3 in
    let (e5, c_data2) =
      closure_conversion_hoist bogus_cloTag bogus_cloiTag e4 c_data1
    in
    let e6 = shrink_top e5 in
    let e7 = eliminate e6 in
    let e8 = shrink_top e7 in
    Ret ((((M.empty, c_data2.cenv), c_data2.name_env), c_data2.fenv),
    (M.empty, (shrink_top e8)))
  | None ->
    Exc
      ('f'::('a'::('i'::('l'::('e'::('d'::(' '::('c'::('o'::('n'::('v'::('e'::('r'::('t'::('i'::('n'::('g'::(' '::('f'::('r'::('o'::('m'::(' '::('L'::('5'::(' '::('t'::('o'::(' '::('L'::('6'::[])))))))))))))))))))))))))))))))

(** val coq_L6_pipeline_opt :
    (L3_to_L4.ienv * coq_L5Term, L3_to_L4.ienv * coq_L5Term) cTerm ->
    (coq_L6env * coq_L6term, coq_L6val) cTerm coq_exception **)

let coq_L6_pipeline_opt e =
  match convert_top default_cTag default_iTag fun_fTag kon_fTag e with
  | Some r ->
    let (p, e0) = r in
    let (p0, next_iTag) = p in
    let (p1, next_cTag) = p0 in
    let (p2, f_env) = p1 in
    let (c_env, n_env) = p2 in
    let c_data =
      let next_var = Pos.add (max_var e0 1) 1 in
      let next_fTag =
        Pos.add (M.fold (fun cm ft _ -> Pos.max cm ft) f_env 1) 1
      in
      pack_data next_var next_cTag next_iTag next_fTag c_env f_env n_env []
    in
    let (p3, c_data0) =
      uncurry_fuel (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S
        O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
        (shrink_top e0) c_data
    in
    let (e1, s) = p3 in
    let (e2, c_data1) =
      inline_uncurry e1 s (S (S (S (S (S (S (S (S (S (S O)))))))))) (S (S (S
        (S (S (S (S (S (S (S O)))))))))) c_data0
    in
    let e3 = shrink_top e2 in
    let (e4, c_data2) = lambda_lift' e3 c_data1 in
    let e5 = shrink_top e4 in
    let (e6, c_data3) =
      closure_conversion_hoist bogus_cloTag bogus_cloiTag e5 c_data2
    in
    let e7 = shrink_top e6 in
    let e8 = eliminate e7 in
    let e9 = shrink_top e8 in
    Ret ((((M.empty, c_data3.cenv), c_data3.name_env), c_data3.fenv),
    (M.empty, (shrink_top e9)))
  | None ->
    Exc
      ('f'::('a'::('i'::('l'::('e'::('d'::(' '::('c'::('o'::('n'::('v'::('e'::('r'::('t'::('i'::('n'::('g'::(' '::('f'::('r'::('o'::('m'::(' '::('L'::('5'::(' '::('t'::('o'::(' '::('L'::('6'::[])))))))))))))))))))))))))))))))

(** val certiL5_t0_L6 :
    ((L3_to_L4.ienv * coq_L5Term, L3_to_L4.ienv * coq_L5Term) cTerm,
    (coq_L6env * coq_L6term, coq_L6val) cTerm) coq_CerticoqTranslation **)

let certiL5_t0_L6 = function
| O -> coq_L6_pipeline
| S _ -> coq_L6_pipeline_opt

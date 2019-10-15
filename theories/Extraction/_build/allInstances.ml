open Ast0
open BasicAst
open Clight
open Datatypes
open L6_to_Clight
open CertiClasses
open CertiClasses2
open Cps
open Cps_util
open ExceptionMonad
open Instances0
open Instances1
open Instances2
open Instances3
open Utils

(** val argsIdent : int **)

let argsIdent =
  (fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p) 1)))

(** val allocIdent : int **)

let allocIdent =
  (fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p) 1)))

(** val limitIdent : int **)

let limitIdent =
  (fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p) 1)))

(** val gcIdent : int **)

let gcIdent =
  (fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p)
    ((fun p->2*p) 1)))))

(** val mainIdent : int **)

let mainIdent =
  (fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p)
    ((fun p->2*p) 1)))))

(** val bodyIdent : int **)

let bodyIdent =
  (fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p)
    ((fun p->2*p) 1)))))

(** val threadInfIdent : int **)

let threadInfIdent =
  (fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) 1)))

(** val tinfIdent : int **)

let tinfIdent =
  (fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p)
    ((fun p->1+2*p) ((fun p->2*p) 1)))))

(** val heapInfIdent : int **)

let heapInfIdent =
  (fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p)
    ((fun p->1+2*p) ((fun p->2*p) 1)))))

(** val numArgsIdent : int **)

let numArgsIdent =
  (fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
    ((fun p->1+2*p) 1)))))

(** val isptrIdent : int **)

let isptrIdent =
  (fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p)
    ((fun p->2*p) 1)))))

(** val caseIdent : int **)

let caseIdent =
  (fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p)
    ((fun p->2*p) 1)))))

(** val compile_L7 :
    (coq_L6env * coq_L6term, coq_L6val) cTerm -> (nEnv * program) * program **)

let compile_L7 = function
| (l, l0) ->
  let (p, _) = l in
  let (p0, nenv) = p in
  let (_, cenv) = p0 in
  let (_, prog) = l0 in
  let p1 =
    compile argsIdent allocIdent limitIdent gcIdent mainIdent bodyIdent
      threadInfIdent tinfIdent heapInfIdent numArgsIdent isptrIdent caseIdent
      prog cenv nenv
  in
  (((fst (fst p1)), (stripOption mainIdent (snd (fst p1)))),
  (stripOption mainIdent (snd p1)))

(** val compile_opt_L7 :
    (coq_L6env * coq_L6term, coq_L6val) cTerm coq_exception ->
    ((nEnv * program) * program) coq_exception **)

let compile_opt_L7 = function
| Exc s -> Exc s
| Ret p0 -> Ret (compile_L7 p0)

(** val compile_template_L7 :
    coq_Fuel -> nat -> Ast0.program -> ((nEnv * program) * program)
    coq_exception **)

let compile_template_L7 f opt_level p =
  compile_opt_L7
    (translateTo f
      (composeTranslation (liftTotal certiL2_to_L2k)
        (composeTranslation certiL3_to_L3_eta
          (composeTranslation certiL3_eta_to_L4
            (composeTranslation (liftTotal certiL4_to_L4_2)
              (composeTranslation (liftTotal certiL4_2_to_L4_5)
                (composeTranslation (liftTotal certiL4_5_to_L5) certiL5_t0_L6))))))
      opt_level p)

(** val printProg : (name M.t * program) -> char list -> unit **)

let printProg prog file =
  print_Clight_dest_names (snd prog) (M.elements (fst prog)) file

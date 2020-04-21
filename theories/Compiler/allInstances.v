Require Export Common.certiClasses.
Require Export Common.certiClasses2.
Require Export L1g.instances.
Require Export L2k.instances.
Require Export L4.instances.
Require Export L6.instances L6.cps_util L6.cps L6.cps_show L6.tactics.
(* Require Export L7.Clightexec. *)
Require Import L6_to_Clight L6_to_Clight_stack.
Require Import compcert.lib.Maps.
Require Import ZArith.
Require Import Common.Common.
Require Import String.
Require Import  maps_util.

Open Scope Z_scope.
Open Scope string_scope.

From MetaCoq.Template Require Import All.

(* Zoe : TODO these are very verbose and L6 specific so move it there. Generally this file needs massive cleanup. *)
Require Import L6_to_Clight.
(* Require Import Clightexec.*)
Require Import compcert.lib.Maps.

Definition compile_L7' n (t : cTerm certiL6) : exception (cps_util.name_env * Clight.program * Clight.program) :=
  let '((_, cenv , nenv, fenv), (_, prog)) := t in
  let p := L6_to_Clight.compile argsIdent allocIdent limitIdent gcIdent mainIdent bodyIdent threadInfIdent tinfIdent heapInfIdent numArgsIdent isptrIdent caseIdent
                                n prog cenv nenv in
  match p with
  | Ret p =>
    Ret (fst (fst p), stripOption mainIdent (snd (fst p)), stripOption mainIdent (snd p))
  | Exc s => Exc s
  end.

Definition compile_L7_fast' n (t : cTerm certiL6) : cps_util.name_env * Clight.program * Clight.program :=
  let '((_, cenv , nenv, fenv), (_, prog)) := t in
  let p := compile_fast argsIdent allocIdent limitIdent gcIdent mainIdent bodyIdent threadInfIdent tinfIdent heapInfIdent numArgsIdent isptrIdent caseIdent n prog cenv nenv in
  (fst (fst p), stripOption mainIdent (snd (fst p)), stripOption mainIdent (snd p)).


Definition compile_L7_anf (t : cTerm certiL6) : cps_util.name_env * Clight.program * Clight.program :=
  let '((_, cenv , nenv, fenv), (_, prog)) := t in
  let p := L6_to_Clight_stack.compile
             argsIdent allocIdent limitIdent gcIdent mainIdent bodyIdent threadInfIdent tinfIdent heapInfIdent numArgsIdent isptrIdent caseIdent
             5
             stackframeTIdent frameIdent rootIdent spIdent fpIdent nextFld rootIdent prevFld
             false
             prog cenv nenv in
  (fst (fst p), stripOption mainIdent (snd (fst p)), stripOption mainIdent (snd p)).

Definition compile_L7 o (t : cTerm certiL6) : exception (cps_util.name_env * Clight.program * Clight.program) :=
  let '((_, cenv , nenv, fenv), (_, prog)) := t in
  match o with
  | Flag 0 => compile_L7' 5 t
  | Flag 1 => compile_L7' 5 t
  | Flag 2 =>  compile_L7' 5 t
  | Flag 3 => compile_L7' 0 t
  | Flag 4 => Ret (compile_L7_fast' 0 t)
  | Flag 5 => compile_L7' 5 t
  | Flag 6 => compile_L7' 11 t
  | Flag 7 => Ret (compile_L7_fast' 11 t)
  | Flag 8 => compile_L7' 0 t
  | Flag 9 => Ret (compile_L7_fast' 0 t)
  | Flag 10 => compile_L7' 0 t
  | _ => compile_L7' 5 t
  end.

Definition compile_opt_L7 o p :=
  match p with
  | Ret p => compile_L7 o p
  | Exc s => Exc s
  end.

Definition compile_template_L4 (p : Template.Ast.program) : exception (cTerm certiL4) :=
  translateTo (cTerm certiL4) (Flag 0) p.

Definition compile_template_L7 (opt_level : nat) (p : Template.Ast.program)
  : exception (cps_util.name_env * Clight.program * Clight.program)  :=
  compile_opt_L7 (Flag opt_level) (translateTo (cTerm certiL6) (Flag opt_level) p).

Definition emit_L6_anf `{F:utils.Fuel} (opt_level : nat) (p : Template.Ast.program)
  : exceptionMonad.exception string :=
  (* let opt := match opt_level with O => false | S O => true | _ => false end in *)
  do p' <- translateTo (cTerm certiL4) (Flag opt_level) p ;
  do p'' <- match opt_level with
           | S 0 =>  L6_pipeline_pre_cc false p'
           | S (S 0) => L6_pipeline_anf false p'
           | S (S (S 0)) => L6_pipeline_anf true p'
           | _ => L5_to_L6_anf false p'
           end;
  let '((_, cenv, nenv, _), (_, e)) := p'' in
  ret (cps_show.show_exp nenv cenv false e).

Definition compile_template_L7_anf `{F:utils.Fuel} (opt_level : nat) (p : Template.Ast.program)
  : exception (cps_util.name_env * Clight.program * Clight.program)  :=
  let opt := match opt_level with O => false | S O => true | _ => false end in
  do p' <- translateTo (cTerm certiL4) (Flag opt_level) p ;
  do p'' <- L6_pipeline_anf opt p' ;
  ret (compile_L7_anf p'').

Definition emit_L6_cc `{F:utils.Fuel} (opt_level : nat) (p : Template.Ast.program)
  : exceptionMonad.exception string :=
  let opt := match opt_level with O => false | S O => true | _ => false end in
  do p' <- translateTo (cTerm certiL4) (Flag opt_level) p ;
  do p'' <- L6_pipeline_anf opt p' ;
  let '((_, cenv, nenv, _), (_, e)) := p'' in
  ret (cps_show.show_exp nenv cenv false e).

Definition emit_L6_pre_cc `{F:utils.Fuel} (opt_level : nat) (p : Template.Ast.program)
  : exceptionMonad.exception string :=
  let opt := match opt_level with O => false | S O => true | _ => false end in
  do p' <- translateTo (cTerm certiL4) (Flag opt_level) p ;
  do p'' <- L6_pipeline_pre_cc opt p' ;
  let '((_, cenv, nenv, _), (_, e)) := p'' in
  ret (cps_show.show_exp nenv cenv false e).

(* Zoe: Commenting out until merge is done *)

Require Import Glue.glue.
Definition make_glue (p : Template.Ast.program)
  : exception (cps_util.name_env * Clight.program * Clight.program * list string)  :=
  match generate_glue p with
  | (nenv, Some hdr, Some prg, logs) =>
      Ret (nenv, hdr, prg, logs)
  | _ => Exc ""
  end.


Open Scope positive_scope.

Definition show_exn  (x : exceptionMonad.exception (cTerm certiL6)) : string :=
  match x with
  | exceptionMonad.Exc s => s
  | exceptionMonad.Ret ((p,cenv, nenv, fenv), (g, e)) => L6.cps_show.show_exp nenv cenv true e
  end.


(* copy of L6.instances.L5a_comp_L6 *)
(* Definition L5a_comp_L6 (v:(ienv * L4.L5a.cps)): ((L6.eval.prims * cEnv * nEnv)* (L6.eval.env * L6.cps.exp)):=
    match v with
        | pair venv vt =>
          let '(cenv, nenv, next_cTag, next_iTag, t) := L6.L5_to_L6.convert_top default_cTag default_iTag fun_fTag kon_fTag (venv, vt) in
          let '(cenv',nenv', t') :=  L6.closure_conversion.closure_conversion_hoist
                                       bogus_cloTag
                                       (L6.shrink_cps.shrink_top t)
                                       next_cTag
                                       next_iTag
                                       cenv nenv in
          ((M.empty _ , (add_cloTag bogus_cloTag bogus_cloiTag cenv'), nenv'),  (M.empty _,  L6.shrink_cps.shrink_top t'))
    end.
 *)



(*
Require Import Benchmarks.Binom
        Benchmarks.vs.


Instance fuel : utils.Fuel := { fuel := 2 ^ 14 }.


Ltac computeExtract certiL4 f:=
(let t:= eval compute in (translateTo (cTerm certiL4) f) in
     match t with
       |Ret ?xx => exact xx
     end).

Definition ext_comp `{F:utils.Fuel} := fun prog =>
  let t := (translateTo (cTerm certiL6) (Flag 0) prog) in
  match t with
  | Ret xx => xx
  | _ => ((M.empty _, M.empty _, M.empty _, M.empty _) , (M.empty _, cps.Ehalt 1%positive))
  end.

Definition ext_comp_opt `{F:utils.Fuel} f := fun prog =>
  let t := (translateTo (cTerm certiL6) f prog) in
  match t with
  | Ret xx => xx
  | _ => ((M.empty _, M.empty _, M.empty _, M.empty _) , (M.empty _, cps.Ehalt 1%positive))
  end.

Quote Recursively Definition foo := (2+3).

Definition foo6 := Eval native_compute in (translateTo (cTerm certiL6) (Flag 1) foo).
Print foo6.

Definition test := Eval native_compute in
  let '(nenv , p , _) := (compile_L7 (ext_comp_opt (Flag 1) foo)) in
  p.
Print test.


Quote Recursively Definition binom := Binom.main.
*)

(*
(*  Quote Recursively Definition vs := vs.main_h.  (*ce_example_ent*) *)
Quote Recursively Definition binom := Binom.main.
(* Quote Recursively Definition graph_color := Color.ex_2.  (*(Color.run G16)*)    *)

Quote Recursively Definition graph_color := (2+3).  (*(Color.run G16)*)


(*
 Definition demo4 := Eval native_compute in (translateTo (cTerm certiL4) (Flag 0) graph_color).

 Print demo4.
 Definition demo5 := Eval native_compute in (translateTo (cTerm certiL5) (Flag 0) Demo1).
 Set Printing Depth 1000.
 Print demo5.
 Definition binom4 := Eval native_compute in (translateTo (cTerm certiL4) (Flag 0) binom).
 Definition binom5 := Eval native_compute in (translateTo (cTerm certiL5) (Flag 0) binom).

Definition color5 := Eval native_compute in (translateTo (cTerm certiL5) (Flag 0) graph_color).

Print color5.



Definition binom2 := Eval native_compute in (translateTo (cTerm certiL2k) (Flag 0) binom).
Definition eval_c2 := match binom2 with
                      | Ret (mkPgm p env) =>
                        Re
t (L2k.wcbvEval.wcbvEval env 1000%nat p)
                        | Exc s => Exc "foo"
                      end.

Definition eval_c2' := Eval native_compute in eval_c2.
Print eval_c2'.


Definition binom3 := Eval native_compute in (translateTo (cTerm certiL3_eta) (Flag 0) binom).


Require Export L4.expression.
Print binom4.
Definition eval_c4 := match binom5 with
                      | Ret p =>
                        Ret (L5_evaln 20%nat p)
                        | Exc s => Exc "foo"
                      end.

Definition eval_c4' := Eval vm_compute in eval_c4.
Print eval_c4'.

(* Definition vs5 := Eval native_compute in (translateTo (cTerm certiL5a) vs).  *)
Print color5.



(* Definition test := printProg (compile_L7 (ext_comp vs)) "output/vs_h.c".      *)
(*  Definition test := printProg (compile_L7 (ext_comp graph_color)) "output/color.c".    *)




(*  This can be used to test L6 (using an L5 program, extract to ML and run in ocaml to translate to L6 and then run using L6 executable semantics : *)

(*
Require Import  ExtLib.Data.String.
(* Multistep *)
Fixpoint mstep_L6  (x : (cTerm certiL6)) (n:nat) :=
  match n with
    | O =>
      Ret x
    | S n' =>
      let '((p,cenv, nenv, fenv), (rho, e)) := x in
      (match (L6.eval.sstep_f p cenv rho e) with
         | Ret (rho', e') => mstep_L6 ((p, cenv, nenv, fenv), (rho',e')) n'
         | Exc s => Exc ("Error :"++s++" at "++(nat2string10 n)++" from end")%string
       end)
  end.

Definition print_BigStepResult_L6 p  n:=
  let '((prim,cenv, nenv, fenv), (rho, e)) := p in
  L7.L6_to_Clight.print (
      match (L6_evaln n p) with
      | Error s _ => s
      | OutOfTime (_, (rho', e')) => "Out of time:"++ (show_cenv cenv)++(show_env nenv cenv false rho')++ (show_exp nenv cenv false e')
      | Result v => show_val nenv cenv false v
      end).

 Definition comp_L6 p := match p
                          with
                            | Exc s => Exc s
                            | Ret v =>  L6.instances.certiL5_t0_L6 v
                        end.

Definition comp_to_L6:= fun p =>
                       comp_L6 (translateTo (cTerm certiL5) p).

Definition testL6 := match comp_L6 demo5 with
                   | Ret ((pr,cenv,nenv), (env, t)) => print_BigStepResult_L6 ((pr,cenv,nenv), (env, t)) 30%nat
                   | _ =>   L7.L6_to_Clight.print ("Failed during comp_L6")
                     end.

Require Import ExtrOcamlBasic.
Require Import ExtrOcamlString.
Require Import ExtrOcamlZInt.
Require Import ExtrOcamlNatInt.

Extract Inductive Decimal.int => unit [ "(fun _ -> ())" "(fun _ -> ())" ] "(fun _ _ _ -> assert false)".

Extract Constant L6_to_Clight.print => "(fun s-> print_string (String.concat """" (List.map (String.make 1) s)))".


 Extract Constant   varImplDummyPair.varClassNVar => " (fun f (p:int*bool) -> varClass0 (f (fst p)))".
Extraction "test_demo1.ml" testL6.
Definition demo1 :=  (List.app (List.repeat true 5) (List.repeat false 3)).
From CertiCoq Require Import CertiCoq.
Definition foo := 2+ 3.

CertiCoq Compile demo1.
*)



(*  Section TEST_L7. *)
(* This can be used to test Clight (using an L5 program, extract to ocaml and run to translate to Clight and then run using Clightexec: *)
(*
(*  Definition binom7 :=  compile_opt_L7 (comp_L6 binom5). *)
(* Definition vs7 :=  compile_opt_L7 (comp_L6 vs5).  *)
 Definition color7 :=  compile_opt_L7 (comp_L6 color5).




 Extraction Language Ocaml.
(* Standard lib -- Comment out if extracting full Compiler using build.sh *)
Require Import ExtrOcamlBasic.
Require Import ExtrOcamlString.
Require Import ExtrOcamlNatInt.
(* Coqlib *)
Extract Inlined Constant Coqlib.proj_sumbool => "(fun x -> x)".

Extract Constant L7.L6_to_Clight.print => "print_string".

Definition print_BigStepResult_L7 (p:cps.M.t BasicAst.name*Clight.program) (n:nat):=
  L7.L6_to_Clight.print (
      match (L7.Clightexec.run_wo_main threadInfIdent bodyIdent p n) with
      | Error s _ => s
      | OutOfTime _ => "Out of time"
      | Result v => show_nat (Coqlib.nat_of_Z (Integers.Int.unsigned v))
      end).







 Definition print_opt_BigStepResult_L7 (po:exception (cps.M.t BasicAst.name*Clight.program)) n :=
   match po with
   | Ret ( nenv, p) => print_BigStepResult_L7 (nenv, p) n
   | _ => tt
   end.






(*Definition testBinom := (print_opt_BigStepResult_L7 binom7 10). *)
(* Definition testVs := (print_opt_BigStepResult_L7 vs7 10).   *)
Definition testColor := (print_opt_BigStepResult_L7 color7 10).

(* Extraction "testBinom2_l7.ml" testBinom. *)
Extraction "testColorT_L7.ml" testColor.
(*Extraction "testVs2_L7.ml" testVs.  *)

*)
(* End TEST_L7. *)
*)
*)

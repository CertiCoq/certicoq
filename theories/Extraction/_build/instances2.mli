open AstCommon
open Datatypes
open L3_to_L3_eta
open L3_to_L4
open L4_2_to_L4_5
open L4_5_to_L5
open L4_to_L4_1_to_L4_2
open UsefulTypes
open CertiClasses
open CertiClasses2
open Compile1
open ExceptionMonad
open Expression
open Terms
open VarImplZ
open Variables

type coq_L3_eta_Program = coq_Term coq_Program

val certiL3_to_L3_eta :
  ((coq_Term coq_Program, coq_Term coq_Program) cTerm, (coq_L3_eta_Program,
  coq_L3_eta_Program) cTerm) coq_CerticoqTranslation

val certiL3_eta_to_L4 :
  ((coq_L3_eta_Program, coq_L3_eta_Program) cTerm, (ienv * exp, ienv * exp)
  cTerm) coq_CerticoqTranslation

val certiL4_to_L4_2 :
  ((ienv * exp, ienv * exp) cTerm, (ienv * coq_L4_2_Term,
  ienv * coq_L4_2_Term) cTerm) coq_CerticoqTotalTranslation

val certiL4_2_to_L4_5 :
  ((ienv * coq_L4_2_Term, ienv * coq_L4_2_Term) cTerm, (ienv * coq_L4_5_Term,
  ienv * coq_L4_5_Term) cTerm) coq_CerticoqTotalTranslation

type coq_L5Term = (coq_NVar, coq_L5Opid) coq_NTerm

val certiL4_5_to_L5 :
  ((ienv * coq_L4_5_Term, ienv * coq_L4_5_Term) cTerm, (ienv * coq_L5Term,
  ienv * coq_L5Term) cTerm) coq_CerticoqTotalTranslation

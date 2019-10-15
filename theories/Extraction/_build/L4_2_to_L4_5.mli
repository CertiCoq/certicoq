open Datatypes
open L4_5_to_L5
open L4_to_L4_1_to_L4_2
open List0
open UsefulTypes
open PolyEval
open Terms
open VarImplZ
open VarInterface
open Variables

type coq_L4_5_Term = (coq_NVar, coq_L4_5Opid) coq_NTerm

val mapOpidL4_to_L4_5 : coq_L4Opid -> coq_L4_5Opid

val coq_L4_2_to_L4_5 : coq_L4_2_Term -> coq_L4_5_Term

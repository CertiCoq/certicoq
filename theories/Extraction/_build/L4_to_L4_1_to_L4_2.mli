open BasicAst
open Basics
open BinNat
open Datatypes
open FMapPositive
open List0
open Expression
open List1
open PolyEval
open Terms
open TermsDB
open Variables

val mkNames : (int * name list) -> name list

val tL4_to_L4_1 : exp -> (name, coq_L4Opid) coq_DTerm

val ltL4_to_L4_1 : exps -> (name, coq_L4Opid) coq_DTerm list

val ftL4_to_L4_1 : efnlst -> (name, coq_L4Opid) coq_DTerm list

val btL4_to_L4_1 : branches_e -> coq_L4Opid branch list

val mkVar : int -> int

val mkNVar : (int * name) -> coq_NVar

type coq_L4_1_Term = (name, coq_L4Opid) coq_DTerm

type coq_L4_2_Term = (coq_NVar, coq_L4Opid) coq_NTerm

val tL4_1_to_L4_2 : coq_L4_1_Term -> coq_L4_2_Term

val tL4_to_L4_2 : exp -> coq_L4_2_Term

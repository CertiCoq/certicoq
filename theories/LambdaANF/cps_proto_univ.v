(* The stack-of-frames one-hole contexts, with the right indices, are isomorphic to 
   [cps.exp_ctx] and [cps.fundefs_ctx] *)

From Coq Require Import ZArith.ZArith Lists.List Sets.Ensembles Strings.String.
Require Import Lia.
Import ListNotations.
From CertiCoq Require Import Common.
From CertiCoq.LambdaANF Require Import
    Prototype cps cps_util ctx
    identifiers Ensembles_util.

From MetaCoq Require Import Template.All.

From CertiCoq.LambdaANF Require Import PrototypeGenFrame cps.
   
MetaCoq Run (mk_Frame_ops
  (MPfile ["cps_proto_univ"; "LambdaANF"; "CertiCoq"])
  (MPfile ["cps"; "LambdaANF"; "CertiCoq"], "exp")
  exp [var; fun_tag; ctor_tag; prim; N; list var; primitive]).

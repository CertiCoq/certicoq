open BinNat
open Datatypes
open List0
open Maps
open Monad0
open StateMonad
open Cps
open Ctx
open Identifiers
open Set_util
open State

type coq_VarInfo =
| FreeVar of var
| WrapperFun of var

type coq_VarInfoMap = coq_VarInfo PTree.t

type 't lambdaM = (unit, 't) compM

val rename : coq_VarInfoMap -> var -> var

val rename_lst : coq_VarInfoMap -> var list -> var list

val add_free_vars :
  var list -> coq_VarInfoMap -> (var list * coq_VarInfoMap) lambdaM

type coq_FunInfo' =
| Fun' of var * fTag * var list * PS.t

type coq_FunInfoMap' = coq_FunInfo' PTree.t

type coq_GFunInfo = var
  (* singleton inductive, whose constructor was GFun *)

type coq_GFunMap = coq_GFunInfo M.t

val add_functions' :
  fundefs -> var list -> PS.t -> coq_FunInfoMap' -> coq_GFunMap -> bool ->
  (coq_FunInfoMap' * coq_GFunMap) lambdaM

val make_wrappers :
  fundefs -> coq_VarInfoMap -> coq_FunInfoMap' -> (exp_ctx * coq_VarInfoMap)
  lambdaM

val exp_lambda_lift' :
  exp -> PS.t -> coq_VarInfoMap -> coq_FunInfoMap' -> coq_GFunMap -> exp
  lambdaM

val fundefs_lambda_lift' :
  fundefs -> fundefs -> coq_VarInfoMap -> coq_FunInfoMap' -> coq_GFunMap ->
  fundefs lambdaM

val lambda_lift' : exp -> comp_data -> exp * comp_data

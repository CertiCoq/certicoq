open Ast0
open AstCommon
open BasicAst
open Datatypes
open Compile0
open Compile1
open Utils

type __ = Obj.t

module L3t :
 sig
  type coq_L1gTerm = Compile0.coq_Term

  type coq_L1gTerms = Compile0.coq_Term list

  type coq_L1gBrs = Compile0.coq_Brs

  type coq_L1gDefs = Compile0.coq_Defs

  type coq_L1gPgm = coq_L1gTerm coq_Program

  type coq_L1gEC = coq_L1gTerm envClass

  type coq_L1gEnv = coq_L1gTerm environ

  type projection = inductive * nat

  val project_dec : projection -> projection -> bool

  type coq_Term = Compile1.coq_Term =
  | TRel of nat
  | TProof
  | TLambda of name * coq_Term
  | TLetIn of name * coq_Term * coq_Term
  | TApp of coq_Term * coq_Term
  | TConst of char list
  | TConstruct of inductive * nat * coq_Terms
  | TCase of inductive * coq_Term * coq_Brs
  | TFix of coq_Defs * nat
  | TProj of projection * coq_Term
  | TWrong of char list
  and coq_Terms = Compile1.coq_Terms =
  | Coq_tnil
  | Coq_tcons of coq_Term * coq_Terms
  and coq_Brs = Compile1.coq_Brs =
  | Coq_bnil
  | Coq_bcons of nat * coq_Term * coq_Brs
  and coq_Defs = Compile1.coq_Defs =
  | Coq_dnil
  | Coq_dcons of name * coq_Term * nat * coq_Defs

  val coq_Term_rect :
    (nat -> 'a1) -> 'a1 -> (name -> coq_Term -> 'a1 -> 'a1) -> (name ->
    coq_Term -> 'a1 -> coq_Term -> 'a1 -> 'a1) -> (coq_Term -> 'a1 ->
    coq_Term -> 'a1 -> 'a1) -> (char list -> 'a1) -> (inductive -> nat ->
    coq_Terms -> 'a1) -> (inductive -> coq_Term -> 'a1 -> coq_Brs -> 'a1) ->
    (coq_Defs -> nat -> 'a1) -> (projection -> coq_Term -> 'a1 -> 'a1) ->
    (char list -> 'a1) -> coq_Term -> 'a1

  val coq_Term_rec :
    (nat -> 'a1) -> 'a1 -> (name -> coq_Term -> 'a1 -> 'a1) -> (name ->
    coq_Term -> 'a1 -> coq_Term -> 'a1 -> 'a1) -> (coq_Term -> 'a1 ->
    coq_Term -> 'a1 -> 'a1) -> (char list -> 'a1) -> (inductive -> nat ->
    coq_Terms -> 'a1) -> (inductive -> coq_Term -> 'a1 -> coq_Brs -> 'a1) ->
    (coq_Defs -> nat -> 'a1) -> (projection -> coq_Term -> 'a1 -> 'a1) ->
    (char list -> 'a1) -> coq_Term -> 'a1

  val coq_Terms_rect :
    'a1 -> (coq_Term -> coq_Terms -> 'a1 -> 'a1) -> coq_Terms -> 'a1

  val coq_Terms_rec :
    'a1 -> (coq_Term -> coq_Terms -> 'a1 -> 'a1) -> coq_Terms -> 'a1

  val coq_Brs_rect :
    'a1 -> (nat -> coq_Term -> coq_Brs -> 'a1 -> 'a1) -> coq_Brs -> 'a1

  val coq_Brs_rec :
    'a1 -> (nat -> coq_Term -> coq_Brs -> 'a1 -> 'a1) -> coq_Brs -> 'a1

  val coq_Defs_rect :
    'a1 -> (name -> coq_Term -> nat -> coq_Defs -> 'a1 -> 'a1) -> coq_Defs ->
    'a1

  val coq_Defs_rec :
    'a1 -> (name -> coq_Term -> nat -> coq_Defs -> 'a1 -> 'a1) -> coq_Defs ->
    'a1

  val coq_Terms_list : coq_Terms -> coq_Term list

  val tlength : coq_Terms -> nat

  type coq_R_tlength = Compile1.coq_R_tlength =
  | R_tlength_0 of coq_Terms
  | R_tlength_1 of coq_Terms * coq_Term * coq_Terms * nat * coq_R_tlength

  val coq_R_tlength_rect :
    (coq_Terms -> __ -> 'a1) -> (coq_Terms -> coq_Term -> coq_Terms -> __ ->
    nat -> coq_R_tlength -> 'a1 -> 'a1) -> coq_Terms -> nat -> coq_R_tlength
    -> 'a1

  val coq_R_tlength_rec :
    (coq_Terms -> __ -> 'a1) -> (coq_Terms -> coq_Term -> coq_Terms -> __ ->
    nat -> coq_R_tlength -> 'a1 -> 'a1) -> coq_Terms -> nat -> coq_R_tlength
    -> 'a1

  val tlength_rect :
    (coq_Terms -> __ -> 'a1) -> (coq_Terms -> coq_Term -> coq_Terms -> __ ->
    'a1 -> 'a1) -> coq_Terms -> 'a1

  val tlength_rec :
    (coq_Terms -> __ -> 'a1) -> (coq_Terms -> coq_Term -> coq_Terms -> __ ->
    'a1 -> 'a1) -> coq_Terms -> 'a1

  val coq_R_tlength_correct : coq_Terms -> nat -> coq_R_tlength

  val blength : coq_Brs -> nat

  type coq_R_blength = Compile1.coq_R_blength =
  | R_blength_0 of coq_Brs
  | R_blength_1 of coq_Brs * nat * coq_Term * coq_Brs * nat * coq_R_blength

  val coq_R_blength_rect :
    (coq_Brs -> __ -> 'a1) -> (coq_Brs -> nat -> coq_Term -> coq_Brs -> __ ->
    nat -> coq_R_blength -> 'a1 -> 'a1) -> coq_Brs -> nat -> coq_R_blength ->
    'a1

  val coq_R_blength_rec :
    (coq_Brs -> __ -> 'a1) -> (coq_Brs -> nat -> coq_Term -> coq_Brs -> __ ->
    nat -> coq_R_blength -> 'a1 -> 'a1) -> coq_Brs -> nat -> coq_R_blength ->
    'a1

  val blength_rect :
    (coq_Brs -> __ -> 'a1) -> (coq_Brs -> nat -> coq_Term -> coq_Brs -> __ ->
    'a1 -> 'a1) -> coq_Brs -> 'a1

  val blength_rec :
    (coq_Brs -> __ -> 'a1) -> (coq_Brs -> nat -> coq_Term -> coq_Brs -> __ ->
    'a1 -> 'a1) -> coq_Brs -> 'a1

  val coq_R_blength_correct : coq_Brs -> nat -> coq_R_blength

  val tappend : coq_Terms -> coq_Terms -> coq_Terms

  val tdrop : nat -> coq_Terms -> coq_Terms

  val treverse : coq_Terms -> coq_Terms

  val dlength : coq_Defs -> nat

  val isApp_dec : coq_Term -> bool

  val lift : nat -> coq_Term -> coq_Term

  val lifts : nat -> coq_Terms -> coq_Terms

  val liftBs : nat -> coq_Brs -> coq_Brs

  val liftDs : nat -> coq_Defs -> coq_Defs

  type coq_R_lift = Compile1.coq_R_lift =
  | R_lift_0 of nat * coq_Term * nat
  | R_lift_1 of nat * coq_Term * nat * comparison
  | R_lift_2 of nat * coq_Term
  | R_lift_3 of nat * coq_Term * name * coq_Term * coq_Term * coq_R_lift
  | R_lift_4 of nat * coq_Term * name * coq_Term * coq_Term * coq_Term
     * coq_R_lift * coq_Term * coq_R_lift
  | R_lift_5 of nat * coq_Term * coq_Term * coq_Term * coq_Term * coq_R_lift
     * coq_Term * coq_R_lift
  | R_lift_6 of nat * coq_Term * inductive * nat * coq_Terms * coq_Terms
     * coq_R_lifts
  | R_lift_7 of nat * coq_Term * inductive * coq_Term * coq_Brs * coq_Term
     * coq_R_lift * coq_Brs * coq_R_liftBs
  | R_lift_8 of nat * coq_Term * coq_Defs * nat * coq_Defs * coq_R_liftDs
  | R_lift_9 of nat * coq_Term * projection * coq_Term * coq_Term * coq_R_lift
  | R_lift_10 of nat * coq_Term * coq_Term
  and coq_R_lifts = Compile1.coq_R_lifts =
  | R_lifts_0 of nat * coq_Terms
  | R_lifts_1 of nat * coq_Terms * coq_Term * coq_Terms * coq_Term
     * coq_R_lift * coq_Terms * coq_R_lifts
  and coq_R_liftBs = Compile1.coq_R_liftBs =
  | R_liftBs_0 of nat * coq_Brs
  | R_liftBs_1 of nat * coq_Brs * nat * coq_Term * coq_Brs * coq_Term
     * coq_R_lift * coq_Brs * coq_R_liftBs
  and coq_R_liftDs = Compile1.coq_R_liftDs =
  | R_liftDs_0 of nat * coq_Defs
  | R_liftDs_1 of nat * coq_Defs * name * coq_Term * nat * coq_Defs
     * coq_Term * coq_R_lift * coq_Defs * coq_R_liftDs

  val coq_R_lift_rect :
    (nat -> coq_Term -> nat -> __ -> __ -> 'a1) -> (nat -> coq_Term -> nat ->
    __ -> comparison -> __ -> __ -> 'a1) -> (nat -> coq_Term -> __ -> 'a1) ->
    (nat -> coq_Term -> name -> coq_Term -> __ -> coq_Term -> coq_R_lift ->
    'a1 -> 'a1) -> (nat -> coq_Term -> name -> coq_Term -> coq_Term -> __ ->
    coq_Term -> coq_R_lift -> 'a1 -> coq_Term -> coq_R_lift -> 'a1 -> 'a1) ->
    (nat -> coq_Term -> coq_Term -> coq_Term -> __ -> coq_Term -> coq_R_lift
    -> 'a1 -> coq_Term -> coq_R_lift -> 'a1 -> 'a1) -> (nat -> coq_Term ->
    inductive -> nat -> coq_Terms -> __ -> coq_Terms -> coq_R_lifts -> 'a1)
    -> (nat -> coq_Term -> inductive -> coq_Term -> coq_Brs -> __ -> coq_Term
    -> coq_R_lift -> 'a1 -> coq_Brs -> coq_R_liftBs -> 'a1) -> (nat ->
    coq_Term -> coq_Defs -> nat -> __ -> coq_Defs -> coq_R_liftDs -> 'a1) ->
    (nat -> coq_Term -> projection -> coq_Term -> __ -> coq_Term ->
    coq_R_lift -> 'a1 -> 'a1) -> (nat -> coq_Term -> coq_Term -> __ -> __ ->
    'a1) -> nat -> coq_Term -> coq_Term -> coq_R_lift -> 'a1

  val coq_R_lift_rec :
    (nat -> coq_Term -> nat -> __ -> __ -> 'a1) -> (nat -> coq_Term -> nat ->
    __ -> comparison -> __ -> __ -> 'a1) -> (nat -> coq_Term -> __ -> 'a1) ->
    (nat -> coq_Term -> name -> coq_Term -> __ -> coq_Term -> coq_R_lift ->
    'a1 -> 'a1) -> (nat -> coq_Term -> name -> coq_Term -> coq_Term -> __ ->
    coq_Term -> coq_R_lift -> 'a1 -> coq_Term -> coq_R_lift -> 'a1 -> 'a1) ->
    (nat -> coq_Term -> coq_Term -> coq_Term -> __ -> coq_Term -> coq_R_lift
    -> 'a1 -> coq_Term -> coq_R_lift -> 'a1 -> 'a1) -> (nat -> coq_Term ->
    inductive -> nat -> coq_Terms -> __ -> coq_Terms -> coq_R_lifts -> 'a1)
    -> (nat -> coq_Term -> inductive -> coq_Term -> coq_Brs -> __ -> coq_Term
    -> coq_R_lift -> 'a1 -> coq_Brs -> coq_R_liftBs -> 'a1) -> (nat ->
    coq_Term -> coq_Defs -> nat -> __ -> coq_Defs -> coq_R_liftDs -> 'a1) ->
    (nat -> coq_Term -> projection -> coq_Term -> __ -> coq_Term ->
    coq_R_lift -> 'a1 -> 'a1) -> (nat -> coq_Term -> coq_Term -> __ -> __ ->
    'a1) -> nat -> coq_Term -> coq_Term -> coq_R_lift -> 'a1

  val coq_R_lifts_rect :
    (nat -> coq_Terms -> __ -> 'a1) -> (nat -> coq_Terms -> coq_Term ->
    coq_Terms -> __ -> coq_Term -> coq_R_lift -> coq_Terms -> coq_R_lifts ->
    'a1 -> 'a1) -> nat -> coq_Terms -> coq_Terms -> coq_R_lifts -> 'a1

  val coq_R_lifts_rec :
    (nat -> coq_Terms -> __ -> 'a1) -> (nat -> coq_Terms -> coq_Term ->
    coq_Terms -> __ -> coq_Term -> coq_R_lift -> coq_Terms -> coq_R_lifts ->
    'a1 -> 'a1) -> nat -> coq_Terms -> coq_Terms -> coq_R_lifts -> 'a1

  val coq_R_liftBs_rect :
    (nat -> coq_Brs -> __ -> 'a1) -> (nat -> coq_Brs -> nat -> coq_Term ->
    coq_Brs -> __ -> coq_Term -> coq_R_lift -> coq_Brs -> coq_R_liftBs -> 'a1
    -> 'a1) -> nat -> coq_Brs -> coq_Brs -> coq_R_liftBs -> 'a1

  val coq_R_liftBs_rec :
    (nat -> coq_Brs -> __ -> 'a1) -> (nat -> coq_Brs -> nat -> coq_Term ->
    coq_Brs -> __ -> coq_Term -> coq_R_lift -> coq_Brs -> coq_R_liftBs -> 'a1
    -> 'a1) -> nat -> coq_Brs -> coq_Brs -> coq_R_liftBs -> 'a1

  val coq_R_liftDs_rect :
    (nat -> coq_Defs -> __ -> 'a1) -> (nat -> coq_Defs -> name -> coq_Term ->
    nat -> coq_Defs -> __ -> coq_Term -> coq_R_lift -> coq_Defs ->
    coq_R_liftDs -> 'a1 -> 'a1) -> nat -> coq_Defs -> coq_Defs ->
    coq_R_liftDs -> 'a1

  val coq_R_liftDs_rec :
    (nat -> coq_Defs -> __ -> 'a1) -> (nat -> coq_Defs -> name -> coq_Term ->
    nat -> coq_Defs -> __ -> coq_Term -> coq_R_lift -> coq_Defs ->
    coq_R_liftDs -> 'a1 -> 'a1) -> nat -> coq_Defs -> coq_Defs ->
    coq_R_liftDs -> 'a1

  val lift_rect :
    (nat -> coq_Term -> nat -> __ -> __ -> 'a1) -> (nat -> coq_Term -> nat ->
    __ -> comparison -> __ -> __ -> 'a1) -> (nat -> coq_Term -> __ -> 'a1) ->
    (nat -> coq_Term -> name -> coq_Term -> __ -> 'a1 -> 'a1) -> (nat ->
    coq_Term -> name -> coq_Term -> coq_Term -> __ -> 'a1 -> 'a1 -> 'a1) ->
    (nat -> coq_Term -> coq_Term -> coq_Term -> __ -> 'a1 -> 'a1 -> 'a1) ->
    (nat -> coq_Term -> inductive -> nat -> coq_Terms -> __ -> 'a1) -> (nat
    -> coq_Term -> inductive -> coq_Term -> coq_Brs -> __ -> 'a1 -> 'a1) ->
    (nat -> coq_Term -> coq_Defs -> nat -> __ -> 'a1) -> (nat -> coq_Term ->
    projection -> coq_Term -> __ -> 'a1 -> 'a1) -> (nat -> coq_Term ->
    coq_Term -> __ -> __ -> 'a1) -> nat -> coq_Term -> 'a1

  val lift_rec :
    (nat -> coq_Term -> nat -> __ -> __ -> 'a1) -> (nat -> coq_Term -> nat ->
    __ -> comparison -> __ -> __ -> 'a1) -> (nat -> coq_Term -> __ -> 'a1) ->
    (nat -> coq_Term -> name -> coq_Term -> __ -> 'a1 -> 'a1) -> (nat ->
    coq_Term -> name -> coq_Term -> coq_Term -> __ -> 'a1 -> 'a1 -> 'a1) ->
    (nat -> coq_Term -> coq_Term -> coq_Term -> __ -> 'a1 -> 'a1 -> 'a1) ->
    (nat -> coq_Term -> inductive -> nat -> coq_Terms -> __ -> 'a1) -> (nat
    -> coq_Term -> inductive -> coq_Term -> coq_Brs -> __ -> 'a1 -> 'a1) ->
    (nat -> coq_Term -> coq_Defs -> nat -> __ -> 'a1) -> (nat -> coq_Term ->
    projection -> coq_Term -> __ -> 'a1 -> 'a1) -> (nat -> coq_Term ->
    coq_Term -> __ -> __ -> 'a1) -> nat -> coq_Term -> 'a1

  val lifts_rect :
    (nat -> coq_Terms -> __ -> 'a1) -> (nat -> coq_Terms -> coq_Term ->
    coq_Terms -> __ -> 'a1 -> 'a1) -> nat -> coq_Terms -> 'a1

  val lifts_rec :
    (nat -> coq_Terms -> __ -> 'a1) -> (nat -> coq_Terms -> coq_Term ->
    coq_Terms -> __ -> 'a1 -> 'a1) -> nat -> coq_Terms -> 'a1

  val liftBs_rect :
    (nat -> coq_Brs -> __ -> 'a1) -> (nat -> coq_Brs -> nat -> coq_Term ->
    coq_Brs -> __ -> 'a1 -> 'a1) -> nat -> coq_Brs -> 'a1

  val liftBs_rec :
    (nat -> coq_Brs -> __ -> 'a1) -> (nat -> coq_Brs -> nat -> coq_Term ->
    coq_Brs -> __ -> 'a1 -> 'a1) -> nat -> coq_Brs -> 'a1

  val liftDs_rect :
    (nat -> coq_Defs -> __ -> 'a1) -> (nat -> coq_Defs -> name -> coq_Term ->
    nat -> coq_Defs -> __ -> 'a1 -> 'a1) -> nat -> coq_Defs -> 'a1

  val liftDs_rec :
    (nat -> coq_Defs -> __ -> 'a1) -> (nat -> coq_Defs -> name -> coq_Term ->
    nat -> coq_Defs -> __ -> 'a1 -> 'a1) -> nat -> coq_Defs -> 'a1

  val coq_R_lift_correct : nat -> coq_Term -> coq_Term -> coq_R_lift

  val coq_R_lifts_correct : nat -> coq_Terms -> coq_Terms -> coq_R_lifts

  val coq_R_liftBs_correct : nat -> coq_Brs -> coq_Brs -> coq_R_liftBs

  val coq_R_liftDs_correct : nat -> coq_Defs -> coq_Defs -> coq_R_liftDs

  val etaExpand_args_Lam' :
    nat -> (coq_Terms -> coq_Term) -> coq_Terms -> coq_Term

  type coq_R_etaExpand_args_Lam' = Compile1.coq_R_etaExpand_args_Lam' =
  | R_etaExpand_args_Lam'_0 of nat * (coq_Terms -> coq_Term) * coq_Terms
  | R_etaExpand_args_Lam'_1 of nat * (coq_Terms -> coq_Term) * coq_Terms
     * nat * coq_Term * coq_R_etaExpand_args_Lam'

  val coq_R_etaExpand_args_Lam'_rect :
    (nat -> (coq_Terms -> coq_Term) -> coq_Terms -> __ -> 'a1) -> (nat ->
    (coq_Terms -> coq_Term) -> coq_Terms -> nat -> __ -> coq_Term ->
    coq_R_etaExpand_args_Lam' -> 'a1 -> 'a1) -> nat -> (coq_Terms ->
    coq_Term) -> coq_Terms -> coq_Term -> coq_R_etaExpand_args_Lam' -> 'a1

  val coq_R_etaExpand_args_Lam'_rec :
    (nat -> (coq_Terms -> coq_Term) -> coq_Terms -> __ -> 'a1) -> (nat ->
    (coq_Terms -> coq_Term) -> coq_Terms -> nat -> __ -> coq_Term ->
    coq_R_etaExpand_args_Lam' -> 'a1 -> 'a1) -> nat -> (coq_Terms ->
    coq_Term) -> coq_Terms -> coq_Term -> coq_R_etaExpand_args_Lam' -> 'a1

  val etaExpand_args_Lam'_rect :
    (nat -> (coq_Terms -> coq_Term) -> coq_Terms -> __ -> 'a1) -> (nat ->
    (coq_Terms -> coq_Term) -> coq_Terms -> nat -> __ -> 'a1 -> 'a1) -> nat
    -> (coq_Terms -> coq_Term) -> coq_Terms -> 'a1

  val etaExpand_args_Lam'_rec :
    (nat -> (coq_Terms -> coq_Term) -> coq_Terms -> __ -> 'a1) -> (nat ->
    (coq_Terms -> coq_Term) -> coq_Terms -> nat -> __ -> 'a1 -> 'a1) -> nat
    -> (coq_Terms -> coq_Term) -> coq_Terms -> 'a1

  val coq_R_etaExpand_args_Lam'_correct :
    nat -> (coq_Terms -> coq_Term) -> coq_Terms -> coq_Term ->
    coq_R_etaExpand_args_Lam'

  val etaExpand_args_Lam :
    nat -> coq_Terms -> (coq_Terms -> coq_Term) -> coq_Terms -> coq_Term

  type coq_R_etaExpand_args_Lam = Compile1.coq_R_etaExpand_args_Lam =
  | R_etaExpand_args_Lam_0 of nat * coq_Terms * (coq_Terms -> coq_Term)
     * coq_Terms
  | R_etaExpand_args_Lam_1 of nat * coq_Terms * (coq_Terms -> coq_Term)
     * coq_Terms * coq_Term * coq_Terms
  | R_etaExpand_args_Lam_2 of nat * coq_Terms * (coq_Terms -> coq_Term)
     * coq_Terms * nat
  | R_etaExpand_args_Lam_3 of nat * coq_Terms * (coq_Terms -> coq_Term)
     * coq_Terms * nat * coq_Term * coq_Terms * coq_Term
     * coq_R_etaExpand_args_Lam

  val coq_R_etaExpand_args_Lam_rect :
    (nat -> coq_Terms -> (coq_Terms -> coq_Term) -> coq_Terms -> __ -> __ ->
    'a1) -> (nat -> coq_Terms -> (coq_Terms -> coq_Term) -> coq_Terms -> __
    -> coq_Term -> coq_Terms -> __ -> 'a1) -> (nat -> coq_Terms -> (coq_Terms
    -> coq_Term) -> coq_Terms -> nat -> __ -> __ -> 'a1) -> (nat -> coq_Terms
    -> (coq_Terms -> coq_Term) -> coq_Terms -> nat -> __ -> coq_Term ->
    coq_Terms -> __ -> coq_Term -> coq_R_etaExpand_args_Lam -> 'a1 -> 'a1) ->
    nat -> coq_Terms -> (coq_Terms -> coq_Term) -> coq_Terms -> coq_Term ->
    coq_R_etaExpand_args_Lam -> 'a1

  val coq_R_etaExpand_args_Lam_rec :
    (nat -> coq_Terms -> (coq_Terms -> coq_Term) -> coq_Terms -> __ -> __ ->
    'a1) -> (nat -> coq_Terms -> (coq_Terms -> coq_Term) -> coq_Terms -> __
    -> coq_Term -> coq_Terms -> __ -> 'a1) -> (nat -> coq_Terms -> (coq_Terms
    -> coq_Term) -> coq_Terms -> nat -> __ -> __ -> 'a1) -> (nat -> coq_Terms
    -> (coq_Terms -> coq_Term) -> coq_Terms -> nat -> __ -> coq_Term ->
    coq_Terms -> __ -> coq_Term -> coq_R_etaExpand_args_Lam -> 'a1 -> 'a1) ->
    nat -> coq_Terms -> (coq_Terms -> coq_Term) -> coq_Terms -> coq_Term ->
    coq_R_etaExpand_args_Lam -> 'a1

  val etaExpand_args_Lam_rect :
    (nat -> coq_Terms -> (coq_Terms -> coq_Term) -> coq_Terms -> __ -> __ ->
    'a1) -> (nat -> coq_Terms -> (coq_Terms -> coq_Term) -> coq_Terms -> __
    -> coq_Term -> coq_Terms -> __ -> 'a1) -> (nat -> coq_Terms -> (coq_Terms
    -> coq_Term) -> coq_Terms -> nat -> __ -> __ -> 'a1) -> (nat -> coq_Terms
    -> (coq_Terms -> coq_Term) -> coq_Terms -> nat -> __ -> coq_Term ->
    coq_Terms -> __ -> 'a1 -> 'a1) -> nat -> coq_Terms -> (coq_Terms ->
    coq_Term) -> coq_Terms -> 'a1

  val etaExpand_args_Lam_rec :
    (nat -> coq_Terms -> (coq_Terms -> coq_Term) -> coq_Terms -> __ -> __ ->
    'a1) -> (nat -> coq_Terms -> (coq_Terms -> coq_Term) -> coq_Terms -> __
    -> coq_Term -> coq_Terms -> __ -> 'a1) -> (nat -> coq_Terms -> (coq_Terms
    -> coq_Term) -> coq_Terms -> nat -> __ -> __ -> 'a1) -> (nat -> coq_Terms
    -> (coq_Terms -> coq_Term) -> coq_Terms -> nat -> __ -> coq_Term ->
    coq_Terms -> __ -> 'a1 -> 'a1) -> nat -> coq_Terms -> (coq_Terms ->
    coq_Term) -> coq_Terms -> 'a1

  val coq_R_etaExpand_args_Lam_correct :
    nat -> coq_Terms -> (coq_Terms -> coq_Term) -> coq_Terms -> coq_Term ->
    coq_R_etaExpand_args_Lam

  val etaExpand_args_Construct :
    nat -> coq_Terms -> inductive -> nat -> coq_Term

  val nLambda : nat -> coq_Term -> coq_Term

  type coq_R_nLambda = Compile1.coq_R_nLambda =
  | R_nLambda_0 of nat * coq_Term
  | R_nLambda_1 of nat * coq_Term * nat * coq_Term * coq_R_nLambda

  val coq_R_nLambda_rect :
    (nat -> coq_Term -> __ -> 'a1) -> (nat -> coq_Term -> nat -> __ ->
    coq_Term -> coq_R_nLambda -> 'a1 -> 'a1) -> nat -> coq_Term -> coq_Term
    -> coq_R_nLambda -> 'a1

  val coq_R_nLambda_rec :
    (nat -> coq_Term -> __ -> 'a1) -> (nat -> coq_Term -> nat -> __ ->
    coq_Term -> coq_R_nLambda -> 'a1 -> 'a1) -> nat -> coq_Term -> coq_Term
    -> coq_R_nLambda -> 'a1

  val nLambda_rect :
    (nat -> coq_Term -> __ -> 'a1) -> (nat -> coq_Term -> nat -> __ -> 'a1 ->
    'a1) -> nat -> coq_Term -> 'a1

  val nLambda_rec :
    (nat -> coq_Term -> __ -> 'a1) -> (nat -> coq_Term -> nat -> __ -> 'a1 ->
    'a1) -> nat -> coq_Term -> 'a1

  val coq_R_nLambda_correct : nat -> coq_Term -> coq_Term -> coq_R_nLambda

  val coq_Lambdan : nat -> coq_Term -> coq_Term

  type coq_R_Lambdan = Compile1.coq_R_Lambdan =
  | R_Lambdan_0 of nat * coq_Term
  | R_Lambdan_1 of nat * coq_Term * nat * coq_Term * coq_R_Lambdan

  val coq_R_Lambdan_rect :
    (nat -> coq_Term -> __ -> 'a1) -> (nat -> coq_Term -> nat -> __ ->
    coq_Term -> coq_R_Lambdan -> 'a1 -> 'a1) -> nat -> coq_Term -> coq_Term
    -> coq_R_Lambdan -> 'a1

  val coq_R_Lambdan_rec :
    (nat -> coq_Term -> __ -> 'a1) -> (nat -> coq_Term -> nat -> __ ->
    coq_Term -> coq_R_Lambdan -> 'a1 -> 'a1) -> nat -> coq_Term -> coq_Term
    -> coq_R_Lambdan -> 'a1

  val coq_Lambdan_rect :
    (nat -> coq_Term -> __ -> 'a1) -> (nat -> coq_Term -> nat -> __ -> 'a1 ->
    'a1) -> nat -> coq_Term -> 'a1

  val coq_Lambdan_rec :
    (nat -> coq_Term -> __ -> 'a1) -> (nat -> coq_Term -> nat -> __ -> 'a1 ->
    'a1) -> nat -> coq_Term -> 'a1

  val coq_R_Lambdan_correct : nat -> coq_Term -> coq_Term -> coq_R_Lambdan

  val mkExpand : nat -> (coq_Terms -> coq_Term) -> coq_Terms -> coq_Term

  type coq_R_mkExpand = Compile1.coq_R_mkExpand =
  | R_mkExpand_0 of nat * (coq_Terms -> coq_Term) * coq_Terms
  | R_mkExpand_1 of nat * (coq_Terms -> coq_Term) * coq_Terms * nat
     * coq_Term * coq_R_mkExpand

  val coq_R_mkExpand_rect :
    (nat -> (coq_Terms -> coq_Term) -> coq_Terms -> __ -> 'a1) -> (nat ->
    (coq_Terms -> coq_Term) -> coq_Terms -> nat -> __ -> coq_Term ->
    coq_R_mkExpand -> 'a1 -> 'a1) -> nat -> (coq_Terms -> coq_Term) ->
    coq_Terms -> coq_Term -> coq_R_mkExpand -> 'a1

  val coq_R_mkExpand_rec :
    (nat -> (coq_Terms -> coq_Term) -> coq_Terms -> __ -> 'a1) -> (nat ->
    (coq_Terms -> coq_Term) -> coq_Terms -> nat -> __ -> coq_Term ->
    coq_R_mkExpand -> 'a1 -> 'a1) -> nat -> (coq_Terms -> coq_Term) ->
    coq_Terms -> coq_Term -> coq_R_mkExpand -> 'a1

  val mkExpand_rect :
    (nat -> (coq_Terms -> coq_Term) -> coq_Terms -> __ -> 'a1) -> (nat ->
    (coq_Terms -> coq_Term) -> coq_Terms -> nat -> __ -> 'a1 -> 'a1) -> nat
    -> (coq_Terms -> coq_Term) -> coq_Terms -> 'a1

  val mkExpand_rec :
    (nat -> (coq_Terms -> coq_Term) -> coq_Terms -> __ -> 'a1) -> (nat ->
    (coq_Terms -> coq_Term) -> coq_Terms -> nat -> __ -> 'a1 -> 'a1) -> nat
    -> (coq_Terms -> coq_Term) -> coq_Terms -> 'a1

  val coq_R_mkExpand_correct :
    nat -> (coq_Terms -> coq_Term) -> coq_Terms -> coq_Term -> coq_R_mkExpand

  val etaExpand_aArgs :
    (coq_Terms -> coq_Term) -> nat -> nat -> coq_Terms -> coq_Terms ->
    coq_Term

  type coq_R_etaExpand_aArgs = Compile1.coq_R_etaExpand_aArgs =
  | R_etaExpand_aArgs_0 of nat * nat * coq_Terms * coq_Terms * nat * 
     coq_Term * coq_Terms * coq_Term * coq_R_etaExpand_aArgs
  | R_etaExpand_aArgs_1 of nat * nat * coq_Terms * coq_Terms * coq_Term
     * coq_Terms
  | R_etaExpand_aArgs_2 of nat * nat * coq_Terms * coq_Terms * nat

  val coq_R_etaExpand_aArgs_rect :
    (coq_Terms -> coq_Term) -> (nat -> nat -> coq_Terms -> coq_Terms -> nat
    -> __ -> coq_Term -> coq_Terms -> __ -> coq_Term -> coq_R_etaExpand_aArgs
    -> 'a1 -> 'a1) -> (nat -> nat -> coq_Terms -> coq_Terms -> __ -> coq_Term
    -> coq_Terms -> __ -> 'a1) -> (nat -> nat -> coq_Terms -> coq_Terms ->
    nat -> __ -> __ -> 'a1) -> nat -> nat -> coq_Terms -> coq_Terms ->
    coq_Term -> coq_R_etaExpand_aArgs -> 'a1

  val coq_R_etaExpand_aArgs_rec :
    (coq_Terms -> coq_Term) -> (nat -> nat -> coq_Terms -> coq_Terms -> nat
    -> __ -> coq_Term -> coq_Terms -> __ -> coq_Term -> coq_R_etaExpand_aArgs
    -> 'a1 -> 'a1) -> (nat -> nat -> coq_Terms -> coq_Terms -> __ -> coq_Term
    -> coq_Terms -> __ -> 'a1) -> (nat -> nat -> coq_Terms -> coq_Terms ->
    nat -> __ -> __ -> 'a1) -> nat -> nat -> coq_Terms -> coq_Terms ->
    coq_Term -> coq_R_etaExpand_aArgs -> 'a1

  val etaExpand_aArgs_rect :
    (coq_Terms -> coq_Term) -> (nat -> nat -> coq_Terms -> coq_Terms -> nat
    -> __ -> coq_Term -> coq_Terms -> __ -> 'a1 -> 'a1) -> (nat -> nat ->
    coq_Terms -> coq_Terms -> __ -> coq_Term -> coq_Terms -> __ -> 'a1) ->
    (nat -> nat -> coq_Terms -> coq_Terms -> nat -> __ -> __ -> 'a1) -> nat
    -> nat -> coq_Terms -> coq_Terms -> 'a1

  val etaExpand_aArgs_rec :
    (coq_Terms -> coq_Term) -> (nat -> nat -> coq_Terms -> coq_Terms -> nat
    -> __ -> coq_Term -> coq_Terms -> __ -> 'a1 -> 'a1) -> (nat -> nat ->
    coq_Terms -> coq_Terms -> __ -> coq_Term -> coq_Terms -> __ -> 'a1) ->
    (nat -> nat -> coq_Terms -> coq_Terms -> nat -> __ -> __ -> 'a1) -> nat
    -> nat -> coq_Terms -> coq_Terms -> 'a1

  val coq_R_etaExpand_aArgs_correct :
    (coq_Terms -> coq_Term) -> nat -> nat -> coq_Terms -> coq_Terms ->
    coq_Term -> coq_R_etaExpand_aArgs

  val etaExpand :
    (coq_Terms -> coq_Term) -> coq_Terms -> nat -> nat -> coq_Term

  type coq_R_etaExpand = Compile1.coq_R_etaExpand =
  | R_etaExpand_0 of coq_Terms * nat * nat * coq_Term * coq_Terms * nat
     * coq_Term * coq_R_etaExpand
  | R_etaExpand_1 of coq_Terms * nat * nat * nat
  | R_etaExpand_2 of coq_Terms * nat * nat * coq_Terms

  val coq_R_etaExpand_rect :
    (coq_Terms -> coq_Term) -> (coq_Terms -> nat -> nat -> coq_Term ->
    coq_Terms -> __ -> nat -> __ -> coq_Term -> coq_R_etaExpand -> 'a1 ->
    'a1) -> (coq_Terms -> nat -> nat -> __ -> nat -> __ -> 'a1) -> (coq_Terms
    -> nat -> nat -> coq_Terms -> __ -> __ -> __ -> 'a1) -> coq_Terms -> nat
    -> nat -> coq_Term -> coq_R_etaExpand -> 'a1

  val coq_R_etaExpand_rec :
    (coq_Terms -> coq_Term) -> (coq_Terms -> nat -> nat -> coq_Term ->
    coq_Terms -> __ -> nat -> __ -> coq_Term -> coq_R_etaExpand -> 'a1 ->
    'a1) -> (coq_Terms -> nat -> nat -> __ -> nat -> __ -> 'a1) -> (coq_Terms
    -> nat -> nat -> coq_Terms -> __ -> __ -> __ -> 'a1) -> coq_Terms -> nat
    -> nat -> coq_Term -> coq_R_etaExpand -> 'a1

  val etaExpand_rect :
    (coq_Terms -> coq_Term) -> (coq_Terms -> nat -> nat -> coq_Term ->
    coq_Terms -> __ -> nat -> __ -> 'a1 -> 'a1) -> (coq_Terms -> nat -> nat
    -> __ -> nat -> __ -> 'a1) -> (coq_Terms -> nat -> nat -> coq_Terms -> __
    -> __ -> __ -> 'a1) -> coq_Terms -> nat -> nat -> 'a1

  val etaExpand_rec :
    (coq_Terms -> coq_Term) -> (coq_Terms -> nat -> nat -> coq_Term ->
    coq_Terms -> __ -> nat -> __ -> 'a1 -> 'a1) -> (coq_Terms -> nat -> nat
    -> __ -> nat -> __ -> 'a1) -> (coq_Terms -> nat -> nat -> coq_Terms -> __
    -> __ -> __ -> 'a1) -> coq_Terms -> nat -> nat -> 'a1

  val coq_R_etaExpand_correct :
    (coq_Terms -> coq_Term) -> coq_Terms -> nat -> nat -> coq_Term ->
    coq_R_etaExpand

  val coq_CanonicalP :
    (coq_L1gTerm -> coq_Term) -> coq_L1gTerm -> coq_Term -> ((((coq_Terms ->
    coq_Term) * coq_Terms) * nat) * nat) option

  val strips : (coq_L1gTerm -> coq_Term) -> coq_L1gTerms -> coq_Terms

  type coq_R_strips = Compile1.coq_R_strips =
  | R_strips_0 of coq_L1gTerms
  | R_strips_1 of coq_L1gTerms * Compile0.coq_Term * Compile0.coq_Term list
     * coq_Terms * coq_R_strips

  val coq_R_strips_rect :
    (coq_L1gTerm -> coq_Term) -> (coq_L1gTerms -> __ -> 'a1) -> (coq_L1gTerms
    -> Compile0.coq_Term -> Compile0.coq_Term list -> __ -> coq_Terms ->
    coq_R_strips -> 'a1 -> 'a1) -> coq_L1gTerms -> coq_Terms -> coq_R_strips
    -> 'a1

  val coq_R_strips_rec :
    (coq_L1gTerm -> coq_Term) -> (coq_L1gTerms -> __ -> 'a1) -> (coq_L1gTerms
    -> Compile0.coq_Term -> Compile0.coq_Term list -> __ -> coq_Terms ->
    coq_R_strips -> 'a1 -> 'a1) -> coq_L1gTerms -> coq_Terms -> coq_R_strips
    -> 'a1

  val strips_rect :
    (coq_L1gTerm -> coq_Term) -> (coq_L1gTerms -> __ -> 'a1) -> (coq_L1gTerms
    -> Compile0.coq_Term -> Compile0.coq_Term list -> __ -> 'a1 -> 'a1) ->
    coq_L1gTerms -> 'a1

  val strips_rec :
    (coq_L1gTerm -> coq_Term) -> (coq_L1gTerms -> __ -> 'a1) -> (coq_L1gTerms
    -> Compile0.coq_Term -> Compile0.coq_Term list -> __ -> 'a1 -> 'a1) ->
    coq_L1gTerms -> 'a1

  val coq_R_strips_correct :
    (coq_L1gTerm -> coq_Term) -> coq_L1gTerms -> coq_Terms -> coq_R_strips

  val strip : coq_L1gTerm -> coq_Term

  val stripBs : coq_L1gBrs -> coq_Brs

  val stripDs : coq_L1gDefs -> coq_Defs

  type coq_R_strip = Compile1.coq_R_strip =
  | R_strip_0 of coq_L1gTerm * nat
  | R_strip_1 of coq_L1gTerm
  | R_strip_2 of coq_L1gTerm * name * Compile0.coq_Term * coq_Term
     * coq_R_strip
  | R_strip_3 of coq_L1gTerm * name * Compile0.coq_Term * Compile0.coq_Term
     * coq_Term * coq_R_strip * coq_Term * coq_R_strip
  | R_strip_4 of coq_L1gTerm * Compile0.coq_Term * Compile0.coq_Term
     * coq_Term * coq_R_strip * coq_Term * coq_R_strip
  | R_strip_5 of coq_L1gTerm * Compile0.coq_Term * Compile0.coq_Term
     * coq_Term * coq_R_strip * (coq_Terms -> coq_Term) * coq_Terms * 
     nat * nat
  | R_strip_6 of coq_L1gTerm * char list
  | R_strip_7 of coq_L1gTerm * inductive * nat * nat * nat
  | R_strip_8 of coq_L1gTerm * (inductive * nat) * Compile0.coq_Term
     * Compile0.coq_Brs * coq_Term * coq_R_strip * coq_Brs * coq_R_stripBs
  | R_strip_9 of coq_L1gTerm * Compile0.coq_Defs * nat * coq_Defs
     * coq_R_stripDs
  | R_strip_10 of coq_L1gTerm * inductive * nat * nat * Compile0.coq_Term
     * coq_Term * coq_R_strip
  | R_strip_11 of coq_L1gTerm * char list
  and coq_R_stripBs = Compile1.coq_R_stripBs =
  | R_stripBs_0 of coq_L1gBrs
  | R_stripBs_1 of coq_L1gBrs * nat * Compile0.coq_Term * Compile0.coq_Brs
     * coq_Term * coq_R_strip * coq_Brs * coq_R_stripBs
  and coq_R_stripDs = Compile1.coq_R_stripDs =
  | R_stripDs_0 of coq_L1gDefs
  | R_stripDs_1 of coq_L1gDefs * name * Compile0.coq_Term * nat
     * Compile0.coq_Defs * coq_Term * coq_R_strip * coq_Defs * coq_R_stripDs

  val coq_R_strip_rect :
    (coq_L1gTerm -> nat -> __ -> 'a1) -> (coq_L1gTerm -> __ -> 'a1) ->
    (coq_L1gTerm -> name -> Compile0.coq_Term -> __ -> coq_Term ->
    coq_R_strip -> 'a1 -> 'a1) -> (coq_L1gTerm -> name -> Compile0.coq_Term
    -> Compile0.coq_Term -> __ -> coq_Term -> coq_R_strip -> 'a1 -> coq_Term
    -> coq_R_strip -> 'a1 -> 'a1) -> (coq_L1gTerm -> Compile0.coq_Term ->
    Compile0.coq_Term -> __ -> coq_Term -> coq_R_strip -> 'a1 -> __ ->
    coq_Term -> coq_R_strip -> 'a1 -> 'a1) -> (coq_L1gTerm ->
    Compile0.coq_Term -> Compile0.coq_Term -> __ -> coq_Term -> coq_R_strip
    -> 'a1 -> (coq_Terms -> coq_Term) -> coq_Terms -> nat -> nat -> __ ->
    'a1) -> (coq_L1gTerm -> char list -> __ -> 'a1) -> (coq_L1gTerm ->
    inductive -> nat -> nat -> nat -> __ -> 'a1) -> (coq_L1gTerm ->
    (inductive * nat) -> Compile0.coq_Term -> Compile0.coq_Brs -> __ ->
    coq_Term -> coq_R_strip -> 'a1 -> coq_Brs -> coq_R_stripBs -> 'a1) ->
    (coq_L1gTerm -> Compile0.coq_Defs -> nat -> __ -> coq_Defs ->
    coq_R_stripDs -> 'a1) -> (coq_L1gTerm -> inductive -> nat -> nat ->
    Compile0.coq_Term -> __ -> coq_Term -> coq_R_strip -> 'a1 -> 'a1) ->
    (coq_L1gTerm -> char list -> __ -> 'a1) -> coq_L1gTerm -> coq_Term ->
    coq_R_strip -> 'a1

  val coq_R_strip_rec :
    (coq_L1gTerm -> nat -> __ -> 'a1) -> (coq_L1gTerm -> __ -> 'a1) ->
    (coq_L1gTerm -> name -> Compile0.coq_Term -> __ -> coq_Term ->
    coq_R_strip -> 'a1 -> 'a1) -> (coq_L1gTerm -> name -> Compile0.coq_Term
    -> Compile0.coq_Term -> __ -> coq_Term -> coq_R_strip -> 'a1 -> coq_Term
    -> coq_R_strip -> 'a1 -> 'a1) -> (coq_L1gTerm -> Compile0.coq_Term ->
    Compile0.coq_Term -> __ -> coq_Term -> coq_R_strip -> 'a1 -> __ ->
    coq_Term -> coq_R_strip -> 'a1 -> 'a1) -> (coq_L1gTerm ->
    Compile0.coq_Term -> Compile0.coq_Term -> __ -> coq_Term -> coq_R_strip
    -> 'a1 -> (coq_Terms -> coq_Term) -> coq_Terms -> nat -> nat -> __ ->
    'a1) -> (coq_L1gTerm -> char list -> __ -> 'a1) -> (coq_L1gTerm ->
    inductive -> nat -> nat -> nat -> __ -> 'a1) -> (coq_L1gTerm ->
    (inductive * nat) -> Compile0.coq_Term -> Compile0.coq_Brs -> __ ->
    coq_Term -> coq_R_strip -> 'a1 -> coq_Brs -> coq_R_stripBs -> 'a1) ->
    (coq_L1gTerm -> Compile0.coq_Defs -> nat -> __ -> coq_Defs ->
    coq_R_stripDs -> 'a1) -> (coq_L1gTerm -> inductive -> nat -> nat ->
    Compile0.coq_Term -> __ -> coq_Term -> coq_R_strip -> 'a1 -> 'a1) ->
    (coq_L1gTerm -> char list -> __ -> 'a1) -> coq_L1gTerm -> coq_Term ->
    coq_R_strip -> 'a1

  val coq_R_stripBs_rect :
    (coq_L1gBrs -> __ -> 'a1) -> (coq_L1gBrs -> nat -> Compile0.coq_Term ->
    Compile0.coq_Brs -> __ -> coq_Term -> coq_R_strip -> coq_Brs ->
    coq_R_stripBs -> 'a1 -> 'a1) -> coq_L1gBrs -> coq_Brs -> coq_R_stripBs ->
    'a1

  val coq_R_stripBs_rec :
    (coq_L1gBrs -> __ -> 'a1) -> (coq_L1gBrs -> nat -> Compile0.coq_Term ->
    Compile0.coq_Brs -> __ -> coq_Term -> coq_R_strip -> coq_Brs ->
    coq_R_stripBs -> 'a1 -> 'a1) -> coq_L1gBrs -> coq_Brs -> coq_R_stripBs ->
    'a1

  val coq_R_stripDs_rect :
    (coq_L1gDefs -> __ -> 'a1) -> (coq_L1gDefs -> name -> Compile0.coq_Term
    -> nat -> Compile0.coq_Defs -> __ -> coq_Term -> coq_R_strip -> coq_Defs
    -> coq_R_stripDs -> 'a1 -> 'a1) -> coq_L1gDefs -> coq_Defs ->
    coq_R_stripDs -> 'a1

  val coq_R_stripDs_rec :
    (coq_L1gDefs -> __ -> 'a1) -> (coq_L1gDefs -> name -> Compile0.coq_Term
    -> nat -> Compile0.coq_Defs -> __ -> coq_Term -> coq_R_strip -> coq_Defs
    -> coq_R_stripDs -> 'a1 -> 'a1) -> coq_L1gDefs -> coq_Defs ->
    coq_R_stripDs -> 'a1

  val strip_rect :
    (coq_L1gTerm -> nat -> __ -> 'a1) -> (coq_L1gTerm -> __ -> 'a1) ->
    (coq_L1gTerm -> name -> Compile0.coq_Term -> __ -> 'a1 -> 'a1) ->
    (coq_L1gTerm -> name -> Compile0.coq_Term -> Compile0.coq_Term -> __ ->
    'a1 -> 'a1 -> 'a1) -> (coq_L1gTerm -> Compile0.coq_Term ->
    Compile0.coq_Term -> __ -> 'a1 -> __ -> 'a1 -> 'a1) -> (coq_L1gTerm ->
    Compile0.coq_Term -> Compile0.coq_Term -> __ -> 'a1 -> (coq_Terms ->
    coq_Term) -> coq_Terms -> nat -> nat -> __ -> 'a1) -> (coq_L1gTerm ->
    char list -> __ -> 'a1) -> (coq_L1gTerm -> inductive -> nat -> nat -> nat
    -> __ -> 'a1) -> (coq_L1gTerm -> (inductive * nat) -> Compile0.coq_Term
    -> Compile0.coq_Brs -> __ -> 'a1 -> 'a1) -> (coq_L1gTerm ->
    Compile0.coq_Defs -> nat -> __ -> 'a1) -> (coq_L1gTerm -> inductive ->
    nat -> nat -> Compile0.coq_Term -> __ -> 'a1 -> 'a1) -> (coq_L1gTerm ->
    char list -> __ -> 'a1) -> coq_L1gTerm -> 'a1

  val strip_rec :
    (coq_L1gTerm -> nat -> __ -> 'a1) -> (coq_L1gTerm -> __ -> 'a1) ->
    (coq_L1gTerm -> name -> Compile0.coq_Term -> __ -> 'a1 -> 'a1) ->
    (coq_L1gTerm -> name -> Compile0.coq_Term -> Compile0.coq_Term -> __ ->
    'a1 -> 'a1 -> 'a1) -> (coq_L1gTerm -> Compile0.coq_Term ->
    Compile0.coq_Term -> __ -> 'a1 -> __ -> 'a1 -> 'a1) -> (coq_L1gTerm ->
    Compile0.coq_Term -> Compile0.coq_Term -> __ -> 'a1 -> (coq_Terms ->
    coq_Term) -> coq_Terms -> nat -> nat -> __ -> 'a1) -> (coq_L1gTerm ->
    char list -> __ -> 'a1) -> (coq_L1gTerm -> inductive -> nat -> nat -> nat
    -> __ -> 'a1) -> (coq_L1gTerm -> (inductive * nat) -> Compile0.coq_Term
    -> Compile0.coq_Brs -> __ -> 'a1 -> 'a1) -> (coq_L1gTerm ->
    Compile0.coq_Defs -> nat -> __ -> 'a1) -> (coq_L1gTerm -> inductive ->
    nat -> nat -> Compile0.coq_Term -> __ -> 'a1 -> 'a1) -> (coq_L1gTerm ->
    char list -> __ -> 'a1) -> coq_L1gTerm -> 'a1

  val stripBs_rect :
    (coq_L1gBrs -> __ -> 'a1) -> (coq_L1gBrs -> nat -> Compile0.coq_Term ->
    Compile0.coq_Brs -> __ -> 'a1 -> 'a1) -> coq_L1gBrs -> 'a1

  val stripBs_rec :
    (coq_L1gBrs -> __ -> 'a1) -> (coq_L1gBrs -> nat -> Compile0.coq_Term ->
    Compile0.coq_Brs -> __ -> 'a1 -> 'a1) -> coq_L1gBrs -> 'a1

  val stripDs_rect :
    (coq_L1gDefs -> __ -> 'a1) -> (coq_L1gDefs -> name -> Compile0.coq_Term
    -> nat -> Compile0.coq_Defs -> __ -> 'a1 -> 'a1) -> coq_L1gDefs -> 'a1

  val stripDs_rec :
    (coq_L1gDefs -> __ -> 'a1) -> (coq_L1gDefs -> name -> Compile0.coq_Term
    -> nat -> Compile0.coq_Defs -> __ -> 'a1 -> 'a1) -> coq_L1gDefs -> 'a1

  val coq_R_strip_correct : coq_L1gTerm -> coq_Term -> coq_R_strip

  val coq_R_stripBs_correct : coq_L1gBrs -> coq_Brs -> coq_R_stripBs

  val coq_R_stripDs_correct : coq_L1gDefs -> coq_Defs -> coq_R_stripDs

  val stripEC : coq_L1gEC -> coq_Term envClass

  type coq_R_stripEC = Compile1.coq_R_stripEC =
  | R_stripEC_0 of coq_L1gEC * coq_L1gTerm
  | R_stripEC_1 of coq_L1gEC * nat * itypPack

  val coq_R_stripEC_rect :
    (coq_L1gEC -> coq_L1gTerm -> __ -> 'a1) -> (coq_L1gEC -> nat -> itypPack
    -> __ -> 'a1) -> coq_L1gEC -> coq_Term envClass -> coq_R_stripEC -> 'a1

  val coq_R_stripEC_rec :
    (coq_L1gEC -> coq_L1gTerm -> __ -> 'a1) -> (coq_L1gEC -> nat -> itypPack
    -> __ -> 'a1) -> coq_L1gEC -> coq_Term envClass -> coq_R_stripEC -> 'a1

  val stripEC_rect :
    (coq_L1gEC -> coq_L1gTerm -> __ -> 'a1) -> (coq_L1gEC -> nat -> itypPack
    -> __ -> 'a1) -> coq_L1gEC -> 'a1

  val stripEC_rec :
    (coq_L1gEC -> coq_L1gTerm -> __ -> 'a1) -> (coq_L1gEC -> nat -> itypPack
    -> __ -> 'a1) -> coq_L1gEC -> 'a1

  val coq_R_stripEC_correct : coq_L1gEC -> coq_Term envClass -> coq_R_stripEC

  val stripEnv : coq_L1gEnv -> coq_Term environ

  val stripProgram : coq_L1gPgm -> coq_Term coq_Program

  val program_Program : coq_Fuel -> program -> coq_Term coq_Program
 end

val eta_expand : nat -> L3t.coq_Term -> L3t.coq_Term

val trans : L3t.coq_Term -> L3t.coq_Term

val trans_terms : L3t.coq_Terms -> L3t.coq_Terms

val trans_brs : inductive -> L3t.coq_Brs -> L3t.coq_Brs

val trans_fixes : L3t.coq_Defs -> L3t.coq_Defs

val transEC : L3t.coq_Term envClass -> L3t.coq_Term envClass

val transEnv : L3t.coq_Term environ -> L3t.coq_Term environ

val coq_Program_Program : L3t.coq_Term coq_Program -> L3t.coq_Term coq_Program

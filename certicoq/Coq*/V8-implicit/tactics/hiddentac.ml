(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id: hiddentac.ml 9952 2007-07-06 15:31:37Z letouzey $ *)

open Term
open Proof_type
open Tacmach

open Rawterm
open Refiner
open Genarg
open Tacexpr
open Tactics
open Util

let inj_id id = (dummy_loc,id)
let inj_open c = (Evd.empty,c)
let inj_open_wb (c,b) = ((Evd.empty,c),b)
let inj_ia = function
  | ElimOnConstr c -> ElimOnConstr (inj_open c)
  | ElimOnIdent id -> ElimOnIdent id
  | ElimOnAnonHyp n -> ElimOnAnonHyp n
let inj_occ (occ,c) = (occ,inj_open c)

(* Basic tactics *)
let h_intro_move x y =
  abstract_tactic (TacIntroMove (x, option_map inj_id y)) (intro_move x y)
let h_intro x        = h_intro_move (Some x) None
let h_intros_until x = abstract_tactic (TacIntrosUntil x) (intros_until x)
let h_assumption     = abstract_tactic TacAssumption assumption
let h_exact c        = abstract_tactic (TacExact (inj_open c)) (exact_check c)
let h_exact_no_check c =
  abstract_tactic (TacExactNoCheck (inj_open c)) (exact_no_check c)
let h_vm_cast_no_check c = 
  abstract_tactic (TacVmCastNoCheck (inj_open c)) (vm_cast_no_check c)
let h_apply ev cb    =
  abstract_tactic (TacApply (ev,inj_open_wb cb))
    (apply_with_ebindings_gen ev cb)
let h_elim cb cbo    =
  abstract_tactic (TacElim (inj_open_wb cb,option_map inj_open_wb cbo))
    (elim cb cbo)
let h_elim_type c    = abstract_tactic (TacElimType (inj_open c)) (elim_type c)
let h_case cb        = abstract_tactic (TacCase (inj_open_wb cb)) (general_case_analysis cb)
let h_case_type c    = abstract_tactic (TacCaseType (inj_open c)) (case_type c)
let h_fix ido n      = abstract_tactic (TacFix (ido,n)) (fix ido n)
let h_mutual_fix id n l =
  abstract_tactic
    (TacMutualFix (id,n,List.map (fun (id,n,c) -> (id,n,inj_open c)) l))
    (mutual_fix id n l)
let h_cofix ido      = abstract_tactic (TacCofix ido) (cofix ido)
let h_mutual_cofix id l =
  abstract_tactic
    (TacMutualCofix (id,List.map (fun (id,c) -> (id,inj_open c)) l)) 
    (mutual_cofix id l)

let h_cut imp c           =
  abstract_tactic (TacCut (imp,inj_open c)) (cut imp c)
let h_generalize imps cl  =
  abstract_tactic (TacGeneralize (imps,List.map inj_open cl))
    (generalize cl imps)
let h_generalize_dep imp c =
  abstract_tactic (TacGeneralizeDep (imp,inj_open c))(generalize_dep imp c)
let h_let_tac na imp c cl =
  abstract_tactic (TacLetTac (na,imp,inj_open c,cl))
    (letin_tac true na imp c cl)
let h_instantiate n c ido = 
(Evar_tactics.instantiate n c ido)
  (* abstract_tactic (TacInstantiate (n,c,cls))
    (Evar_refiner.instantiate n c (simple_clause_of cls)) *)

(* Derived basic tactics *)
let h_simple_induction h =
  abstract_tactic (TacSimpleInduction h) (simple_induct h)
let h_simple_destruct h  =
  abstract_tactic (TacSimpleDestruct h) (simple_destruct h)
let h_new_induction c e idl =
  abstract_tactic (TacNewInduction (List.map inj_ia c,option_map inj_open_wb e,idl))
    (new_induct c e idl)
let h_new_destruct c e idl =
  abstract_tactic (TacNewDestruct (List.map inj_ia c,option_map inj_open_wb e,idl))
    (new_destruct c e idl)
let h_specialize n d =
  abstract_tactic (TacSpecialize (n,inj_open_wb d)) (new_hyp n d)
let h_lapply imp c =
  abstract_tactic (TacLApply (imp,inj_open c)) (cut_and_apply imp c)

(* Context management *)
let h_clear b l = abstract_tactic (TacClear (b,l))
  ((if b then keep else clear) l)
let h_clear_body l = abstract_tactic (TacClearBody l) (clear_body l)
let h_move dep id1 id2 =
  abstract_tactic (TacMove (dep,id1,id2)) (move_hyp dep id1 id2)
let h_rename l =
  abstract_tactic (TacRename l) (rename_hyp l)

(* Constructors *)
let h_left l    = abstract_tactic (TacLeft l) (left_with_ebindings l)
let h_right l   = abstract_tactic (TacLeft l) (right_with_ebindings l)
let h_split l   = abstract_tactic (TacSplit (false,l)) (split_with_ebindings l)
(* Moved to tacinterp because of dependence in Tacinterp.interp
let h_any_constructor t =
  abstract_tactic (TacAnyConstructor t) (any_constructor t)
*)
let h_constructor n l =
  abstract_tactic (TacConstructor(AI n,l))(constructor_tac None n l)
let h_one_constructor n = h_constructor n NoBindings
let h_simplest_left   = h_left NoBindings
let h_simplest_right  = h_right NoBindings

(* Conversion *)
let h_reduce r cl  = 
  abstract_tactic (TacReduce (inj_red_expr r,cl)) (reduce r cl)
let h_change oc c cl =
  abstract_tactic (TacChange (option_map inj_occ oc,inj_open c,cl))
    (change (option_map Redexpr.out_with_occurrences oc) c cl)

(* Equivalence relations *)
let h_reflexivity    = abstract_tactic TacReflexivity intros_reflexivity
let h_symmetry c     = abstract_tactic (TacSymmetry c) (intros_symmetry c)
let h_transitivity c =
  abstract_tactic (TacTransitivity (inj_open c)) (intros_transitivity c)

let h_simplest_apply c  = h_apply false (c,NoBindings)
let h_simplest_eapply c = h_apply true (c,NoBindings)
let h_simplest_elim c   = h_elim (c,NoBindings) None
let h_simplest_case   c = h_case (c,NoBindings)

let h_intro_patterns l = abstract_tactic (TacIntroPattern l) (intro_patterns l)


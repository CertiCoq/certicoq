Require Import Arith.
From CertiCoq.L1g Require Import compile.
From CertiCoq.Plugin Require Import CertiCoq.

Definition demo0 := true.

MetaCoq Erase demo0.
CertiCoq Compile demo0.

Definition demo1 := andb (negb true) true.
CertiCoq Compile demo1.

(* Definition demo1 := List.repeat true 5. *)

(* Definition demo1 := List.app (List.repeat true 5) (List.repeat false 3). *)

(* Quote Recursively Definition demo1q := demo1. *)

(* Definition erase p := *)
(*   let p := SafeTemplateChecker.fix_program_universes p in *)
(*   SafeTemplateErasure.erase_template_program p. *)

(* Definition check_erase p := *)
(*   match erase p with *)
(*   | PCUICSafeChecker.CorrectDecl _ => true *)
(*   | PCUICSafeChecker.EnvError _ => false *)
(*   end. *)

(* Goal exists t, check_erase demo1q = t. *)
(*   eexists. *)
(*   unfold erase. simpl. unfold check_erase.  *)
(*   match goal with *)
(*     | [ |- ?x = ?y ] => let x' := eval cbn in x in convert_concl_no_check (x' = y) *)
(*   end. *)

(*     match goal with *)
(*   | [ |- context C [ SafeTemplateChecker.fix_global_env_universes ?t ] ] => *)
(*     let t' := eval vm_compute in (SafeTemplateChecker.fix_global_env_universes t) in *)
(*     let goal' := context C [ t' ] in *)
(*     convert_concl_no_check goal' *)
(*   end. *)
(*   simpl. *)
(*   unfold SafeTemplateErasure.erase_template_program. *)
(*     unfold monad_utils.bind. *)
(*   unfold PCUICSafeChecker.envcheck_monad. *)
(*   match goal with *)
(*   | [ |- context C [ TemplateToPCUIC.trans_global ?t ] ] => *)
(*     let t' := eval vm_compute in (TemplateToPCUIC.trans_global t) in *)
(*     let goal' := context C [ t' ] in *)
(*     convert_concl_no_check goal' *)
(*   end. *)
(*   unfold SafeTemplateErasure.check_wf_env_only_univs. cbv beta iota fix zeta delta [List.rev List.app fst snd]. *)
(*   cbv beta iota fix zeta delta [monad_utils.bind monad_utils.ret PCUICSafeChecker.envcheck_monad *)
(*                                                PCUICSafeChecker.check_fresh *)
(*                                                PCUICSafeChecker.check_udecl *)
(*                                                PCUICTyping.global_decl_ident *)
(*                   ]. *)
(*   cbv beta iota fix zeta delta [monad_utils.bind monad_utils.ret PCUICSafeChecker.envcheck_monad *)
(*                                                PCUICSafeChecker.check_eq_true *)
(*                                                PCUICTyping.levels_of_udecl *)
(*                                                PCUICTyping.universes_decl_of_decl *)
(*                                                Universes.LevelSet.for_all *)
(*                                                PCUICTyping.on_udecl_decl *)
(*                                                Universes.LevelSet.Raw.for_all *)
(*                                                Universes.LevelSet.this *)
(*                                                PCUICTyping.constraints_of_udecl *)
(*                                                Universes.AUContext.repr *)
(*                                                PCUICAst.ind_universes fst snd *)
(*                                                uGraph.gc_of_uctx *)
(*                                                PCUICSafeChecker.uctx_of_udecl *)

(*                                                Universes.ConstraintSet.for_all *)
(*                                                Universes.ConstraintSet.Raw.for_all *)
(*                                                Universes.ConstraintSet.this *)
(* monad_utils.option_monad uGraph.no_prop_levels *)
(*                     uGraph.gc_of_constraints *)
(*                     Universes.LevelSet.fold *)
(*                     Universes.LevelSet.Raw.fold *)
(*                     Universes.ConstraintSet.fold *)
(*                     Universes.ConstraintSet.Raw.fold *)
(*                     List.fold_left Basics.flip uGraph.add_gc_of_constraint *)
(*                   ]. *)
(*   match goal with *)
(*   | [ |- context C [ uGraph.wGraph.is_acyclic ?t ] ] => *)
(*     let t' := eval vm_compute in (uGraph.wGraph.is_acyclic t) in *)
(*     let goal' := context C [ t' ] in *)
(*     convert_concl_no_check goal' *)
(*   end. *)
(*   cbv beta iota fix zeta delta [monad_utils.bind monad_utils.ret PCUICSafeChecker.envcheck_monad *)
(*                                                PCUICSafeChecker.check_eq_true *)
(*                                                PCUICTyping.levels_of_udecl *)
(*                                                PCUICTyping.universes_decl_of_decl *)
(*                                                Universes.LevelSet.for_all *)
(*                                                PCUICTyping.on_udecl_decl *)
(*                                                Universes.LevelSet.Raw.for_all *)
(*                                                Universes.LevelSet.this *)
(*                                                PCUICTyping.constraints_of_udecl *)
(*                                                Universes.AUContext.repr *)
(*                                                PCUICAst.ind_universes fst snd *)
(*                                                uGraph.gc_of_uctx *)
(*                                                PCUICSafeChecker.uctx_of_udecl *)

(*                                                Universes.ConstraintSet.for_all *)
(*                                                Universes.ConstraintSet.Raw.for_all *)
(*                                                Universes.ConstraintSet.this *)
(* monad_utils.option_monad uGraph.no_prop_levels *)
(*                     uGraph.gc_of_constraints *)
(*                     Universes.LevelSet.fold *)
(*                     Universes.LevelSet.Raw.fold *)
(*                     Universes.ConstraintSet.fold *)
(*                     Universes.ConstraintSet.Raw.fold *)
(*                     List.fold_left Basics.flip uGraph.add_gc_of_constraint *)
(*                   ]. *)
(*   unfold SafeTemplateErasure.assume_wf_decl. *)
(*   cbv beta iota fix zeta delta [monad_utils.bind monad_utils.ret PCUICSafeChecker.envcheck_monad *)
(*                                                PCUICSafeChecker.check_eq_true *)
(*                                                PCUICTyping.levels_of_udecl *)
(*                                                PCUICTyping.universes_decl_of_decl *)
(*                                                Universes.LevelSet.for_all *)
(*                                                PCUICTyping.on_udecl_decl *)
(*                                                Universes.LevelSet.Raw.for_all *)
(*                                                Universes.LevelSet.this *)
(*                                                PCUICTyping.constraints_of_udecl *)
(*                                                Universes.AUContext.repr *)
(*                                                PCUICAst.ind_universes fst snd *)
(*                                                uGraph.gc_of_uctx *)
(*                                                PCUICSafeChecker.uctx_of_udecl *)

(*                                                Universes.ConstraintSet.for_all *)
(*                                                Universes.ConstraintSet.Raw.for_all *)
(*                                                Universes.ConstraintSet.this *)
(* monad_utils.option_monad uGraph.no_prop_levels *)
(*                     uGraph.gc_of_constraints *)
(*                     Universes.LevelSet.fold *)
(*                     Universes.LevelSet.Raw.fold *)
(*                     Universes.ConstraintSet.fold *)
(*                     Universes.ConstraintSet.Raw.fold *)
(*                     List.fold_left Basics.flip uGraph.add_gc_of_constraint *)
(*                     AstUtils.eq_constant AstUtils.eq_string utils.string_compare]. *)
(*   cbv. *)
(*   cbv beta zeta iota. *)

(* CertiCoq Compile demo1. *)

Definition demo2 := (negb, List.hd_error).

CertiCoq Compile demo2.

From CertiCoq.Benchmarks Require Import vs.
Import VeriStar.
Definition is_valid :=
  match main with
  | Valid => true
  | _ => false
  end.

Time CertiCoq Compile is_valid. (* 5 secs ! *)
(* Now 0.3s but probably compiling TWrong *)

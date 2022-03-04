Require Import L2k.compile.
Require Import L2k.wcbvEval.
Require Import L2k.term.
Require Import Common.Common Common.compM Common.Pipeline_utils.
From ExtLib Require Import Monads.


Require Import Common.Common Common.classes Common.Pipeline_utils Common.compM.
From ExtLib Require Import Monads.
From MetaCoq.Template Require Import utils Typing.
Import MonadNotation.

(* 
Definition erase_PCUIC : CertiCoqTrans Ast.Env.program (global_context * term) :=
  fun src =>
    debug_msg "Translating from Template to Lbox" ;;
    (LiftErrorCertiCoqTrans "Lbox" L1g.compile.erase src).

(* Expose the top-level transformation function *)
Definition compile_L1g : CertiCoqTrans (global_context * term) (Program Term) :=
  fun src =>
    debug_msg "Translating from Lbox to L1" ;;
    (LiftCertiCoqTrans "L1g" L1g.compile.program_Program src).




#[global] Instance L1g_Lang : Lang (Program Term) :=
  { Value := Term;
    TermWf := fun P => match P with
                      mkPgm trm env => WFapp trm /\ program.WFaEnv env
                    end;
    BigStep := fun s sv => WcbvEval (env s) (main s) sv
  }.
 *)

 Definition wf_program (p : Ast.Env.program) := 
  ∥ ∑ T, @Typing.typing 
    config.extraction_checker_flags
    (Ast.Env.empty_ext p.1)
    [] p.2 T ∥.

Definition template_bigstep (p : Ast.Env.program) (v : Ast.term) : Prop :=
  ∥ Template.WcbvEval.eval p.1 p.2 v ∥.
 
 #[export] Instance Template_Lang : Lang Ast.Env.program :=
  { Value := Ast.term;
    TermWf := wf_program ;
    BigStep := template_bigstep }. 

Import MonadNotation.

Instance L2k_Lang : Lang (Program L2k.compile.Term) :=
  { Value := Term;
    TermWf := fun P => L2k.program.crctTerm (AstCommon.env P) 0 (main P);
    BigStep := fun s sv => WcbvEval (env s) (main s) sv
  }.

Definition compile_L2k
  : CertiCoqTrans (Ast.Env.program) (Program L2k.compile.Term) :=
  fun src =>
    debug_msg "Translating from L1g to L1k" ;;
    (LiftCertiCoqTrans "L2k" compile_program src).

Goal compile_program = compile_program.
Proof.
  unfold compile_program.
  unfold Erasure.erase_program.
  unfold Erasure.expand_program.
  unfold Erasure.erasure_pipeline.


1/1
(fun p : Ast.Env.program =>
 {|
   main :=
     compile
       (Erasure.Transform.run
          (Erasure.Transform.compose
             (Erasure.Transform.compose
                (Erasure.Transform.compose
                   (Erasure.Transform.compose
                      Erasure.template_to_pcuic_transform
                      Erasure.pcuic_expand_lets_transform
                      (fun (p0 : Erasure.pcuic_program)
                         (H : Erasure.Transform.post
                                Erasure.template_to_pcuic_transform p0) =>
                       Erasure.erasure_pipeline_obligation_1 p0 H))
                   Erasure.erase_transform
                   (fun (p0 : Erasure.pcuic_program)
                      (H : Erasure.Transform.post
                             (Erasure.Transform.compose
                                Erasure.template_to_pcuic_transform
                                Erasure.pcuic_expand_lets_transform
                                (fun (p1 : Erasure.pcuic_program)
                                   (H : Erasure.Transform.post
                                          Erasure.template_to_pcuic_transform
                                          p1) =>
                                 Erasure.erasure_pipeline_obligation_1 p1 H))
                             p0) =>
                    Erasure.erasure_pipeline_obligation_2 p0 H))
                (Erasure.remove_params_optimization
                   EWcbvEval.default_wcbv_flags)
                (fun (p0 : Erasure.eprogram_env)
                   (_ : Erasure.Transform.post
                          (Erasure.Transform.compose
                             (Erasure.Transform.compose
                                Erasure.template_to_pcuic_transform
                                Erasure.pcuic_expand_lets_transform
                                (fun (p1 : Erasure.pcuic_program)
                                   (H : Erasure.Transform.post
                                          Erasure.template_to_pcuic_transform
                                          p1) =>
                                 Erasure.erasure_pipeline_obligation_1 p1 H))
                             Erasure.erase_transform
                             (fun (p1 : Erasure.pcuic_program)
                                (H : Erasure.Transform.post
                                       (Erasure.Transform.compose
                                          Erasure.template_to_pcuic_transform
                                          Erasure.pcuic_expand_lets_transform
                                          (fun (p2 : Erasure.pcuic_program)
                                             (H : 
                                              Erasure.Transform.post
                                                Erasure.template_to_pcuic_transform
                                                p2) =>
                                           Erasure.erasure_pipeline_obligation_1
                                             p2 H)) p1) =>
                              Erasure.erasure_pipeline_obligation_2 p1 H)) p0)
                 => Erasure.erasure_pipeline_obligation_3 p0))
             Erasure.optimize_prop_discr_optimization
             (fun (p0 : Erasure.eprogram)
                (H : Erasure.Transform.post
                       (Erasure.Transform.compose
                          (Erasure.Transform.compose
                             (Erasure.Transform.compose
                                Erasure.template_to_pcuic_transform
                                Erasure.pcuic_expand_lets_transform
                                (fun (p1 : Erasure.pcuic_program)
                                   (H : Erasure.Transform.post
                                          Erasure.template_to_pcuic_transform
                                          p1) =>
                                 Erasure.erasure_pipeline_obligation_1 p1 H))
                             Erasure.erase_transform
                             (fun (p1 : Erasure.pcuic_program)
                                (H : Erasure.Transform.post
                                       (Erasure.Transform.compose
                                          Erasure.template_to_pcuic_transform
                                          Erasure.pcuic_expand_lets_transform
                                          (fun (p2 : Erasure.pcuic_program)
                                             (H : 
                                              Erasure.Transform.post
                                                Erasure.template_to_pcuic_transform
                                                p2) =>
                                           Erasure.erasure_pipeline_obligation_1
                                             p2 H)) p1) =>
                              Erasure.erasure_pipeline_obligation_2 p1 H))
                          (Erasure.remove_params_optimization
                             EWcbvEval.default_wcbv_flags)
                          (fun (p1 : Erasure.eprogram_env)
                             (_ : Erasure.Transform.post
                                    (Erasure.Transform.compose
                                       (Erasure.Transform.compose
                                          Erasure.template_to_pcuic_transform
                                          Erasure.pcuic_expand_lets_transform
                                          (fun (p2 : Erasure.pcuic_program)
                                             (H : 
                                              Erasure.Transform.post
                                                Erasure.template_to_pcuic_transform
                                                p2) =>
                                           Erasure.erasure_pipeline_obligation_1
                                             p2 H)) Erasure.erase_transform
                                       (fun (p2 : Erasure.pcuic_program)
                                          (H : Erasure.Transform.post
                                                 (Erasure.Transform.compose
                                                 Erasure.template_to_pcuic_transform
                                                 Erasure.pcuic_expand_lets_transform
                                                 (fun
                                                 (p3 : Erasure.pcuic_program)
                                                 (H : 
                                                 Erasure.Transform.post
                                                 Erasure.template_to_pcuic_transform
                                                 p3) =>
                                                 Erasure.erasure_pipeline_obligation_1
                                                 p3 H)) p2) =>
                                        Erasure.erasure_pipeline_obligation_2
                                          p2 H)) p1) =>
                           Erasure.erasure_pipeline_obligation_3 p1)) p0) =>
              Erasure.erasure_pipeline_obligation_4 p0 H))
          (Erasure.expand_program p) (todo "wf_env and welltyped term")).2;
   env :=
     compile_ctx
       (Erasure.Transform.run
          (Erasure.Transform.compose
             (Erasure.Transform.compose
                (Erasure.Transform.compose
                   (Erasure.Transform.compose
                      Erasure.template_to_pcuic_transform
                      Erasure.pcuic_expand_lets_transform
                      (fun (p0 : Erasure.pcuic_program)
                         (H : Erasure.Transform.post
                                Erasure.template_to_pcuic_transform p0) =>
                       Erasure.erasure_pipeline_obligation_1 p0 H))
                   Erasure.erase_transform
                   (fun (p0 : Erasure.pcuic_program)
                      (H : Erasure.Transform.post
                             (Erasure.Transform.compose
                                Erasure.template_to_pcuic_transform
                                Erasure.pcuic_expand_lets_transform
                                (fun (p1 : Erasure.pcuic_program)
                                   (H : Erasure.Transform.post
                                          Erasure.template_to_pcuic_transform
                                          p1) =>
                                 Erasure.erasure_pipeline_obligation_1 p1 H))
                             p0) =>
                    Erasure.erasure_pipeline_obligation_2 p0 H))
                (Erasure.remove_params_optimization
                   EWcbvEval.default_wcbv_flags)
                (fun (p0 : Erasure.eprogram_env)
                   (_ : Erasure.Transform.post
                          (Erasure.Transform.compose
                             (Erasure.Transform.compose
                                Erasure.template_to_pcuic_transform
                                Erasure.pcuic_expand_lets_transform
                                (fun (p1 : Erasure.pcuic_program)
                                   (H : Erasure.Transform.post
                                          Erasure.template_to_pcuic_transform
                                          p1) =>
                                 Erasure.erasure_pipeline_obligation_1 p1 H))
                             Erasure.erase_transform
                             (fun (p1 : Erasure.pcuic_program)
                                (H : Erasure.Transform.post
                                       (Erasure.Transform.compose
                                          Erasure.template_to_pcuic_transform
                                          Erasure.pcuic_expand_lets_transform
                                          (fun (p2 : Erasure.pcuic_program)
                                             (H : 
                                              Erasure.Transform.post
                                                Erasure.template_to_pcuic_transform
                                                p2) =>
                                           Erasure.erasure_pipeline_obligation_1
                                             p2 H)) p1) =>
                              Erasure.erasure_pipeline_obligation_2 p1 H)) p0)
                 => Erasure.erasure_pipeline_obligation_3 p0))
             Erasure.optimize_prop_discr_optimization
             (fun (p0 : Erasure.eprogram)
                (H : Erasure.Transform.post
                       (Erasure.Transform.compose
                          (Erasure.Transform.compose
                             (Erasure.Transform.compose
                                Erasure.template_to_pcuic_transform
                                Erasure.pcuic_expand_lets_transform
                                (fun (p1 : Erasure.pcuic_program)
                                   (H : Erasure.Transform.post
                                          Erasure.template_to_pcuic_transform
                                          p1) =>
                                 Erasure.erasure_pipeline_obligation_1 p1 H))
                             Erasure.erase_transform
                             (fun (p1 : Erasure.pcuic_program)
                                (H : Erasure.Transform.post
                                       (Erasure.Transform.compose
                                          Erasure.template_to_pcuic_transform
                                          Erasure.pcuic_expand_lets_transform
                                          (fun (p2 : Erasure.pcuic_program)
                                             (H : 
                                              Erasure.Transform.post
                                                Erasure.template_to_pcuic_transform
                                                p2) =>
                                           Erasure.erasure_pipeline_obligation_1
                                             p2 H)) p1) =>
                              Erasure.erasure_pipeline_obligation_2 p1 H))
                          (Erasure.remove_params_optimization
                             EWcbvEval.default_wcbv_flags)
                          (fun (p1 : Erasure.eprogram_env)
                             (_ : Erasure.Transform.post
                                    (Erasure.Transform.compose
                                       (Erasure.Transform.compose
                                          Erasure.template_to_pcuic_transform
                                          Erasure.pcuic_expand_lets_transform
                                          (fun (p2 : Erasure.pcuic_program)
                                             (H : 
                                              Erasure.Transform.post
                                                Erasure.template_to_pcuic_transform
                                                p2) =>
                                           Erasure.erasure_pipeline_obligation_1
                                             p2 H)) Erasure.erase_transform
                                       (fun (p2 : Erasure.pcuic_program)
                                          (H : Erasure.Transform.post
                                                 (Erasure.Transform.compose
                                                 Erasure.template_to_pcuic_transform
                                                 Erasure.pcuic_expand_lets_transform
                                                 (fun
                                                 (p3 : Erasure.pcuic_program)
                                                 (H : 
                                                 Erasure.Transform.post
                                                 Erasure.template_to_pcuic_transform
                                                 p3) =>
                                                 Erasure.erasure_pipeline_obligation_1
                                                 p3 H)) p2) =>
                                        Erasure.erasure_pipeline_obligation_2
                                          p2 H)) p1) =>
                           Erasure.erasure_pipeline_obligation_3 p1)) p0) =>
              Erasure.erasure_pipeline_obligation_4 p0 H))
          (Erasure.expand_program p) (todo "wf_env and welltyped term")).1
 |}) =
(fun p : Ast.Env.program =>
 {|
   main :=
     compile
       (Erasure.Transform.run
          (Erasure.Transform.compose
             (Erasure.Transform.compose
                (Erasure.Transform.compose
                   (Erasure.Transform.compose
                      Erasure.template_to_pcuic_transform
                      Erasure.pcuic_expand_lets_transform
                      (fun (p0 : Erasure.pcuic_program)
                         (H : Erasure.Transform.post
                                Erasure.template_to_pcuic_transform p0) =>
                       Erasure.erasure_pipeline_obligation_1 p0 H))
                   Erasure.erase_transform
                   (fun (p0 : Erasure.pcuic_program)
                      (H : Erasure.Transform.post
                             (Erasure.Transform.compose
                                Erasure.template_to_pcuic_transform
                                Erasure.pcuic_expand_lets_transform
                                (fun (p1 : Erasure.pcuic_program)
                                   (H : Erasure.Transform.post
                                          Erasure.template_to_pcuic_transform
                                          p1) =>
                                 Erasure.erasure_pipeline_obligation_1 p1 H))
                             p0) =>
                    Erasure.erasure_pipeline_obligation_2 p0 H))
                (Erasure.remove_params_optimization
                   EWcbvEval.default_wcbv_flags)
                (fun (p0 : Erasure.eprogram_env)
                   (_ : Erasure.Transform.post
                          (Erasure.Transform.compose
                             (Erasure.Transform.compose
                                Erasure.template_to_pcuic_transform
                                Erasure.pcuic_expand_lets_transform
                                (fun (p1 : Erasure.pcuic_program)
                                   (H : Erasure.Transform.post
                                          Erasure.template_to_pcuic_transform
                                          p1) =>
                                 Erasure.erasure_pipeline_obligation_1 p1 H))
                             Erasure.erase_transform
                             (fun (p1 : Erasure.pcuic_program)
                                (H : Erasure.Transform.post
                                       (Erasure.Transform.compose
                                          Erasure.template_to_pcuic_transform
                                          Erasure.pcuic_expand_lets_transform
                                          (fun (p2 : Erasure.pcuic_program)
                                             (H : 
                                              Erasure.Transform.post
                                                Erasure.template_to_pcuic_transform
                                                p2) =>
                                           Erasure.erasure_pipeline_obligation_1
                                             p2 H)) p1) =>
                              Erasure.erasure_pipeline_obligation_2 p1 H)) p0)
                 => Erasure.erasure_pipeline_obligation_3 p0))
             Erasure.optimize_prop_discr_optimization
             (fun (p0 : Erasure.eprogram)
                (H : Erasure.Transform.post
                       (Erasure.Transform.compose
                          (Erasure.Transform.compose
                             (Erasure.Transform.compose
                                Erasure.template_to_pcuic_transform
                                Erasure.pcuic_expand_lets_transform
                                (fun (p1 : Erasure.pcuic_program)
                                   (H : Erasure.Transform.post
                                          Erasure.template_to_pcuic_transform
                                          p1) =>
                                 Erasure.erasure_pipeline_obligation_1 p1 H))
                             Erasure.erase_transform
                             (fun (p1 : Erasure.pcuic_program)
                                (H : Erasure.Transform.post
                                       (Erasure.Transform.compose
                                          Erasure.template_to_pcuic_transform
                                          Erasure.pcuic_expand_lets_transform
                                          (fun (p2 : Erasure.pcuic_program)
                                             (H : 
                                              Erasure.Transform.post
                                                Erasure.template_to_pcuic_transform
                                                p2) =>
                                           Erasure.erasure_pipeline_obligation_1
                                             p2 H)) p1) =>
                              Erasure.erasure_pipeline_obligation_2 p1 H))
                          (Erasure.remove_params_optimization
                             EWcbvEval.default_wcbv_flags)
                          (fun (p1 : Erasure.eprogram_env)
                             (_ : Erasure.Transform.post
                                    (Erasure.Transform.compose
                                       (Erasure.Transform.compose
                                          Erasure.template_to_pcuic_transform
                                          Erasure.pcuic_expand_lets_transform
                                          (fun (p2 : Erasure.pcuic_program)
                                             (H : 
                                              Erasure.Transform.post
                                                Erasure.template_to_pcuic_transform
                                                p2) =>
                                           Erasure.erasure_pipeline_obligation_1
                                             p2 H)) Erasure.erase_transform
                                       (fun (p2 : Erasure.pcuic_program)
                                          (H : Erasure.Transform.post
                                                 (Erasure.Transform.compose
                                                 Erasure.template_to_pcuic_transform
                                                 Erasure.pcuic_expand_lets_transform
                                                 (fun
                                                 (p3 : Erasure.pcuic_program)
                                                 (H : 
                                                 Erasure.Transform.post
                                                 Erasure.template_to_pcuic_transform
                                                 p3) =>
                                                 Erasure.erasure_pipeline_obligation_1
                                                 p3 H)) p2) =>
                                        Erasure.erasure_pipeline_obligation_2
                                          p2 H)) p1) =>
                           Erasure.erasure_pipeline_obligation_3 p1)) p0) =>
              Erasure.erasure_pipeline_obligation_4 p0 H))
          (Erasure.expand_program p) (todo "wf_env and welltyped term")).2;
   env :=
     compile_ctx
       (Erasure.Transform.run
          (Erasure.Transform.compose
             (Erasure.Transform.compose
                (Erasure.Transform.compose
                   (Erasure.Transform.compose
                      Erasure.template_to_pcuic_transform
                      Erasure.pcuic_expand_lets_transform
                      (fun (p0 : Erasure.pcuic_program)
                         (H : Erasure.Transform.post
                                Erasure.template_to_pcuic_transform p0) =>
                       Erasure.erasure_pipeline_obligation_1 p0 H))
                   Erasure.erase_transform
                   (fun (p0 : Erasure.pcuic_program)
                      (H : Erasure.Transform.post
                             (Erasure.Transform.compose
                                Erasure.template_to_pcuic_transform
                                Erasure.pcuic_expand_lets_transform
                                (fun (p1 : Erasure.pcuic_program)
                                   (H : Erasure.Transform.post
                                          Erasure.template_to_pcuic_transform
                                          p1) =>
                                 Erasure.erasure_pipeline_obligation_1 p1 H))
                             p0) =>
                    Erasure.erasure_pipeline_obligation_2 p0 H))
                (Erasure.remove_params_optimization
                   EWcbvEval.default_wcbv_flags)
                (fun (p0 : Erasure.eprogram_env)
                   (_ : Erasure.Transform.post
                          (Erasure.Transform.compose
                             (Erasure.Transform.compose
                                Erasure.template_to_pcuic_transform
                                Erasure.pcuic_expand_lets_transform
                                (fun (p1 : Erasure.pcuic_program)
                                   (H : Erasure.Transform.post
                                          Erasure.template_to_pcuic_transform
                                          p1) =>
                                 Erasure.erasure_pipeline_obligation_1 p1 H))
                             Erasure.erase_transform
                             (fun (p1 : Erasure.pcuic_program)
                                (H : Erasure.Transform.post
                                       (Erasure.Transform.compose
                                          Erasure.template_to_pcuic_transform
                                          Erasure.pcuic_expand_lets_transform
                                          (fun (p2 : Erasure.pcuic_program)
                                             (H : 
                                              Erasure.Transform.post
                                                Erasure.template_to_pcuic_transform
                                                p2) =>
                                           Erasure.erasure_pipeline_obligation_1
                                             p2 H)) p1) =>
                              Erasure.erasure_pipeline_obligation_2 p1 H)) p0)
                 => Erasure.erasure_pipeline_obligation_3 p0))
             Erasure.optimize_prop_discr_optimization
             (fun (p0 : Erasure.eprogram)
                (H : Erasure.Transform.post
                       (Erasure.Transform.compose
                          (Erasure.Transform.compose
                             (Erasure.Transform.compose
                                Erasure.template_to_pcuic_transform
                                Erasure.pcuic_expand_lets_transform
                                (fun (p1 : Erasure.pcuic_program)
                                   (H : Erasure.Transform.post
                                          Erasure.template_to_pcuic_transform
                                          p1) =>
                                 Erasure.erasure_pipeline_obligation_1 p1 H))
                             Erasure.erase_transform
                             (fun (p1 : Erasure.pcuic_program)
                                (H : Erasure.Transform.post
                                       (Erasure.Transform.compose
                                          Erasure.template_to_pcuic_transform
                                          Erasure.pcuic_expand_lets_transform
                                          (fun (p2 : Erasure.pcuic_program)
                                             (H : 
                                              Erasure.Transform.post
                                                Erasure.template_to_pcuic_transform
                                                p2) =>
                                           Erasure.erasure_pipeline_obligation_1
                                             p2 H)) p1) =>
                              Erasure.erasure_pipeline_obligation_2 p1 H))
                          (Erasure.remove_params_optimization
                             EWcbvEval.default_wcbv_flags)
                          (fun (p1 : Erasure.eprogram_env)
                             (_ : Erasure.Transform.post
                                    (Erasure.Transform.compose
                                       (Erasure.Transform.compose
                                          Erasure.template_to_pcuic_transform
                                          Erasure.pcuic_expand_lets_transform
                                          (fun (p2 : Erasure.pcuic_program)
                                             (H : 
                                              Erasure.Transform.post
                                                Erasure.template_to_pcuic_transform
                                                p2) =>
                                           Erasure.erasure_pipeline_obligation_1
                                             p2 H)) Erasure.erase_transform
                                       (fun (p2 : Erasure.pcuic_program)
                                          (H : Erasure.Transform.post
                                                 (Erasure.Transform.compose
                                                 Erasure.template_to_pcuic_transform
                                                 Erasure.pcuic_expand_lets_transform
                                                 (fun
                                                 (p3 : Erasure.pcuic_program)
                                                 (H : 
                                                 Erasure.Transform.post
                                                 Erasure.template_to_pcuic_transform
                                                 p3) =>
                                                 Erasure.erasure_pipeline_obligation_1
                                                 p3 H)) p2) =>
                                        Erasure.erasure_pipeline_obligation_2
                                          p2 H)) p1) =>
                           Erasure.erasure_pipeline_obligation_3 p1)) p0) =>
              Erasure.erasure_pipeline_obligation_4 p0 H))
          (Erasure.expand_program p) (todo "wf_env and welltyped term")).1
 |})
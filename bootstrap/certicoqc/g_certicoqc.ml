let _ = Mltop.add_known_module "coq-certicoqc.plugin"

# 5 "g_certicoqc.mlg"
 
open Pp
open Certicoqc
open Ltac_plugin
open Stdarg
open Pcoq.Prim
open Plugin_utils
open Certicoq
open Tacarg
open G_certicoq_vanilla


let () = Vernacextend.static_vernac_extend ~plugin:(Some "coq-certicoqc.plugin") ~command:"CertiCoqCCompile" ~classifier:(fun _ -> Vernacextend.classify_as_query) ?entry:None 
         [(Vernacextend.TyML (false, Vernacextend.TyTerminal ("CertiCoqC", 
                                     Vernacextend.TyTerminal ("Compile", 
                                     Vernacextend.TyNonTerminal (Extend.TUlist0 (
                                                                 Extend.TUentry (Genarg.get_arg_tag wit_vanilla_cargs)), 
                                     Vernacextend.TyNonTerminal (Extend.TUentry (Genarg.get_arg_tag wit_global), 
                                     Vernacextend.TyNil)))), (let coqpp_body l
                                                             gr
                                                             () = Vernactypes.vtdefault (fun () -> 
                                                                  
# 18 "g_certicoqc.mlg"
                                                                 
    let gr = Nametab.global gr in
    let opts = make_options l [] (get_name gr) in
    Certicoqc.compile_only opts gr []
  
                                                                  ) in fun l
                                                             gr ?loc ~atts ()
                                                             -> coqpp_body l
                                                             gr
                                                             (Attributes.unsupported_attributes atts)), None));
         (Vernacextend.TyML (false, Vernacextend.TyTerminal ("CertiCoqC", 
                                    Vernacextend.TyTerminal ("Compile", 
                                    Vernacextend.TyNonTerminal (Extend.TUlist0 (
                                                                Extend.TUentry (Genarg.get_arg_tag wit_vanilla_cargs)), 
                                    Vernacextend.TyNonTerminal (Extend.TUentry (Genarg.get_arg_tag wit_global), 
                                    Vernacextend.TyTerminal ("Extract", 
                                    Vernacextend.TyTerminal ("Constants", 
                                    Vernacextend.TyTerminal ("[", Vernacextend.TyNonTerminal (
                                                                  Extend.TUlist0sep (
                                                                  Extend.TUentry (Genarg.get_arg_tag wit_vanilla_extract_cnst), ","), 
                                                                  Vernacextend.TyTerminal ("]", 
                                                                  Vernacextend.TyTerminal ("Include", 
                                                                  Vernacextend.TyTerminal ("[", 
                                                                  Vernacextend.TyNonTerminal (
                                                                  Extend.TUlist0sep (
                                                                  Extend.TUentry (Genarg.get_arg_tag wit_vanilla_cinclude), ","), 
                                                                  Vernacextend.TyTerminal ("]", 
                                                                  Vernacextend.TyNil))))))))))))), 
         (let coqpp_body l gr cs imps
         () = Vernactypes.vtdefault (fun () -> 
# 23 "g_certicoqc.mlg"
                                                                                                                                                                                             
    let gr = Nametab.global gr in
    let opts = make_options l cs (get_name gr) in
    Certicoqc.compile_only opts gr imps
  
              ) in fun l
         gr cs imps ?loc ~atts () -> coqpp_body l gr cs imps
         (Attributes.unsupported_attributes atts)), None));
         (Vernacextend.TyML (false, Vernacextend.TyTerminal ("CertiCoqC", 
                                    Vernacextend.TyTerminal ("Run", Vernacextend.TyNonTerminal (
                                                                    Extend.TUlist0 (
                                                                    Extend.TUentry (Genarg.get_arg_tag wit_vanilla_cargs)), 
                                                                    Vernacextend.TyNonTerminal (
                                                                    Extend.TUentry (Genarg.get_arg_tag wit_global), 
                                                                    Vernacextend.TyTerminal ("Extract", 
                                                                    Vernacextend.TyTerminal ("Constants", 
                                                                    Vernacextend.TyTerminal ("[", 
                                                                    Vernacextend.TyNonTerminal (
                                                                    Extend.TUlist0sep (
                                                                    Extend.TUentry (Genarg.get_arg_tag wit_vanilla_extract_cnst), ","), 
                                                                    Vernacextend.TyTerminal ("]", 
                                                                    Vernacextend.TyTerminal ("Include", 
                                                                    Vernacextend.TyTerminal ("[", 
                                                                    Vernacextend.TyNonTerminal (
                                                                    Extend.TUlist0sep (
                                                                    Extend.TUentry (Genarg.get_arg_tag wit_vanilla_cinclude), ","), 
                                                                    Vernacextend.TyTerminal ("]", 
                                                                    Vernacextend.TyNil))))))))))))), 
         (let coqpp_body l gr cs imps
         () = Vernactypes.vtdefault (fun () -> 
# 28 "g_certicoqc.mlg"
                                                                                                                                                                                         
  let gr = Nametab.global gr in
  let opts = make_options l cs (get_name gr) in
  Certicoqc.compile_C opts gr imps
  
              ) in fun l
         gr cs imps ?loc ~atts () -> coqpp_body l gr cs imps
         (Attributes.unsupported_attributes atts)), None));
         (Vernacextend.TyML (false, Vernacextend.TyTerminal ("CertiCoqC", 
                                    Vernacextend.TyTerminal ("Run", Vernacextend.TyNonTerminal (
                                                                    Extend.TUlist0 (
                                                                    Extend.TUentry (Genarg.get_arg_tag wit_vanilla_cargs)), 
                                                                    Vernacextend.TyNonTerminal (
                                                                    Extend.TUentry (Genarg.get_arg_tag wit_global), 
                                                                    Vernacextend.TyNil)))), 
         (let coqpp_body l gr
         () = Vernactypes.vtdefault (fun () -> 
# 33 "g_certicoqc.mlg"
                                                             
  let gr = Nametab.global gr in
  let opts = make_options l [] (get_name gr) in
  Certicoqc.compile_C opts gr []
  
              ) in fun l
         gr ?loc ~atts () -> coqpp_body l gr
         (Attributes.unsupported_attributes atts)), None));
         (Vernacextend.TyML (false, Vernacextend.TyTerminal ("CertiCoqC", 
                                    Vernacextend.TyTerminal ("Show", 
                                    Vernacextend.TyTerminal ("IR", Vernacextend.TyNonTerminal (
                                                                   Extend.TUlist0 (
                                                                   Extend.TUentry (Genarg.get_arg_tag wit_vanilla_cargs)), 
                                                                   Vernacextend.TyNonTerminal (
                                                                   Extend.TUentry (Genarg.get_arg_tag wit_global), 
                                                                   Vernacextend.TyNil))))), 
         (let coqpp_body l gr
         () = Vernactypes.vtdefault (fun () -> 
# 38 "g_certicoqc.mlg"
                                                                   
    let gr = Nametab.global gr in
    let opts = make_options l [] (get_name gr) in
    Certicoqc.show_ir opts gr
  
              ) in fun l
         gr ?loc ~atts () -> coqpp_body l gr
         (Attributes.unsupported_attributes atts)), None));
         (Vernacextend.TyML (false, Vernacextend.TyTerminal ("CertiCoqC", 
                                    Vernacextend.TyTerminal ("Show", 
                                    Vernacextend.TyTerminal ("IR", Vernacextend.TyNonTerminal (
                                                                   Extend.TUlist0 (
                                                                   Extend.TUentry (Genarg.get_arg_tag wit_vanilla_cargs)), 
                                                                   Vernacextend.TyNonTerminal (
                                                                   Extend.TUentry (Genarg.get_arg_tag wit_global), 
                                                                   Vernacextend.TyTerminal ("Extract", 
                                                                   Vernacextend.TyTerminal ("Constants", 
                                                                   Vernacextend.TyTerminal ("[", 
                                                                   Vernacextend.TyNonTerminal (
                                                                   Extend.TUlist0sep (
                                                                   Extend.TUentry (Genarg.get_arg_tag wit_vanilla_extract_cnst), ","), 
                                                                   Vernacextend.TyTerminal ("]", 
                                                                   Vernacextend.TyNil)))))))))), 
         (let coqpp_body l gr cs
         () = Vernactypes.vtdefault (fun () -> 
# 43 "g_certicoqc.mlg"
                                                                                                                                        
    let gr = Nametab.global gr in
    let opts = make_options l cs (get_name gr) in
    Certicoqc.show_ir opts gr
  
              ) in fun l
         gr cs ?loc ~atts () -> coqpp_body l gr cs
         (Attributes.unsupported_attributes atts)), None));
         (Vernacextend.TyML (false, Vernacextend.TyTerminal ("CertiCoqC", 
                                    Vernacextend.TyTerminal ("FFI", Vernacextend.TyNonTerminal (
                                                                    Extend.TUlist0 (
                                                                    Extend.TUentry (Genarg.get_arg_tag wit_vanilla_ffiargs)), 
                                                                    Vernacextend.TyNonTerminal (
                                                                    Extend.TUentry (Genarg.get_arg_tag wit_global), 
                                                                    Vernacextend.TyNil)))), 
         (let coqpp_body l gr
         () = Vernactypes.vtdefault (fun () -> 
# 48 "g_certicoqc.mlg"
                                                               
    let gr = Nametab.global gr in
    let opts = make_options l [] "" in
    Certicoqc.ffi_command opts gr
  
              ) in fun l
         gr ?loc ~atts () -> coqpp_body l gr
         (Attributes.unsupported_attributes atts)), None));
         (Vernacextend.TyML (false, Vernacextend.TyTerminal ("CertiCoqC", 
                                    Vernacextend.TyTerminal ("Generate", 
                                    Vernacextend.TyTerminal ("Glue", 
                                    Vernacextend.TyNonTerminal (Extend.TUlist0 (
                                                                Extend.TUentry (Genarg.get_arg_tag wit_vanilla_glueargs)), 
                                    Vernacextend.TyTerminal ("[", Vernacextend.TyNonTerminal (
                                                                  Extend.TUlist0sep (
                                                                  Extend.TUentry (Genarg.get_arg_tag wit_global), ","), 
                                                                  Vernacextend.TyTerminal ("]", 
                                                                  Vernacextend.TyNil))))))), 
         (let coqpp_body l grs
         () = Vernactypes.vtdefault (fun () -> 
# 53 "g_certicoqc.mlg"
                                                                                                   
    let grs = List.map Nametab.global grs in
    let opts = make_options l [] "" in
    Certicoqc.glue_command opts grs
  
              ) in fun l
         grs ?loc ~atts () -> coqpp_body l grs
         (Attributes.unsupported_attributes atts)), None));
         (Vernacextend.TyML (false, Vernacextend.TyTerminal ("CertiCoqC", 
                                    Vernacextend.TyTerminal ("-help", 
                                    Vernacextend.TyNil)), (let coqpp_body () = 
                                                          Vernactypes.vtdefault (fun () -> 
                                                          
# 58 "g_certicoqc.mlg"
                              
    Feedback.msg_info (str help_msg)
  
                                                          ) in fun ?loc ~atts ()
                                                          -> coqpp_body (Attributes.unsupported_attributes atts)), None))]

let () = Vernacextend.static_vernac_extend ~plugin:(Some "coq-certicoqc.plugin") ~command:"CertiCoqC_Eval" ~classifier:(fun _ -> Vernacextend.classify_as_sideeff) ?entry:None 
         [(Vernacextend.TyML (false, Vernacextend.TyTerminal ("CertiCoqC", 
                                     Vernacextend.TyTerminal ("Eval", 
                                     Vernacextend.TyNonTerminal (Extend.TUlist0 (
                                                                 Extend.TUentry (Genarg.get_arg_tag wit_vanilla_cargs)), 
                                     Vernacextend.TyNonTerminal (Extend.TUentry (Genarg.get_arg_tag wit_global), 
                                     Vernacextend.TyTerminal ("Extract", 
                                     Vernacextend.TyTerminal ("Constants", 
                                     Vernacextend.TyTerminal ("[", Vernacextend.TyNonTerminal (
                                                                   Extend.TUlist0sep (
                                                                   Extend.TUentry (Genarg.get_arg_tag wit_vanilla_extract_cnst), ","), 
                                                                   Vernacextend.TyTerminal ("]", 
                                                                   Vernacextend.TyTerminal ("Include", 
                                                                   Vernacextend.TyTerminal ("[", 
                                                                   Vernacextend.TyNonTerminal (
                                                                   Extend.TUlist0sep (
                                                                   Extend.TUentry (Genarg.get_arg_tag wit_vanilla_cinclude), ","), 
                                                                   Vernacextend.TyTerminal ("]", 
                                                                   Vernacextend.TyNil))))))))))))), 
         (let coqpp_body l gr cs imps
         () = Vernactypes.vtdefault (fun () -> 
# 65 "g_certicoqc.mlg"
                                                                                                                                                                                          
  let gr = Nametab.global gr in
  let opts = Certicoq.make_options l cs (get_name gr) in
  let result = Certicoq.eval_gr opts gr imps in 
  Feedback.msg_notice Pp.(str" = " ++ Printer.pr_constr_env (Global.env ()) Evd.empty result)
  
              ) in fun l
         gr cs imps ?loc ~atts () -> coqpp_body l gr cs imps
         (Attributes.unsupported_attributes atts)), None));
         (Vernacextend.TyML (false, Vernacextend.TyTerminal ("CertiCoqC", 
                                    Vernacextend.TyTerminal ("Eval", 
                                    Vernacextend.TyNonTerminal (Extend.TUlist0 (
                                                                Extend.TUentry (Genarg.get_arg_tag wit_vanilla_cargs)), 
                                    Vernacextend.TyNonTerminal (Extend.TUentry (Genarg.get_arg_tag wit_global), 
                                    Vernacextend.TyNil)))), (let coqpp_body l
                                                            gr
                                                            () = Vernactypes.vtdefault (fun () -> 
                                                                 
# 71 "g_certicoqc.mlg"
                                                              
  let gr = Nametab.global gr in
  let opts = Certicoq.make_options l [] (get_name gr) in
  let result = Certicoq.eval_gr opts gr [] in
  Feedback.msg_notice Pp.(str" = " ++ Printer.pr_constr_env (Global.env ()) Evd.empty result)
  
                                                                 ) in fun l
                                                            gr ?loc ~atts ()
                                                            -> coqpp_body l
                                                            gr
                                                            (Attributes.unsupported_attributes atts)), None))]

let () = Tacentries.tactic_extend "coq-certicoqc.plugin" "CertiCoqc_eval" ~level:0 
         [(Tacentries.TyML (Tacentries.TyIdent ("certicoqc_eval", Tacentries.TyArg (
                                                                  Extend.TUlist0 (
                                                                  Extend.TUentry (Genarg.get_arg_tag wit_vanilla_cargs)), 
                                                                  Tacentries.TyArg (
                                                                  Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                                                  Tacentries.TyArg (
                                                                  Extend.TUentry (Genarg.get_arg_tag wit_tactic), 
                                                                  Tacentries.TyNil)))), 
           (fun l c tac ist -> 
# 81 "g_certicoqc.mlg"
    (* quote and evaluate the given term, unquote, pass the result to t *)
    Proofview.Goal.enter begin fun gl ->
      let env = Proofview.Goal.env gl in
      let sigma = Proofview.Goal.sigma gl in
      let opts = Certicoq.make_options l [] "goal" in
      let opts = Certicoq.{ opts with toplevel_name = "goal" } in
      let c' = Certicoq.eval opts env sigma c [] in 
      ltac_apply tac (List.map to_ltac_val [EConstr.of_constr c'])
  end 
           )))]


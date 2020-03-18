let __coq_plugin_name = "certicoq_plugin"
let _ = Mltop.add_known_module __coq_plugin_name

# 5 "g_certicoq.mlg"
 
open Stdarg


let () = Vernacextend.vernac_extend ~command:"CertiCoq_Compile" ~classifier:(fun _ -> Vernacextend.classify_as_query) ?entry:None 
         [(Vernacextend.TyML (false, Vernacextend.TyTerminal ("CertiCoq", 
                                     Vernacextend.TyTerminal ("Compile", 
                                     Vernacextend.TyNonTerminal (Extend.TUentry (Genarg.get_arg_tag wit_global), 
                                     Vernacextend.TyNil))), (let coqpp_body gr
                                                            () ~st = 
                                                            let () = 
                                                            
# 10 "g_certicoq.mlg"
                                          
    let gr = Nametab.global gr in
    Certicoq.compile gr
  
                                                             in st in fun gr
                                                            ~atts ~st
                                                            -> coqpp_body gr
                                                            (Attributes.unsupported_attributes atts) ~st), None))]


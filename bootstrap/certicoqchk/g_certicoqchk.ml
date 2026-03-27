let _ = Mltop.add_known_module "coq-certicoqchk.plugin"

# 5 "g_certicoqchk.mlg"
 
open Pp
open Ltac_plugin
open Stdarg
open Pcoq.Prim
open Plugin_utils
open Certicoq
open G_certicoq_vanilla


let () = Vernacextend.static_vernac_extend ~plugin:(Some "coq-certicoqchk.plugin") ~command:"CertiCoqCheck" ~classifier:(fun _ -> Vernacextend.classify_as_query) ?entry:None 
         [(Vernacextend.TyML (false, Vernacextend.TyTerminal ("CertiCoqCheck", 
                                     Vernacextend.TyNonTerminal (Extend.TUentry (Genarg.get_arg_tag wit_global), 
                                     Vernacextend.TyNil)), (let coqpp_body gr
                                                           () = Vernactypes.vtdefault (fun () -> 
                                                                
# 16 "g_certicoqchk.mlg"
                                     
    let gr = Nametab.global gr in
    Certicoqchk.check gr
  
                                                                ) in fun gr
                                                           ?loc ~atts ()
                                                           -> coqpp_body gr
                                                           (Attributes.unsupported_attributes atts)), None))]


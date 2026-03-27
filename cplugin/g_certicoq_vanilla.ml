let _ = Mltop.add_known_module "coq-certicoq-vanilla.plugin"

# 5 "g_certicoq_vanilla.mlg"
 
open Pp
open Certicoq
open Ltac_plugin
open Stdarg
open Pcoq.Prim
open Plugin_utils
open Tacexpr
open Tacinterp
open Stdarg
open Tacarg
open Genredexpr

(** Calling Ltac **)

let ltac_lcall tac args =
  let (location, name) = Loc.tag (Names.Id.of_string tac)
    (* Loc.tag @@ Names.Id.of_string tac *)
  in
  CAst.make ?loc:location (Tacexpr.TacArg(Tacexpr.TacCall
                              (CAst.make (Locus.ArgVar (CAst.make ?loc:location name),args))))


let ltac_apply (f : Value.t) (args: Tacinterp.Value.t list) =
  let fold arg (i, vars, lfun) =
    let id = Names.Id.of_string ("x" ^ string_of_int i) in
    let (l,n) = (Loc.tag id) in
    let x = Reference (Locus.ArgVar (CAst.make ?loc:l n)) in
    (succ i, x :: vars, Names.Id.Map.add id arg lfun)
  in
  let (_, args, lfun) = List.fold_right fold args (0, [], Names.Id.Map.empty) in
  let lfun = Names.Id.Map.add (Names.Id.of_string "F") f lfun in
  let ist = { (Tacinterp.default_ist ()) with Tacinterp.lfun = lfun; } in
  Tacinterp.eval_tactic_ist ist (ltac_lcall "F" args)

let to_ltac_val c = Tacinterp.Value.of_constr c

let globref_of_qualid ?loc (gr : Libnames.qualid) : Names.GlobRef.t  =
  match Constrintern.locate_reference gr with
  | None -> CErrors.user_err ?loc Pp.(Libnames.pr_qualid gr ++ str " not found.")
  | Some g -> g

let quoted_globref_of_qualid ~loc (gr : Libnames.qualid) : Metacoq_template_plugin.Kernames.global_reference =
  Metacoq_template_plugin.Ast_quoter.quote_global_reference (globref_of_qualid ~loc gr)

let inductive_of_qualid ~loc (gr : Libnames.qualid) : Kernames.inductive =
  let open Metacoq_template_plugin in
  match quoted_globref_of_qualid ~loc gr with
  | Kernames.ConstRef kn -> CErrors.user_err ~loc Pp.(str "Expected an inductive name but found a constant.")
  | Kernames.VarRef(v) -> CErrors.user_err ~loc Pp.(str "Expected an inductive name but found a variable.")
  | Kernames.IndRef(i) -> (Obj.magic i)
  | Kernames.ConstructRef(_, _) -> CErrors.user_err ~loc Pp.(str "Expected an inductive name but found a constructor.")


let (wit_vanilla_cargs, vanilla_cargs) = Tacentries.argument_extend ~plugin:"coq-certicoq-vanilla.plugin" ~name:"vanilla_cargs" 
                                         {
                                         Tacentries.arg_parsing = Vernacextend.Arg_rules (
                                                                  [(Pcoq.Production.make
                                                                    (Pcoq.Rule.next 
                                                                    (Pcoq.Rule.next 
                                                                    (Pcoq.Rule.stop)
                                                                    ((Pcoq.Symbol.token (Pcoq.terminal "-toplevel_name"))))
                                                                    ((Pcoq.Symbol.nterm string)))
                                                                    (fun s _
                                                                    loc -> 
                                                                    
# 75 "g_certicoq_vanilla.mlg"
                                      TOPLEVEL_NAME(s) 
                                                                    ));
                                                                  (Pcoq.Production.make
                                                                   (Pcoq.Rule.next 
                                                                   (Pcoq.Rule.next 
                                                                   (Pcoq.Rule.stop)
                                                                   ((Pcoq.Symbol.token (Pcoq.terminal "-file"))))
                                                                   ((Pcoq.Symbol.nterm string)))
                                                                   (fun s _
                                                                   loc -> 
                                                                   
# 74 "g_certicoq_vanilla.mlg"
                             FILENAME(s) 
                                                                   ));
                                                                  (Pcoq.Production.make
                                                                   (Pcoq.Rule.next 
                                                                   (Pcoq.Rule.next 
                                                                   (Pcoq.Rule.stop)
                                                                   ((Pcoq.Symbol.token (Pcoq.terminal "-ext"))))
                                                                   ((Pcoq.Symbol.nterm string)))
                                                                   (fun s _
                                                                   loc -> 
                                                                   
# 73 "g_certicoq_vanilla.mlg"
                            EXT(s) 
                                                                   ));
                                                                  (Pcoq.Production.make
                                                                   (Pcoq.Rule.next 
                                                                   (Pcoq.Rule.next 
                                                                   (Pcoq.Rule.stop)
                                                                   ((Pcoq.Symbol.token (Pcoq.terminal "-dev"))))
                                                                   ((Pcoq.Symbol.nterm natural)))
                                                                   (fun n _
                                                                   loc -> 
                                                                   
# 72 "g_certicoq_vanilla.mlg"
                             DEV(n) 
                                                                   ));
                                                                  (Pcoq.Production.make
                                                                   (Pcoq.Rule.next 
                                                                   (Pcoq.Rule.next 
                                                                   (Pcoq.Rule.stop)
                                                                   ((Pcoq.Symbol.token (Pcoq.terminal "-build_dir"))))
                                                                   ((Pcoq.Symbol.nterm string)))
                                                                   (fun s _
                                                                   loc -> 
                                                                   
# 71 "g_certicoq_vanilla.mlg"
                                  BUILDDIR(s) 
                                                                   ));
                                                                  (Pcoq.Production.make
                                                                   (Pcoq.Rule.next 
                                                                   (Pcoq.Rule.next 
                                                                   (Pcoq.Rule.stop)
                                                                   ((Pcoq.Symbol.token (Pcoq.terminal "-config"))))
                                                                   ((Pcoq.Symbol.nterm natural)))
                                                                   (fun n _
                                                                   loc -> 
                                                                   
# 69 "g_certicoq_vanilla.mlg"
                                ANFCONFIG(n) 
                                                                   ));
                                                                  (Pcoq.Production.make
                                                                   (Pcoq.Rule.next 
                                                                   (Pcoq.Rule.next 
                                                                   (Pcoq.Rule.stop)
                                                                   ((Pcoq.Symbol.token (Pcoq.terminal "-args"))))
                                                                   ((Pcoq.Symbol.nterm natural)))
                                                                   (fun n _
                                                                   loc -> 
                                                                   
# 68 "g_certicoq_vanilla.mlg"
                              ARGS(n) 
                                                                   ));
                                                                  (Pcoq.Production.make
                                                                   (Pcoq.Rule.next 
                                                                   (Pcoq.Rule.stop)
                                                                   ((Pcoq.Symbol.token (Pcoq.terminal "-debug"))))
                                                                   (fun _
                                                                   loc -> 
                                                                   
# 67 "g_certicoq_vanilla.mlg"
                    DEBUG 
                                                                   ));
                                                                  (Pcoq.Production.make
                                                                   (Pcoq.Rule.next 
                                                                   (Pcoq.Rule.next 
                                                                   (Pcoq.Rule.stop)
                                                                   ((Pcoq.Symbol.token (Pcoq.terminal "-O"))))
                                                                   ((Pcoq.Symbol.nterm natural)))
                                                                   (fun n _
                                                                   loc -> 
                                                                   
# 66 "g_certicoq_vanilla.mlg"
                           OPT(n) 
                                                                   ));
                                                                  (Pcoq.Production.make
                                                                   (Pcoq.Rule.next 
                                                                   (Pcoq.Rule.stop)
                                                                   ((Pcoq.Symbol.token (Pcoq.terminal "-time_anf"))))
                                                                   (fun _
                                                                   loc -> 
                                                                   
# 65 "g_certicoq_vanilla.mlg"
                       TIMEANF 
                                                                   ));
                                                                  (Pcoq.Production.make
                                                                   (Pcoq.Rule.next 
                                                                   (Pcoq.Rule.stop)
                                                                   ((Pcoq.Symbol.token (Pcoq.terminal "-time"))))
                                                                   (fun _
                                                                   loc -> 
                                                                   
# 64 "g_certicoq_vanilla.mlg"
                   TIME 
                                                                   ));
                                                                  (Pcoq.Production.make
                                                                   (Pcoq.Rule.next 
                                                                   (Pcoq.Rule.stop)
                                                                   ((Pcoq.Symbol.token (Pcoq.terminal "-cps"))))
                                                                   (fun _
                                                                   loc -> 
                                                                   
# 63 "g_certicoq_vanilla.mlg"
                  CPS 
                                                                   ));
                                                                  (Pcoq.Production.make
                                                                   (Pcoq.Rule.next 
                                                                   (Pcoq.Rule.stop)
                                                                   ((Pcoq.Symbol.token (Pcoq.terminal "-bypass_qed"))))
                                                                   (fun _
                                                                   loc -> 
                                                                   
# 62 "g_certicoq_vanilla.mlg"
                         BYPASS_QED 
                                                                   ));
                                                                  (Pcoq.Production.make
                                                                   (Pcoq.Rule.next 
                                                                   (Pcoq.Rule.stop)
                                                                   ((Pcoq.Symbol.token (Pcoq.terminal "-unsafe-erasure"))))
                                                                   (fun _
                                                                   loc -> 
                                                                   
# 61 "g_certicoq_vanilla.mlg"
                             UNSAFE_ERASURE 
                                                                   ));
                                                                  (Pcoq.Production.make
                                                                   (Pcoq.Rule.next 
                                                                   (Pcoq.Rule.stop)
                                                                   ((Pcoq.Symbol.token (Pcoq.terminal "-typed-erasure"))))
                                                                   (fun _
                                                                   loc -> 
                                                                   
# 60 "g_certicoq_vanilla.mlg"
                            TYPED_ERASURE 
                                                                   ))]);
                                         Tacentries.arg_tag = None;
                                         Tacentries.arg_intern = Tacentries.ArgInternFun (fun ist v -> (ist, v));
                                         Tacentries.arg_subst = Tacentries.ArgSubstFun (fun s v -> v);
                                         Tacentries.arg_interp = Tacentries.ArgInterpRet;
                                         Tacentries.arg_printer = ((fun env sigma -> fun _ _ _ _ -> Pp.str "missing printer"), (fun env sigma -> fun _ _ _ _ -> Pp.str "missing printer"), (fun env sigma -> fun _ _ _ _ -> Pp.str "missing printer"));
                                         }
let _ = (wit_vanilla_cargs, vanilla_cargs)

let (wit_vanilla_extract_cnst, vanilla_extract_cnst) = Vernacextend.vernac_argument_extend ~plugin:"coq-certicoq-vanilla.plugin" ~name:"vanilla_extract_cnst" 
                                                       {
                                                       Vernacextend.arg_parsing = 
                                                       Vernacextend.Arg_rules (
                                                       [(Pcoq.Production.make
                                                         (Pcoq.Rule.next 
                                                         (Pcoq.Rule.next 
                                                         (Pcoq.Rule.next 
                                                         (Pcoq.Rule.next 
                                                         (Pcoq.Rule.next 
                                                         (Pcoq.Rule.stop)
                                                         ((Pcoq.Symbol.nterm reference)))
                                                         ((Pcoq.Symbol.token (Pcoq.terminal "=>"))))
                                                         ((Pcoq.Symbol.nterm string)))
                                                         ((Pcoq.Symbol.token (Pcoq.terminal "with"))))
                                                         ((Pcoq.Symbol.token (Pcoq.terminal "tinfo"))))
                                                         (fun _ _ str _ gr
                                                         loc -> 
# 81 "g_certicoq_vanilla.mlg"
                                                         (extract_constant (Option.get (Constrintern.locate_reference gr)) str, true) 
                                                                ));
                                                       (Pcoq.Production.make
                                                        (Pcoq.Rule.next 
                                                        (Pcoq.Rule.next 
                                                        (Pcoq.Rule.next 
                                                        (Pcoq.Rule.stop)
                                                        ((Pcoq.Symbol.nterm reference)))
                                                        ((Pcoq.Symbol.token (Pcoq.terminal "=>"))))
                                                        ((Pcoq.Symbol.nterm string)))
                                                        (fun str _ gr loc ->
                                                        
# 80 "g_certicoq_vanilla.mlg"
                                          (extract_constant (Option.get (Constrintern.locate_reference gr)) str, false) 
                                                        ))]);
                                                       Vernacextend.arg_printer = fun env sigma -> 
                                                       fun _ -> Pp.str "missing printer";
                                                       }
let _ = (wit_vanilla_extract_cnst, vanilla_extract_cnst)

let (wit_vanilla_ffiargs, vanilla_ffiargs) = Vernacextend.vernac_argument_extend ~plugin:"coq-certicoq-vanilla.plugin" ~name:"vanilla_ffiargs" 
                                             {
                                             Vernacextend.arg_parsing = 
                                             Vernacextend.Arg_rules (
                                             [(Pcoq.Production.make
                                               (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                               ((Pcoq.Symbol.nterm vanilla_cargs)))
                                               (fun c loc -> 
# 87 "g_certicoq_vanilla.mlg"
                            c 
                                                             ));
                                             (Pcoq.Production.make
                                              (Pcoq.Rule.next (Pcoq.Rule.next 
                                                              (Pcoq.Rule.stop)
                                                              ((Pcoq.Symbol.token (Pcoq.terminal "-prefix"))))
                                                              ((Pcoq.Symbol.nterm string)))
                                              (fun s _ loc -> 
# 86 "g_certicoq_vanilla.mlg"
                               PREFIX(s) 
                                                              ))]);
                                             Vernacextend.arg_printer = fun env sigma -> 
                                             fun _ -> Pp.str "missing printer";
                                             }
let _ = (wit_vanilla_ffiargs, vanilla_ffiargs)

let (wit_vanilla_glueargs, vanilla_glueargs) = Vernacextend.vernac_argument_extend ~plugin:"coq-certicoq-vanilla.plugin" ~name:"vanilla_glueargs" 
                                               {
                                               Vernacextend.arg_parsing = 
                                               Vernacextend.Arg_rules (
                                               [(Pcoq.Production.make
                                                 (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Pcoq.terminal "-file"))))
                                                                 ((Pcoq.Symbol.nterm string)))
                                                 (fun s _ loc -> 
# 94 "g_certicoq_vanilla.mlg"
                             FILENAME(s) 
                                                                 ));
                                               (Pcoq.Production.make
                                                (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                (Pcoq.Rule.stop)
                                                                ((Pcoq.Symbol.token (Pcoq.terminal "-args"))))
                                                                ((Pcoq.Symbol.nterm natural)))
                                                (fun n _ loc -> 
# 93 "g_certicoq_vanilla.mlg"
                              ARGS(n) 
                                                                ));
                                               (Pcoq.Production.make
                                                (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                ((Pcoq.Symbol.token (Pcoq.terminal "-debug"))))
                                                (fun _ loc -> 
# 92 "g_certicoq_vanilla.mlg"
                    DEBUG 
                                                              ));
                                               (Pcoq.Production.make
                                                (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                ((Pcoq.Symbol.token (Pcoq.terminal "-cps"))))
                                                (fun _ loc -> 
# 91 "g_certicoq_vanilla.mlg"
                  CPS 
                                                              ))]);
                                               Vernacextend.arg_printer = fun env sigma -> 
                                               fun _ -> Pp.str "missing printer";
                                               }
let _ = (wit_vanilla_glueargs, vanilla_glueargs)

let (wit_vanilla_cinclude, vanilla_cinclude) = Vernacextend.vernac_argument_extend ~plugin:"coq-certicoq-vanilla.plugin" ~name:"vanilla_cinclude" 
                                               {
                                               Vernacextend.arg_parsing = 
                                               Vernacextend.Arg_rules (
                                               [(Pcoq.Production.make
                                                 (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Pcoq.terminal "Library"))))
                                                                 ((Pcoq.Symbol.nterm string)))
                                                                 ((Pcoq.Symbol.opt (Pcoq.Symbol.nterm string))))
                                                 (fun str' str _ loc -> 
# 100 "g_certicoq_vanilla.mlg"
                                                  FromLibrary (str, str') 
                                                                    ));
                                               (Pcoq.Production.make
                                                (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                (Pcoq.Rule.stop)
                                                                ((Pcoq.Symbol.token (Pcoq.terminal "Absolute"))))
                                                                ((Pcoq.Symbol.nterm string)))
                                                (fun str _ loc -> 
# 99 "g_certicoq_vanilla.mlg"
                                  FromAbsolutePath str 
                                                                  ));
                                               (Pcoq.Production.make
                                                (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                ((Pcoq.Symbol.nterm string)))
                                                (fun str loc -> 
# 98 "g_certicoq_vanilla.mlg"
                       FromRelativePath str 
                                                                ))]);
                                               Vernacextend.arg_printer = fun env sigma -> 
                                               fun _ -> Pp.str "missing printer";
                                               }
let _ = (wit_vanilla_cinclude, vanilla_cinclude)

let (wit_vanilla_certiCoq_Register_extract_inductive, vanilla_certiCoq_Register_extract_inductive) = 
Vernacextend.vernac_argument_extend ~plugin:"coq-certicoq-vanilla.plugin" ~name:"vanilla_certiCoq_Register_extract_inductive" 
{
Vernacextend.arg_parsing = Vernacextend.Arg_rules ([(Pcoq.Production.make
                                                     (Pcoq.Rule.next 
                                                     (Pcoq.Rule.next 
                                                     (Pcoq.Rule.next 
                                                     (Pcoq.Rule.next 
                                                     (Pcoq.Rule.next 
                                                     (Pcoq.Rule.next 
                                                     (Pcoq.Rule.stop)
                                                     ((Pcoq.Symbol.nterm reference)))
                                                     ((Pcoq.Symbol.token (Pcoq.terminal "=>"))))
                                                     ((Pcoq.Symbol.nterm string)))
                                                     ((Pcoq.Symbol.token (Pcoq.terminal "["))))
                                                     ((Pcoq.Symbol.list0 (Pcoq.Symbol.nterm natural))))
                                                     ((Pcoq.Symbol.token (Pcoq.terminal "]"))))
                                                     (fun _ cstrs _ ty _ gr
                                                     loc -> 
# 106 "g_certicoq_vanilla.mlg"
    ((inductive_of_qualid ~loc gr), (ty, cstrs)) 
                                                            ))]);
Vernacextend.arg_printer = fun env sigma -> fun _ -> Pp.str "missing printer";
}
let _ = (wit_vanilla_certiCoq_Register_extract_inductive, vanilla_certiCoq_Register_extract_inductive)

let () = Vernacextend.static_vernac_extend ~plugin:(Some "coq-certicoq-vanilla.plugin") ~command:"CertiCoq_Register" ~classifier:(fun _ -> Vernacextend.classify_as_sideeff) ?entry:None 
         [(Vernacextend.TyML (false, Vernacextend.TyTerminal ("CertiCoq", 
                                     Vernacextend.TyTerminal ("Register", 
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
                                                                   Vernacextend.TyNil))))))))), 
         (let coqpp_body l imps
         () = Vernactypes.vtdefault (fun () -> 
# 110 "g_certicoq_vanilla.mlg"
                                                                                                                                     
    Certicoq.register l imps
  
              ) in fun l
         imps ?loc ~atts () -> coqpp_body l imps
         (Attributes.unsupported_attributes atts)), None));
         (Vernacextend.TyML (false, Vernacextend.TyTerminal ("CertiCoq", 
                                    Vernacextend.TyTerminal ("Extract", 
                                    Vernacextend.TyTerminal ("Inductives", 
                                    Vernacextend.TyTerminal ("[", Vernacextend.TyNonTerminal (
                                                                  Extend.TUlist0sep (
                                                                  Extend.TUentry (Genarg.get_arg_tag wit_vanilla_certiCoq_Register_extract_inductive), ","), 
                                                                  Vernacextend.TyTerminal ("]", 
                                                                  Vernacextend.TyNil)))))), 
         (let coqpp_body inds
         () = Vernactypes.vtdefault (fun () -> 
# 113 "g_certicoq_vanilla.mlg"
                                                                                                                    
    Certicoq.register_inductives inds

              ) in fun inds
         ?loc ~atts () -> coqpp_body inds
         (Attributes.unsupported_attributes atts)), None))]

let () = Vernacextend.static_vernac_extend ~plugin:(Some "coq-certicoq-vanilla.plugin") ~command:"CertiCoq_Compile" ~classifier:(fun _ -> Vernacextend.classify_as_query) ?entry:None 
         [(Vernacextend.TyML (false, Vernacextend.TyTerminal ("CertiCoq", 
                                     Vernacextend.TyTerminal ("Compile", 
                                     Vernacextend.TyNonTerminal (Extend.TUlist0 (
                                                                 Extend.TUentry (Genarg.get_arg_tag wit_vanilla_cargs)), 
                                     Vernacextend.TyNonTerminal (Extend.TUentry (Genarg.get_arg_tag wit_global), 
                                     Vernacextend.TyNil)))), (let coqpp_body l
                                                             gr
                                                             () = Vernactypes.vtdefault (fun () -> 
                                                                  
# 120 "g_certicoq_vanilla.mlg"
                                                                
    let gr = Nametab.global gr in
    let opts = Certicoq.make_options l [] (get_name gr) in
    Certicoq.compile_only opts gr []
  
                                                                  ) in fun l
                                                             gr ?loc ~atts ()
                                                             -> coqpp_body l
                                                             gr
                                                             (Attributes.unsupported_attributes atts)), None));
         (Vernacextend.TyML (false, Vernacextend.TyTerminal ("CertiCoq", 
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
# 125 "g_certicoq_vanilla.mlg"
                                                                                                                                                                                            
    let gr = Nametab.global gr in
    let opts = Certicoq.make_options l cs (get_name gr) in
    Certicoq.compile_only opts gr imps
  
              ) in fun l
         gr cs imps ?loc ~atts () -> coqpp_body l gr cs imps
         (Attributes.unsupported_attributes atts)), None));
         (Vernacextend.TyML (false, Vernacextend.TyTerminal ("CertiCoq", 
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
# 130 "g_certicoq_vanilla.mlg"
                                                                                                                                                                                        
  let gr = Nametab.global gr in
  let opts = Certicoq.make_options l cs (get_name gr) in
  Certicoq.compile_C opts gr imps
  
              ) in fun l
         gr cs imps ?loc ~atts () -> coqpp_body l gr cs imps
         (Attributes.unsupported_attributes atts)), None));
         (Vernacextend.TyML (false, Vernacextend.TyTerminal ("CertiCoq", 
                                    Vernacextend.TyTerminal ("Run", Vernacextend.TyNonTerminal (
                                                                    Extend.TUlist0 (
                                                                    Extend.TUentry (Genarg.get_arg_tag wit_vanilla_cargs)), 
                                                                    Vernacextend.TyNonTerminal (
                                                                    Extend.TUentry (Genarg.get_arg_tag wit_global), 
                                                                    Vernacextend.TyNil)))), 
         (let coqpp_body l gr
         () = Vernactypes.vtdefault (fun () -> 
# 135 "g_certicoq_vanilla.mlg"
                                                            
  let gr = Nametab.global gr in
  let opts = Certicoq.make_options l [] (get_name gr) in
  Certicoq.compile_C opts gr []
  
              ) in fun l
         gr ?loc ~atts () -> coqpp_body l gr
         (Attributes.unsupported_attributes atts)), None));
         (Vernacextend.TyML (false, Vernacextend.TyTerminal ("CertiCoq", 
                                    Vernacextend.TyTerminal ("Show", 
                                    Vernacextend.TyTerminal ("IR", Vernacextend.TyNonTerminal (
                                                                   Extend.TUlist0 (
                                                                   Extend.TUentry (Genarg.get_arg_tag wit_vanilla_cargs)), 
                                                                   Vernacextend.TyNonTerminal (
                                                                   Extend.TUentry (Genarg.get_arg_tag wit_global), 
                                                                   Vernacextend.TyNil))))), 
         (let coqpp_body l gr
         () = Vernactypes.vtdefault (fun () -> 
# 140 "g_certicoq_vanilla.mlg"
                                                                  
    let gr = Nametab.global gr in
    let opts = Certicoq.make_options l [] (get_name gr) in
    Certicoq.show_ir opts gr
  
              ) in fun l
         gr ?loc ~atts () -> coqpp_body l gr
         (Attributes.unsupported_attributes atts)), None));
         (Vernacextend.TyML (false, Vernacextend.TyTerminal ("CertiCoq", 
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
# 145 "g_certicoq_vanilla.mlg"
                                                                                                                                       
    let gr = Nametab.global gr in
    let opts = Certicoq.make_options l cs (get_name gr) in
    Certicoq.show_ir opts gr
  
              ) in fun l
         gr cs ?loc ~atts () -> coqpp_body l gr cs
         (Attributes.unsupported_attributes atts)), None));
         (Vernacextend.TyML (false, Vernacextend.TyTerminal ("CertiCoq", 
                                    Vernacextend.TyTerminal ("FFI", Vernacextend.TyNonTerminal (
                                                                    Extend.TUlist0 (
                                                                    Extend.TUentry (Genarg.get_arg_tag wit_vanilla_ffiargs)), 
                                                                    Vernacextend.TyNonTerminal (
                                                                    Extend.TUentry (Genarg.get_arg_tag wit_global), 
                                                                    Vernacextend.TyNil)))), 
         (let coqpp_body l gr
         () = Vernactypes.vtdefault (fun () -> 
# 150 "g_certicoq_vanilla.mlg"
                                                              
    let gr = Nametab.global gr in
    let opts = Certicoq.make_options l [] "" in
    Certicoq.ffi_command opts gr
  
              ) in fun l
         gr ?loc ~atts () -> coqpp_body l gr
         (Attributes.unsupported_attributes atts)), None));
         (Vernacextend.TyML (false, Vernacextend.TyTerminal ("CertiCoq", 
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
# 155 "g_certicoq_vanilla.mlg"
                                                                                                  
    let grs = List.map Nametab.global grs in
    let opts = Certicoq.make_options l [] "" in
    Certicoq.glue_command opts grs
  
              ) in fun l
         grs ?loc ~atts () -> coqpp_body l grs
         (Attributes.unsupported_attributes atts)), None));
         (Vernacextend.TyML (false, Vernacextend.TyTerminal ("CertiCoq", 
                                    Vernacextend.TyTerminal ("-help", 
                                    Vernacextend.TyNil)), (let coqpp_body () = 
                                                          Vernactypes.vtdefault (fun () -> 
                                                          
# 160 "g_certicoq_vanilla.mlg"
                             
    Feedback.msg_info (str help_msg)
  
                                                          ) in fun ?loc ~atts ()
                                                          -> coqpp_body (Attributes.unsupported_attributes atts)), None))]

let () = Vernacextend.static_vernac_extend ~plugin:(Some "coq-certicoq-vanilla.plugin") ~command:"CertiCoq_Eval" ~classifier:(fun _ -> Vernacextend.classify_as_sideeff) ?entry:None 
         [(Vernacextend.TyML (false, Vernacextend.TyTerminal ("CertiCoq", 
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
# 166 "g_certicoq_vanilla.mlg"
                                                                                                                                                                                         
  let gr = Nametab.global gr in
  let opts = Certicoq.make_options l cs (get_name gr) in
  let result = Certicoq.eval_gr opts gr imps in 
  Feedback.msg_notice Pp.(str" = " ++ Printer.pr_constr_env (Global.env ()) Evd.empty result)
  
              ) in fun l
         gr cs imps ?loc ~atts () -> coqpp_body l gr cs imps
         (Attributes.unsupported_attributes atts)), None));
         (Vernacextend.TyML (false, Vernacextend.TyTerminal ("CertiCoq", 
                                    Vernacextend.TyTerminal ("Eval", 
                                    Vernacextend.TyNonTerminal (Extend.TUlist0 (
                                                                Extend.TUentry (Genarg.get_arg_tag wit_vanilla_cargs)), 
                                    Vernacextend.TyNonTerminal (Extend.TUentry (Genarg.get_arg_tag wit_global), 
                                    Vernacextend.TyNil)))), (let coqpp_body l
                                                            gr
                                                            () = Vernactypes.vtdefault (fun () -> 
                                                                 
# 172 "g_certicoq_vanilla.mlg"
                                                             
  let gr = Nametab.global gr in
  let opts = Certicoq.make_options l [] (get_name gr) in
  let result = Certicoq.eval_gr opts gr [] in
  Feedback.msg_notice Pp.(str" = " ++ Printer.pr_constr_env (Global.env ()) Evd.empty result)
  
                                                                 ) in fun l
                                                            gr ?loc ~atts ()
                                                            -> coqpp_body l
                                                            gr
                                                            (Attributes.unsupported_attributes atts)), None))]

let () = Tacentries.tactic_extend "coq-certicoq-vanilla.plugin" "CertiCoq_eval" ~level:0 
         [(Tacentries.TyML (Tacentries.TyIdent ("certicoq_eval", Tacentries.TyArg (
                                                                 Extend.TUlist0 (
                                                                 Extend.TUentry (Genarg.get_arg_tag wit_vanilla_cargs)), 
                                                                 Tacentries.TyArg (
                                                                 Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                                                 Tacentries.TyArg (
                                                                 Extend.TUentry (Genarg.get_arg_tag wit_tactic), 
                                                                 Tacentries.TyNil)))), 
           (fun l c tac ist -> 
# 182 "g_certicoq_vanilla.mlg"
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


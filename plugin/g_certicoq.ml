let _ = Mltop.add_known_module "coq-certicoq.plugin"

# 5 "g_certicoq.mlg"
 
open Names
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
    (succ i, x :: vars, Id.Map.add id arg lfun)
  in
  let (_, args, lfun) = List.fold_right fold args (0, [], Id.Map.empty) in
  let lfun = Id.Map.add (Id.of_string "F") f lfun in
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



let (wit_cargs, cargs) = Tacentries.argument_extend ~plugin:"coq-certicoq.plugin" ~name:"cargs" 
                         {
                         Tacentries.arg_parsing = Vernacextend.Arg_rules (
                                                  [(Pcoq.Production.make
                                                    (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                    (Pcoq.Rule.stop)
                                                                    ((Pcoq.Symbol.token (Pcoq.terminal "-toplevel_name"))))
                                                                    ((Pcoq.Symbol.nterm string)))
                                                    (fun s _ loc -> 
# 77 "g_certicoq.mlg"
                                      TOPLEVEL_NAME(s) 
                                                                    ));
                                                  (Pcoq.Production.make
                                                   (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                   (Pcoq.Rule.stop)
                                                                   ((Pcoq.Symbol.token (Pcoq.terminal "-file"))))
                                                                   ((Pcoq.Symbol.nterm string)))
                                                   (fun s _ loc -> 
# 76 "g_certicoq.mlg"
                             FILENAME(s) 
                                                                   ));
                                                  (Pcoq.Production.make
                                                   (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                   (Pcoq.Rule.stop)
                                                                   ((Pcoq.Symbol.token (Pcoq.terminal "-ext"))))
                                                                   ((Pcoq.Symbol.nterm string)))
                                                   (fun s _ loc -> 
# 75 "g_certicoq.mlg"
                            EXT(s) 
                                                                   ));
                                                  (Pcoq.Production.make
                                                   (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                   (Pcoq.Rule.stop)
                                                                   ((Pcoq.Symbol.token (Pcoq.terminal "-dev"))))
                                                                   ((Pcoq.Symbol.nterm natural)))
                                                   (fun n _ loc -> 
# 74 "g_certicoq.mlg"
                             DEV(n) 
                                                                   ));
                                                  (Pcoq.Production.make
                                                   (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                   (Pcoq.Rule.stop)
                                                                   ((Pcoq.Symbol.token (Pcoq.terminal "-build_dir"))))
                                                                   ((Pcoq.Symbol.nterm string)))
                                                   (fun s _ loc -> 
# 73 "g_certicoq.mlg"
                                  BUILDDIR(s) 
                                                                   ));
                                                  (Pcoq.Production.make
                                                   (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                   (Pcoq.Rule.stop)
                                                                   ((Pcoq.Symbol.token (Pcoq.terminal "-config"))))
                                                                   ((Pcoq.Symbol.nterm natural)))
                                                   (fun n _ loc -> 
# 71 "g_certicoq.mlg"
                                ANFCONFIG(n) 
                                                                   ));
                                                  (Pcoq.Production.make
                                                   (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                   (Pcoq.Rule.stop)
                                                                   ((Pcoq.Symbol.token (Pcoq.terminal "-args"))))
                                                                   ((Pcoq.Symbol.nterm natural)))
                                                   (fun n _ loc -> 
# 70 "g_certicoq.mlg"
                              ARGS(n) 
                                                                   ));
                                                  (Pcoq.Production.make
                                                   (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                   ((Pcoq.Symbol.token (Pcoq.terminal "-debug"))))
                                                   (fun _ loc -> 
# 69 "g_certicoq.mlg"
                    DEBUG 
                                                                 ));
                                                  (Pcoq.Production.make
                                                   (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                   (Pcoq.Rule.stop)
                                                                   ((Pcoq.Symbol.token (Pcoq.terminal "-O"))))
                                                                   ((Pcoq.Symbol.nterm natural)))
                                                   (fun n _ loc -> 
# 68 "g_certicoq.mlg"
                           OPT(n) 
                                                                   ));
                                                  (Pcoq.Production.make
                                                   (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                   ((Pcoq.Symbol.token (Pcoq.terminal "-time_anf"))))
                                                   (fun _ loc -> 
# 67 "g_certicoq.mlg"
                       TIMEANF 
                                                                 ));
                                                  (Pcoq.Production.make
                                                   (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                   ((Pcoq.Symbol.token (Pcoq.terminal "-time"))))
                                                   (fun _ loc -> 
# 66 "g_certicoq.mlg"
                   TIME 
                                                                 ));
                                                  (Pcoq.Production.make
                                                   (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                   ((Pcoq.Symbol.token (Pcoq.terminal "-cps"))))
                                                   (fun _ loc -> 
# 65 "g_certicoq.mlg"
                  CPS 
                                                                 ));
                                                  (Pcoq.Production.make
                                                   (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                   ((Pcoq.Symbol.token (Pcoq.terminal "-bypass_qed"))))
                                                   (fun _ loc -> 
# 64 "g_certicoq.mlg"
                         BYPASS_QED 
                                                                 ));
                                                  (Pcoq.Production.make
                                                   (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                   ((Pcoq.Symbol.token (Pcoq.terminal "-unsafe-erasure"))))
                                                   (fun _ loc -> 
# 63 "g_certicoq.mlg"
                             UNSAFE_ERASURE 
                                                                 ));
                                                  (Pcoq.Production.make
                                                   (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                   ((Pcoq.Symbol.token (Pcoq.terminal "-typed-erasure"))))
                                                   (fun _ loc -> 
# 62 "g_certicoq.mlg"
                            TYPED_ERASURE 
                                                                 ))]);
                         Tacentries.arg_tag = None;
                         Tacentries.arg_intern = Tacentries.ArgInternFun (fun ist v -> (ist, v));
                         Tacentries.arg_subst = Tacentries.ArgSubstFun (fun s v -> v);
                         Tacentries.arg_interp = Tacentries.ArgInterpRet;
                         Tacentries.arg_printer = ((fun env sigma -> fun _ _ _ _ -> Pp.str "missing printer"), (fun env sigma -> fun _ _ _ _ -> Pp.str "missing printer"), (fun env sigma -> fun _ _ _ _ -> Pp.str "missing printer"));
                         }
let _ = (wit_cargs, cargs)

let (wit_extract_cnst, extract_cnst) = Vernacextend.vernac_argument_extend ~plugin:"coq-certicoq.plugin" ~name:"extract_cnst" 
                                       {
                                       Vernacextend.arg_parsing = Vernacextend.Arg_rules (
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
                                                                    (fun _ _
                                                                    str _ gr
                                                                    loc -> 
                                                                    
# 84 "g_certicoq.mlg"
                                                         
  try (extract_constant (Option.get (Constrintern.locate_reference gr)) str, true)
  with Not_found -> CErrors.user_err ~loc Pp.(str"Reference " ++ Libnames.pr_qualid gr ++ str" not found") 
                                                                    ));
                                                                  (Pcoq.Production.make
                                                                   (Pcoq.Rule.next 
                                                                   (Pcoq.Rule.next 
                                                                   (Pcoq.Rule.next 
                                                                   (Pcoq.Rule.stop)
                                                                   ((Pcoq.Symbol.nterm reference)))
                                                                   ((Pcoq.Symbol.token (Pcoq.terminal "=>"))))
                                                                   ((Pcoq.Symbol.nterm string)))
                                                                   (fun str _
                                                                   gr loc ->
                                                                   
# 81 "g_certicoq.mlg"
                                          
  try (extract_constant (Option.get (Constrintern.locate_reference gr)) str, false)
  with Not_found -> CErrors.user_err ~loc Pp.(str"Reference " ++ Libnames.pr_qualid gr ++ str" not found") 
                                                                   ))]);
                                       Vernacextend.arg_printer = fun env sigma -> 
                                       fun _ -> Pp.str "missing printer";
                                       }
let _ = (wit_extract_cnst, extract_cnst)

let (wit_ffiargs, ffiargs) = Vernacextend.vernac_argument_extend ~plugin:"coq-certicoq.plugin" ~name:"ffiargs" 
                             {
                             Vernacextend.arg_parsing = Vernacextend.Arg_rules (
                                                        [(Pcoq.Production.make
                                                          (Pcoq.Rule.next 
                                                          (Pcoq.Rule.stop)
                                                          ((Pcoq.Symbol.nterm cargs)))
                                                          (fun c loc -> 
# 91 "g_certicoq.mlg"
                    c 
                                                                    ));
                                                        (Pcoq.Production.make
                                                         (Pcoq.Rule.next 
                                                         (Pcoq.Rule.next 
                                                         (Pcoq.Rule.stop)
                                                         ((Pcoq.Symbol.token (Pcoq.terminal "-prefix"))))
                                                         ((Pcoq.Symbol.nterm string)))
                                                         (fun s _ loc -> 
# 90 "g_certicoq.mlg"
                               PREFIX(s) 
                                                                    ))]);
                             Vernacextend.arg_printer = fun env sigma -> 
                             fun _ -> Pp.str "missing printer";
                             }
let _ = (wit_ffiargs, ffiargs)

let (wit_glueargs, glueargs) = Vernacextend.vernac_argument_extend ~plugin:"coq-certicoq.plugin" ~name:"glueargs" 
                               {
                               Vernacextend.arg_parsing = Vernacextend.Arg_rules (
                                                          [(Pcoq.Production.make
                                                            (Pcoq.Rule.next 
                                                            (Pcoq.Rule.next 
                                                            (Pcoq.Rule.stop)
                                                            ((Pcoq.Symbol.token (Pcoq.terminal "-build_dir"))))
                                                            ((Pcoq.Symbol.nterm string)))
                                                            (fun s _ loc -> 
# 99 "g_certicoq.mlg"
                                  BUILDDIR(s) 
                                                                    ));
                                                          (Pcoq.Production.make
                                                           (Pcoq.Rule.next 
                                                           (Pcoq.Rule.next 
                                                           (Pcoq.Rule.stop)
                                                           ((Pcoq.Symbol.token (Pcoq.terminal "-file"))))
                                                           ((Pcoq.Symbol.nterm string)))
                                                           (fun s _ loc -> 
# 98 "g_certicoq.mlg"
                             FILENAME(s) 
                                                                    ));
                                                          (Pcoq.Production.make
                                                           (Pcoq.Rule.next 
                                                           (Pcoq.Rule.next 
                                                           (Pcoq.Rule.stop)
                                                           ((Pcoq.Symbol.token (Pcoq.terminal "-args"))))
                                                           ((Pcoq.Symbol.nterm natural)))
                                                           (fun n _ loc -> 
# 97 "g_certicoq.mlg"
                              ARGS(n) 
                                                                    ));
                                                          (Pcoq.Production.make
                                                           (Pcoq.Rule.next 
                                                           (Pcoq.Rule.stop)
                                                           ((Pcoq.Symbol.token (Pcoq.terminal "-debug"))))
                                                           (fun _ loc -> 
# 96 "g_certicoq.mlg"
                    DEBUG 
                                                                    ));
                                                          (Pcoq.Production.make
                                                           (Pcoq.Rule.next 
                                                           (Pcoq.Rule.stop)
                                                           ((Pcoq.Symbol.token (Pcoq.terminal "-cps"))))
                                                           (fun _ loc -> 
# 95 "g_certicoq.mlg"
                  CPS 
                                                                    ))]);
                               Vernacextend.arg_printer = fun env sigma -> 
                               fun _ -> Pp.str "missing printer";
                               }
let _ = (wit_glueargs, glueargs)

let (wit_cinclude, cinclude) = Vernacextend.vernac_argument_extend ~plugin:"coq-certicoq.plugin" ~name:"cinclude" 
                               {
                               Vernacextend.arg_parsing = Vernacextend.Arg_rules (
                                                          [(Pcoq.Production.make
                                                            (Pcoq.Rule.next 
                                                            (Pcoq.Rule.next 
                                                            (Pcoq.Rule.stop)
                                                            ((Pcoq.Symbol.token (Pcoq.terminal "Absolute"))))
                                                            ((Pcoq.Symbol.nterm string)))
                                                            (fun str _ loc ->
                                                            
# 105 "g_certicoq.mlg"
                                  FromAbsolutePath str 
                                                            ));
                                                          (Pcoq.Production.make
                                                           (Pcoq.Rule.next 
                                                           (Pcoq.Rule.next 
                                                           (Pcoq.Rule.next 
                                                           (Pcoq.Rule.stop)
                                                           ((Pcoq.Symbol.token (Pcoq.terminal "Library"))))
                                                           ((Pcoq.Symbol.nterm string)))
                                                           ((Pcoq.Symbol.opt (Pcoq.Symbol.nterm string))))
                                                           (fun str' str _
                                                           loc -> 
# 104 "g_certicoq.mlg"
                                                  FromLibrary (str, str') 
                                                                  ));
                                                          (Pcoq.Production.make
                                                           (Pcoq.Rule.next 
                                                           (Pcoq.Rule.stop)
                                                           ((Pcoq.Symbol.nterm string)))
                                                           (fun str loc -> 
# 103 "g_certicoq.mlg"
                       FromRelativePath str 
                                                                    ))]);
                               Vernacextend.arg_printer = fun env sigma -> 
                               fun _ -> Pp.str "missing printer";
                               }
let _ = (wit_cinclude, cinclude)

let (wit_certiCoq_Register_extract_inductive, certiCoq_Register_extract_inductive) = 
Vernacextend.vernac_argument_extend ~plugin:"coq-certicoq.plugin" ~name:"certiCoq_Register_extract_inductive" 
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
# 110 "g_certicoq.mlg"
    ((inductive_of_qualid ~loc gr), (ty, cstrs)) 
                                                            ))]);
Vernacextend.arg_printer = fun env sigma -> fun _ -> Pp.str "missing printer";
}
let _ = (wit_certiCoq_Register_extract_inductive, certiCoq_Register_extract_inductive)

let () = Vernacextend.static_vernac_extend ~plugin:(Some "coq-certicoq.plugin") ~command:"CertiCoq_Register" ~classifier:(fun _ -> Vernacextend.classify_as_sideeff) ?entry:None 
         [(Vernacextend.TyML (false, Vernacextend.TyTerminal ("CertiCoq", 
                                     Vernacextend.TyTerminal ("Register", 
                                     Vernacextend.TyTerminal ("[", Vernacextend.TyNonTerminal (
                                                                   Extend.TUlist0sep (
                                                                   Extend.TUentry (Genarg.get_arg_tag wit_extract_cnst), ","), 
                                                                   Vernacextend.TyTerminal ("]", 
                                                                   Vernacextend.TyTerminal ("Include", 
                                                                   Vernacextend.TyTerminal ("[", 
                                                                   Vernacextend.TyNonTerminal (
                                                                   Extend.TUlist0sep (
                                                                   Extend.TUentry (Genarg.get_arg_tag wit_cinclude), ","), 
                                                                   Vernacextend.TyTerminal ("]", 
                                                                   Vernacextend.TyNil))))))))), 
         (let coqpp_body l imps
         () = Vernactypes.vtdefault (fun () -> 
# 114 "g_certicoq.mlg"
                                                                                                                     
    Certicoq.register l imps
  
              ) in fun l
         imps ?loc ~atts () -> coqpp_body l imps
         (Attributes.unsupported_attributes atts)), None));
         (Vernacextend.TyML (false, Vernacextend.TyTerminal ("CertiCoq", 
                                    Vernacextend.TyTerminal ("Extract", 
                                    Vernacextend.TyTerminal ("Inductives", 
                                    Vernacextend.TyTerminal ("[", Vernacextend.TyNonTerminal (
                                                                  Extend.TUlist0sep (
                                                                  Extend.TUentry (Genarg.get_arg_tag wit_certiCoq_Register_extract_inductive), ","), 
                                                                  Vernacextend.TyTerminal ("]", 
                                                                  Vernacextend.TyNil)))))), 
         (let coqpp_body inds
         () = Vernactypes.vtdefault (fun () -> 
# 117 "g_certicoq.mlg"
                                                                                                            
    Certicoq.register_inductives inds

              ) in fun inds
         ?loc ~atts () -> coqpp_body inds
         (Attributes.unsupported_attributes atts)), None))]

let () = Vernacextend.static_vernac_extend ~plugin:(Some "coq-certicoq.plugin") ~command:"CertiCoq_Compile" ~classifier:(fun _ -> Vernacextend.classify_as_query) ?entry:None 
         [(Vernacextend.TyML (false, Vernacextend.TyTerminal ("CertiCoq", 
                                     Vernacextend.TyTerminal ("Compile", 
                                     Vernacextend.TyNonTerminal (Extend.TUlist0 (
                                                                 Extend.TUentry (Genarg.get_arg_tag wit_cargs)), 
                                     Vernacextend.TyNonTerminal (Extend.TUentry (Genarg.get_arg_tag wit_global), 
                                     Vernacextend.TyNil)))), (let coqpp_body l
                                                             gr
                                                             () = Vernactypes.vtdefault (fun () -> 
                                                                  
# 123 "g_certicoq.mlg"
                                                        
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
                                                                Extend.TUentry (Genarg.get_arg_tag wit_cargs)), 
                                    Vernacextend.TyNonTerminal (Extend.TUentry (Genarg.get_arg_tag wit_global), 
                                    Vernacextend.TyTerminal ("Extract", 
                                    Vernacextend.TyTerminal ("Constants", 
                                    Vernacextend.TyTerminal ("[", Vernacextend.TyNonTerminal (
                                                                  Extend.TUlist0sep (
                                                                  Extend.TUentry (Genarg.get_arg_tag wit_extract_cnst), ","), 
                                                                  Vernacextend.TyTerminal ("]", 
                                                                  Vernacextend.TyTerminal ("Include", 
                                                                  Vernacextend.TyTerminal ("[", 
                                                                  Vernacextend.TyNonTerminal (
                                                                  Extend.TUlist0sep (
                                                                  Extend.TUentry (Genarg.get_arg_tag wit_cinclude), ","), 
                                                                  Vernacextend.TyTerminal ("]", 
                                                                  Vernacextend.TyNil))))))))))))), 
         (let coqpp_body l gr cs imps
         () = Vernactypes.vtdefault (fun () -> 
# 128 "g_certicoq.mlg"
                                                                                                                                                                    
    let gr = Nametab.global gr in
    let opts = Certicoq.make_options l cs (get_name gr) in
    Certicoq.compile_only opts gr imps
  
              ) in fun l
         gr cs imps ?loc ~atts () -> coqpp_body l gr cs imps
         (Attributes.unsupported_attributes atts)), None));
         (Vernacextend.TyML (false, Vernacextend.TyTerminal ("CertiCoq", 
                                    Vernacextend.TyTerminal ("Compile", 
                                    Vernacextend.TyTerminal ("Wasm", 
                                    Vernacextend.TyNonTerminal (Extend.TUlist0 (
                                                                Extend.TUentry (Genarg.get_arg_tag wit_cargs)), 
                                    Vernacextend.TyNonTerminal (Extend.TUentry (Genarg.get_arg_tag wit_global), 
                                    Vernacextend.TyNil))))), (let coqpp_body l
                                                             gr
                                                             () = Vernactypes.vtdefault (fun () -> 
                                                                  
# 133 "g_certicoq.mlg"
                                                               
    let gr = Nametab.global gr in
    let opts = Certicoq.make_options l [] (get_name gr) in
    Certicoq.compile_wasm opts gr
  
                                                                  ) in fun l
                                                             gr ?loc ~atts ()
                                                             -> coqpp_body l
                                                             gr
                                                             (Attributes.unsupported_attributes atts)), None));
         (Vernacextend.TyML (false, Vernacextend.TyTerminal ("CertiCoq", 
                                    Vernacextend.TyTerminal ("Run", Vernacextend.TyNonTerminal (
                                                                    Extend.TUlist0 (
                                                                    Extend.TUentry (Genarg.get_arg_tag wit_cargs)), 
                                                                    Vernacextend.TyNonTerminal (
                                                                    Extend.TUentry (Genarg.get_arg_tag wit_global), 
                                                                    Vernacextend.TyTerminal ("Extract", 
                                                                    Vernacextend.TyTerminal ("Constants", 
                                                                    Vernacextend.TyTerminal ("[", 
                                                                    Vernacextend.TyNonTerminal (
                                                                    Extend.TUlist0sep (
                                                                    Extend.TUentry (Genarg.get_arg_tag wit_extract_cnst), ","), 
                                                                    Vernacextend.TyTerminal ("]", 
                                                                    Vernacextend.TyTerminal ("Include", 
                                                                    Vernacextend.TyTerminal ("[", 
                                                                    Vernacextend.TyNonTerminal (
                                                                    Extend.TUlist0sep (
                                                                    Extend.TUentry (Genarg.get_arg_tag wit_cinclude), ","), 
                                                                    Vernacextend.TyTerminal ("]", 
                                                                    Vernacextend.TyNil))))))))))))), 
         (let coqpp_body l gr cs imps
         () = Vernactypes.vtdefault (fun () -> 
# 138 "g_certicoq.mlg"
                                                                                                                                                                
  let gr = Nametab.global gr in
  let opts = Certicoq.make_options l cs (get_name gr) in
  Certicoq.compile_C opts gr imps
  
              ) in fun l
         gr cs imps ?loc ~atts () -> coqpp_body l gr cs imps
         (Attributes.unsupported_attributes atts)), None));
         (Vernacextend.TyML (false, Vernacextend.TyTerminal ("CertiCoq", 
                                    Vernacextend.TyTerminal ("Run", Vernacextend.TyNonTerminal (
                                                                    Extend.TUlist0 (
                                                                    Extend.TUentry (Genarg.get_arg_tag wit_cargs)), 
                                                                    Vernacextend.TyNonTerminal (
                                                                    Extend.TUentry (Genarg.get_arg_tag wit_global), 
                                                                    Vernacextend.TyNil)))), 
         (let coqpp_body l gr
         () = Vernactypes.vtdefault (fun () -> 
# 143 "g_certicoq.mlg"
                                                    
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
                                                                   Extend.TUentry (Genarg.get_arg_tag wit_cargs)), 
                                                                   Vernacextend.TyNonTerminal (
                                                                   Extend.TUentry (Genarg.get_arg_tag wit_global), 
                                                                   Vernacextend.TyNil))))), 
         (let coqpp_body l gr
         () = Vernactypes.vtdefault (fun () -> 
# 148 "g_certicoq.mlg"
                                                          
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
                                                                   Extend.TUentry (Genarg.get_arg_tag wit_cargs)), 
                                                                   Vernacextend.TyNonTerminal (
                                                                   Extend.TUentry (Genarg.get_arg_tag wit_global), 
                                                                   Vernacextend.TyTerminal ("Extract", 
                                                                   Vernacextend.TyTerminal ("Constants", 
                                                                   Vernacextend.TyTerminal ("[", 
                                                                   Vernacextend.TyNonTerminal (
                                                                   Extend.TUlist0sep (
                                                                   Extend.TUentry (Genarg.get_arg_tag wit_extract_cnst), ","), 
                                                                   Vernacextend.TyTerminal ("]", 
                                                                   Vernacextend.TyNil)))))))))), 
         (let coqpp_body l gr cs
         () = Vernactypes.vtdefault (fun () -> 
# 153 "g_certicoq.mlg"
                                                                                                                       
    let gr = Nametab.global gr in
    let opts = Certicoq.make_options l cs (get_name gr) in
    Certicoq.show_ir opts gr
  
              ) in fun l
         gr cs ?loc ~atts () -> coqpp_body l gr cs
         (Attributes.unsupported_attributes atts)), None));
         (Vernacextend.TyML (false, Vernacextend.TyTerminal ("CertiCoq", 
                                    Vernacextend.TyTerminal ("FFI", Vernacextend.TyNonTerminal (
                                                                    Extend.TUlist0 (
                                                                    Extend.TUentry (Genarg.get_arg_tag wit_ffiargs)), 
                                                                    Vernacextend.TyNonTerminal (
                                                                    Extend.TUentry (Genarg.get_arg_tag wit_global), 
                                                                    Vernacextend.TyNil)))), 
         (let coqpp_body l gr
         () = Vernactypes.vtdefault (fun () -> 
# 158 "g_certicoq.mlg"
                                                      
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
                                                                Extend.TUentry (Genarg.get_arg_tag wit_glueargs)), 
                                    Vernacextend.TyTerminal ("[", Vernacextend.TyNonTerminal (
                                                                  Extend.TUlist0sep (
                                                                  Extend.TUentry (Genarg.get_arg_tag wit_global), ","), 
                                                                  Vernacextend.TyTerminal ("]", 
                                                                  Vernacextend.TyNil))))))), 
         (let coqpp_body l grs
         () = Vernactypes.vtdefault (fun () -> 
# 163 "g_certicoq.mlg"
                                                                                          
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
                                                          
# 168 "g_certicoq.mlg"
                             
    Feedback.msg_info (str help_msg)
  
                                                          ) in fun ?loc ~atts ()
                                                          -> coqpp_body (Attributes.unsupported_attributes atts)), None))]

let () = Vernacextend.static_vernac_extend ~plugin:(Some "coq-certicoq.plugin") ~command:"CertiCoq_Eval" ~classifier:(fun _ -> Vernacextend.classify_as_sideeff) ?entry:None 
         [(Vernacextend.TyML (false, Vernacextend.TyTerminal ("CertiCoq", 
                                     Vernacextend.TyTerminal ("Eval", 
                                     Vernacextend.TyNonTerminal (Extend.TUlist0 (
                                                                 Extend.TUentry (Genarg.get_arg_tag wit_cargs)), 
                                     Vernacextend.TyNonTerminal (Extend.TUentry (Genarg.get_arg_tag wit_global), 
                                     Vernacextend.TyTerminal ("Extract", 
                                     Vernacextend.TyTerminal ("Constants", 
                                     Vernacextend.TyTerminal ("[", Vernacextend.TyNonTerminal (
                                                                   Extend.TUlist0sep (
                                                                   Extend.TUentry (Genarg.get_arg_tag wit_extract_cnst), ","), 
                                                                   Vernacextend.TyTerminal ("]", 
                                                                   Vernacextend.TyTerminal ("Include", 
                                                                   Vernacextend.TyTerminal ("[", 
                                                                   Vernacextend.TyNonTerminal (
                                                                   Extend.TUlist0sep (
                                                                   Extend.TUentry (Genarg.get_arg_tag wit_cinclude), ","), 
                                                                   Vernacextend.TyTerminal ("]", 
                                                                   Vernacextend.TyNil))))))))))))), 
         (let coqpp_body l gr cs imps
         () = Vernactypes.vtdefault (fun () -> 
# 174 "g_certicoq.mlg"
                                                                                                                                                                 
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
                                                                Extend.TUentry (Genarg.get_arg_tag wit_cargs)), 
                                    Vernacextend.TyNonTerminal (Extend.TUentry (Genarg.get_arg_tag wit_global), 
                                    Vernacextend.TyNil)))), (let coqpp_body l
                                                            gr
                                                            () = Vernactypes.vtdefault (fun () -> 
                                                                 
# 180 "g_certicoq.mlg"
                                                     
  let gr = Nametab.global gr in
  let opts = Certicoq.make_options l [] (get_name gr) in
  let result = Certicoq.eval_gr opts gr [] in
  Feedback.msg_notice Pp.(str" = " ++ Printer.pr_constr_env (Global.env ()) Evd.empty result)
  
                                                                 ) in fun l
                                                            gr ?loc ~atts ()
                                                            -> coqpp_body l
                                                            gr
                                                            (Attributes.unsupported_attributes atts)), None))]

let () = Tacentries.tactic_extend "coq-certicoq.plugin" "CertiCoq_eval" ~level:0 
         [(Tacentries.TyML (Tacentries.TyIdent ("certicoq_eval", Tacentries.TyArg (
                                                                 Extend.TUlist0 (
                                                                 Extend.TUentry (Genarg.get_arg_tag wit_cargs)), 
                                                                 Tacentries.TyArg (
                                                                 Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                                                 Tacentries.TyArg (
                                                                 Extend.TUentry (Genarg.get_arg_tag wit_tactic), 
                                                                 Tacentries.TyNil)))), 
           (fun l c tac ist -> 
# 190 "g_certicoq.mlg"
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


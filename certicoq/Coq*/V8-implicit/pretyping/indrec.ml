(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id: indrec.ml 9831 2007-05-17 18:55:42Z herbelin $ *)

open Pp
open Util
open Names
open Libnames
open Nameops
open Term
open Termops
open Declarations
open Entries
open Inductive
open Inductiveops
open Environ
open Reductionops
open Typeops
open Type_errors
open Safe_typing
open Nametab
open Sign

(* Errors related to recursors building *)
type recursion_scheme_error =
  | NotAllowedCaseAnalysis of bool * sorts * inductive
  | BadInduction of bool * identifier * sorts
  | NotMutualInScheme of inductive * inductive

exception RecursionSchemeError of recursion_scheme_error

let make_prod_dep dep env = if dep then prod_name env else mkProd
let mkLambda_string s imp t c =
  mkLambda (Name (id_of_string s), imp, t, c)

(*******************************************)
(* Building curryfied elimination          *)
(*******************************************)

(**********************************************************************)
(* Building case analysis schemes *)
(* Nouvelle version, plus concise mais plus coûteuse à cause de
   lift_constructor et lift_inductive_family qui ne se contentent pas de 
   lifter les paramètres globaux *)

let mis_make_case_com depopt env sigma ind (mib,mip as specif) kind =
  let lnamespar = mib.mind_params_ctxt in
  let dep = match depopt with 
    | None -> inductive_sort_family mip <> InProp
    | Some d -> d
  in
  if not (List.mem kind (elim_sorts specif)) then
    raise
      (RecursionSchemeError
	 (NotAllowedCaseAnalysis
	    (dep,(new_sort_in_family kind),ind)));

  let ndepar = mip.mind_nrealargs + 1 in

  (* Pas génant car env ne sert pas à typer mais juste à renommer les Anonym *)
  (* mais pas très joli ... (mais manque get_sort_of à ce niveau) *)
  let env' = push_rel_context lnamespar env in

  let indf =
    let (inst,imps) = extended_rel_list 0 lnamespar in
    make_ind_family(ind,inst,imps) in
  let constrs = get_constructors env indf in

  let rec add_branch env k = 
    if k = Array.length mip.mind_consnames then
      let nbprod = k+1 in

      let indf' = lift_inductive_family nbprod indf in
      let arsign,_ = get_arity env indf' in
      let depind = build_dependent_inductive env indf' in
      let deparsign = (Anonymous,Expl,None,depind)::arsign in

      let ci = make_case_info env ind RegularStyle in
      let pbody =
        let (inst,imps) =
          if dep then extended_rel_vect 0 deparsign
          else extended_rel_vect 1 arsign in
        appvect(mkRel (ndepar + nbprod), inst,imps) in
      let p = 
	it_mkLambda_or_LetIn_name env'
	  ((if dep then mkLambda_name env' else mkLambda)
	   (Anonymous,Expl,depind,pbody))
          arsign
      in
      let body_arsign =
        (Anonymous,Expl,None,depind)::set_impl_rel_context Impl arsign in
      it_mkLambda_or_LetIn_name env'
       	(mkCase (ci, lift ndepar p, mkRel 1, rel_vect ndepar k))
       	body_arsign
    else
      let cs = lift_constructor (k+1) constrs.(k) in
      let t = build_branch_type env dep (mkRel (k+1)) cs in
      mkLambda_string "f" Expl t
	(add_branch (push_rel (Anonymous, Expl, None, t) env) (k+1))
  in
  let typP = make_arity env' dep indf (new_sort_in_family kind) in
  it_mkLambda_or_LetIn_name env 
    (mkLambda_string "P" Impl typP
       (add_branch (push_rel (Anonymous,Impl,None,typP) env') 0))
    (set_impl_rel_context Impl lnamespar)
    
(* check if the type depends recursively on one of the inductive scheme *)

(**********************************************************************)
(* Building the recursive elimination *)

(*
 * t is the type of the constructor co and recargs is the information on 
 * the recursive calls. (It is assumed to be in form given by the user).
 * build the type of the corresponding branch of the recurrence principle
 * assuming f has this type, branch_rec gives also the term 
 *   [x1]..[xk](f xi (F xi) ...) to be put in the corresponding branch of 
 * the case operation
 * FPvect gives for each inductive definition if we want an elimination 
 * on it with which predicate and which recursive function. 
 *)

let type_rec_branch is_rec dep env sigma (vargs,depPvect,decP) tyi cs recargs = 
  let make_prod = make_prod_dep dep in
  let nparams = List.length vargs in
  let process_pos env depK pk =
    let rec prec env i sign p =
      let p',largs,aimps = whd_betadeltaiota_nolet_stack env sigma p in
      match kind_of_term p' with
	| Prod (n,imp,t,c) ->
	    let d = (n,imp,None,t) in
	    make_prod env (n,imp,t,prec (push_rel d env) (i+1) (d::sign) c)
	| LetIn (n,imp,b,t,c) ->
	    let d = (n,imp,Some b,t) in
	    mkLetIn (n,imp,b,t,prec (push_rel d env) (i+1) (d::sign) c)
     	| Ind (_,_) ->
	    let realargs = list_skipn nparams largs in
	    let raimps = list_skipn nparams aimps in
	    let base = applist (lift i pk,realargs,raimps) in
            if depK then 
              let (inst,imps) = extended_rel_list 0 sign in
	      Reduction.beta_appvect base
                [|applist(mkRel (i+1),inst,imps)|] [|Expl|]
            else 
	      base
      	| _ -> assert false 
    in
    prec env 0 []
  in
  let rec process_constr env i c recargs nhyps li imps =
    if nhyps > 0 then match kind_of_term c with 
      | Prod (n,imp,t,c_0) ->
          let (optionpos,rest) = 
	    match recargs with 
	      | [] -> None,[]
              | ra::rest ->
                  (match dest_recarg ra with 
	            | Mrec j when is_rec -> (depPvect.(j),rest)
	            | Imbr _  -> 
		        Options.if_verbose warning "Ignoring recursive call"; 
		        (None,rest) 
                    | _ -> (None, rest))
	  in 
          (match optionpos with 
             | Some(dep',p) when imp=Expl -> 
		 let nP = lift (i+1+decP) p in
                 let env' = push_rel (n,imp,None,t) env in
		 let t_0 = process_pos env' dep' nP (lift 1 t) in 
		 make_prod_dep (dep or dep') env
                   (n,imp,t,
		    mkArrow imp t_0
		      (process_constr
			(push_rel (Anonymous,imp,None,t_0) env')
			 (i+2) (lift 1 c_0) rest (nhyps-1) (i::li)
                        (imp::imps)))
	     | _ -> 
		 make_prod env
		   (n,imp,t,
		    process_constr (push_rel (n,imp,None,t) env) (i+1) c_0 rest
		      (nhyps-1) (i::li) (imp::imps)))
      | LetIn (n,imp,b,t,c_0) ->
	  mkLetIn (n,imp,b,t,
		   process_constr
		     (push_rel (n,imp,Some b,t) env)
		     (i+1) c_0 recargs (nhyps-1) li imps)
      | _ -> assert false
    else
      if dep then
	let realargs = List.map (fun k -> mkRel (i-k)) (List.rev li) in
        let params = List.map (lift i) vargs in
        let aimps = List.map (fun _ -> Impl) params @ List.rev imps in
        let co = applist (mkConstruct cs.cs_cstr,params@realargs,aimps) in
	Reduction.beta_appvect c [|co|] [|Expl|]
      else c
  in
  let nhyps = List.length cs.cs_args in
  let nP = match depPvect.(tyi) with 
    | Some(_,p) -> lift (nhyps+decP) p
    | _ -> assert false in
  let base = appvect (nP,cs.cs_concl_realargs,cs.cs_concl_imps) in
  let c = it_mkProd_or_LetIn base cs.cs_args in
  process_constr env 0 c recargs nhyps [] []


let make_rec_branch_arg env sigma (nparrec,fvect,decF) f cstr recargs = 
  let process_pos env fk  =
    let rec prec env i hyps p =
      let p',largs,limps = whd_betadeltaiota_nolet_stack env sigma p in
      match kind_of_term p' with
	| Prod (n,imp,t,c) ->
	    let d = (n,imp,None,t) in
	    lambda_name env (n,imp,t,prec (push_rel d env) (i+1) (d::hyps) c)
	| LetIn (n,imp,b,t,c) ->
	    let d = (n,imp,Some b,t) in
	    mkLetIn (n,imp,b,t,prec (push_rel d env) (i+1) (d::hyps) c)
     	| Ind _ -> 
            let realargs = list_skipn nparrec largs in
(*            let rimps = list_skipn nparrec limps in*)
            let rimps = List.map (fun _ -> Impl) realargs in 
            let (inst,imps) = extended_rel_vect 0 hyps in
            let arg = appvect (mkRel (i+1),inst,imps) in 
            applist(lift i fk,realargs@[arg],rimps@[Expl])
     	| _ -> assert false
    in
    prec env 0 []
  in
  (* ici, cstrprods est la liste des produits du constructeur instantié *)
  let rec process_constr env i f = function
    | (n,imp,None,t as d)::cprest, recarg::rest -> 
        let optionpos = 
	  match dest_recarg recarg with 
            | Norec   -> None
            | Imbr _  -> None
            | Mrec i  -> fvect.(i)
	in 
        (match optionpos with 
           | Some(_,f_0) when imp=Expl-> 
	       let nF = lift (i+1+decF) f_0 in
               let env' = push_rel d env in
	       let arg = process_pos env' nF (lift 1 t) in 
               lambda_name env
		 (n,imp,t,process_constr env' (i+1)
		    (whd_beta (applist (lift 1 f, [(mkRel 1); arg],[imp;imp])))
		    (cprest,rest))
           | _ ->
	       lambda_name env
		 (n,imp,t,process_constr (push_rel d env) (i+1)
		    (whd_beta (applist (lift 1 f, [(mkRel 1)],[imp])))
		    (cprest,rest)))
    | (n,imp,Some c,t as d)::cprest, rest ->
	mkLetIn
	  (n,imp,c,t,
	   process_constr (push_rel d env) (i+1) (lift 1 f) (cprest,rest))
    | [],[] -> f
    | _ -> anomaly "process_constr"

  in
  process_constr env 0 f (List.rev cstr.cs_args, recargs)


(* Cut a context ctx in 2 parts (ctx1,ctx2) with ctx1 containing k 
   variables *)
let context_chop k ctx = 
  let rec chop_aux acc = function
    | (0, l2) -> (List.rev acc, l2)
    | (n, ((_,_,Some _,_ as h)::t)) -> chop_aux (h::acc) (n, t)
    | (n, (h::t)) -> chop_aux (h::acc) (pred n, t)
    | (_, []) -> failwith "context_chop"
  in chop_aux [] (k,ctx)


(* Main function *)
let mis_make_indrec env sigma listdepkind mib =
  let nparams = mib.mind_nparams in
  let nparrec = mib. mind_nparams_rec in
  let lnonparrec,lnamesparrec = 
    context_chop (nparams-nparrec) mib.mind_params_ctxt in
  let nrec = List.length listdepkind in
  let depPvec =
    Array.create mib.mind_ntypes (None : (bool * constr) option) in 
  let _ = 
    let rec 
	assign k = function 
	  | [] -> ()
          | (indi,mibi,mipi,dep,_)::rest -> 
              (Array.set depPvec (snd indi) (Some(dep,mkRel k));
               assign (k-1) rest)
    in 
      assign nrec listdepkind in 
  let recargsvec =
    Array.map (fun mip -> mip.mind_recargs) mib.mind_packets in
  (* recarg information for non recursive parameters *)
  let rec recargparn l n = 
    if n = 0 then l else recargparn (mk_norec::l) (n-1) in
  let recargpar = recargparn [] (nparams-nparrec) in
  let make_one_rec p =
    let makefix nbconstruct =
      let rec mrec i ln ltyp ldef = function
	| (indi,mibi,mipi,dep,_)::rest ->
	    let tyi = snd indi in
	    let nctyi =
              Array.length mipi.mind_consnames in (* nb constructeurs du type*)
	      
            (* arity in the context of the fixpoint, i.e.
             * P1..P_nrec f1..f_nbconstruct
             * (only recursive params are instantiated) *)
	    let indf =
	      let (args,aimps) =
                extended_rel_list (nrec+nbconstruct) lnamesparrec in
              make_ind_family(indi,args,aimps) in
	    let arsign,_ = get_arity env indf in
	    let depind = build_dependent_inductive env indf in
	    let deparsign = (Anonymous,Expl,None,depind)::arsign in
            let lam_arsign =
              (Anonymous,Expl,None,depind)::set_impl_rel_context Impl arsign in

	    let nonrecpar = rel_context_length lnonparrec in
	    let larsign = rel_context_length deparsign in
	    let ndepar = larsign - nonrecpar in
	    let dect = larsign+nrec+nbconstruct in

            (* constructors in context of the Cases expr, i.e.
               P1..P_nrec f1..f_nbconstruct F_1..F_nrec a_1..a_nar x:I *)
	    let (args',aimps') = extended_rel_list (dect+nrec) lnamesparrec in
	    let (args'',aimps'') = extended_rel_list ndepar lnonparrec in
            let indf' =
              make_ind_family(indi,args'@args'',aimps'@aimps'') in
	      
	    let depind' = build_dependent_inductive env indf' in
	    let arsign',_ = get_arity env indf' in
	    let deparsign' = (Anonymous,Expl,None,depind')::arsign' in
	      
	    (* body of i-th component of the mutual fixpoint *)
	    let j =
              (match depPvec.(tyi) with 
	        | Some (_,c) when isRel c -> destRel c 
		| _ -> assert false)  in
	    let deftyi = 
	      let ci = make_case_info env indi RegularStyle in
	      (* Predicate (in the context of the case) *)
	      let pred =
	        let (nrpar,nrpimps) =
                  extended_rel_list (2*ndepar) lnonparrec in
	        let (ar,aimps) =
                  if dep then extended_rel_list 0 deparsign'
	          else extended_rel_list 1 arsign' in
                let concl =
                  applist (mkRel (dect+j+ndepar),nrpar@ar,nrpimps@aimps) in 
		it_mkLambda_or_LetIn_name env 
		  ((if dep then mkLambda_name env else mkLambda)
		    (Anonymous,Expl,depind',concl))
		  arsign' in
	      let branches = 
	        let constrs = get_constructors env indf' in
	        let fi = rel_vect (dect-i-nctyi) nctyi in
                (* apply non-recursive parameters (implicit) *)
                let (inst,imps) =
	          extended_rel_vect ndepar
                    (set_impl_rel_context Impl lnonparrec) in
                let vecfi = Array.map (fun f -> appvect (f,inst,imps)) fi in
	        array_map3
		  (make_rec_branch_arg env sigma 
		    (nparrec,depPvec,larsign))
                  vecfi constrs (dest_subterms recargsvec.(tyi)) in
	      it_mkLambda_or_LetIn_name env
		(mkCase (ci, pred, 
		             mkRel 1,
			     branches))
		(lift_rel_context nrec lam_arsign)
	    in
	      
	    (* type of i-th component of the mutual fixpoint *)
	    let typtyi =
	      let concl = 
	        let pargs,paimps =
                  if dep then extended_rel_vect 0 deparsign
	          else extended_rel_vect 1 arsign in
                appvect (mkRel(nbconstruct+ndepar+nonrecpar+j),pargs,paimps)
	      in
              it_mkProd_or_LetIn_name env concl lam_arsign
	    in

	    mrec (i+nctyi) (rel_context_nhyps arsign ::ln) (typtyi::ltyp) 
                 (deftyi::ldef) rest
        | [] -> 
	    let fixn = Array.of_list (List.rev ln) in
            let fixtyi = Array.of_list (List.rev ltyp) in
            let fixdef = Array.of_list (List.rev ldef) in 
            let names = Array.create nrec (Name(id_of_string "F")) in
	      mkFix ((fixn,p),(names,fixtyi,fixdef))
      in 
      mrec 0 [] [] [] 
    in 
    let rec make_branch env i = function 
      | (indi,mibi,mipi,dep,_)::rest ->
          let tyi = snd indi in
	  let nconstr = Array.length mipi.mind_consnames in
	  let rec onerec env j = 
	    if j = nconstr then 
	      make_branch env (i+j) rest 
	    else 
	      let recarg = (dest_subterms recargsvec.(tyi)).(j) in
	      let recarg = recargpar@recarg in
	      let (vargs,_) = extended_rel_list (nrec+i+j) lnamesparrec in
	      let cs = get_constructor (indi,mibi,mipi,vargs) (j+1) in
	      let p_0 =
		type_rec_branch
                  true dep env sigma (vargs,depPvec,i+j) tyi cs recarg
	      in 
	      mkLambda_string "f" Expl p_0
		(onerec (push_rel (Anonymous,Expl,None,p_0) env) (j+1))
	  in onerec env 0
      | [] -> 
	  makefix i listdepkind
    in
    let rec put_arity env i = function 
      | (indi,_,_,dep,kinds)::rest -> 
          let (inst,imps) = extended_rel_list i lnamesparrec in
	  let indf = make_ind_family(indi,inst,imps) in
	  let typP = make_arity env dep indf (new_sort_in_family kinds) in
	  mkLambda_string "P" Impl typP
	    (put_arity (push_rel (Anonymous,Impl,None,typP) env) (i+1) rest)
      | [] -> 
	  make_branch env 0 listdepkind 
    in
      
    (* Body on make_one_rec *)
    let (indi,mibi,mipi,dep,kind) = List.nth listdepkind p in

    if mis_is_recursive_subset
      (List.map (fun (indi,_,_,_,_) -> snd indi) listdepkind)
      mipi.mind_recargs
    then 
    let env' = push_rel_context lnamesparrec env in
      it_mkLambda_or_LetIn_name env (put_arity env' 0 listdepkind) 
	(set_impl_rel_context Impl lnamesparrec)
    else 
      mis_make_case_com (Some dep) env sigma indi (mibi,mipi) kind 
  in 
    (* Body of mis_make_indrec *)
    list_tabulate make_one_rec nrec

(**********************************************************************)
(* This builds elimination predicate for Case tactic *)

let make_case_com depopt env sigma ity kind =
  let (mib,mip) = lookup_mind_specif env ity in 
    mis_make_case_com depopt env sigma ity (mib,mip) kind

let make_case_dep env   = make_case_com (Some true) env
let make_case_nodep env = make_case_com (Some false) env 
let make_case_gen env   = make_case_com None env


(**********************************************************************)
(* [instantiate_indrec_scheme s rec] replace the sort of the scheme
   [rec] by [s] *)

let change_sort_arity sort = 
  let rec drec a = match kind_of_term a with
    | Cast (c,_,_) -> drec c 
    | Prod (n,imp,t,c) -> mkProd (n, imp, t, drec c)
    | LetIn (n,imp,b,t,c) -> mkLetIn (n,imp,b, t, drec c)
    | Sort _ -> mkSort sort
    | _ -> assert false
  in 
    drec 

(* [npar] is the number of expected arguments (then excluding letin's) *)
let instantiate_indrec_scheme sort =
  let rec drec npar elim =
    match kind_of_term elim with
      | Lambda (n,imp,t,c) -> 
	  if npar = 0 then 
	    mkLambda (n, imp, change_sort_arity sort t, c)
	  else 
	    mkLambda (n, imp, t, drec (npar-1) c)
      | LetIn (n,imp,b,t,c) -> mkLetIn (n,imp,b,t,drec npar c)
      | _ -> anomaly "instantiate_indrec_scheme: wrong elimination type"
  in
  drec

(* Change the sort in the type of an inductive definition, builds the
   corresponding eta-expanded term *)
let instantiate_type_indrec_scheme sort npars term =
  let rec drec np imps elim =
    match kind_of_term elim with
      | Prod (n,imp,t,c) -> 
	  if np = 0 then 
            let t' = change_sort_arity sort t in
            mkProd (n, imp, t', c),
            mkLambda (n, imp, t',
              mkApp(term,Termops.rel_vect 0 (npars+1),
                    Array.of_list(List.rev(imp::imps))))
	  else 
            let c',term' = drec (np-1) (imp::imps) c in
	    mkProd (n, imp, t, c'), mkLambda (n, imp, t, term')
      | LetIn (n,imp,b,t,c) -> let c',term' = drec np imps c in
           mkLetIn (n,imp,b,t,c'), mkLetIn (n,imp,b,t,term') 
      | _ -> anomaly "instantiate_type_indrec_scheme: wrong elimination type"
  in
  drec npars []

(**********************************************************************)
(* Interface to build complex Scheme *)
(* Check inductive types only occurs once 
(otherwise we obtain a meaning less scheme) *)

let check_arities listdepkind = 
  let _ = List.fold_left
    (fun ln ((_,ni as mind),mibi,mipi,dep,kind) -> 
       let id = mipi.mind_typename  in
       let kelim = elim_sorts (mibi,mipi) in
       if not (List.exists ((=) kind) kelim) then raise
	 (RecursionSchemeError (BadInduction (dep,id,new_sort_in_family kind)))
       else if List.mem ni ln then raise
	 (RecursionSchemeError (NotMutualInScheme (mind,mind)))
       else ni::ln)
	    [] listdepkind
  in true

let build_mutual_indrec env sigma = function 
  | (mind,mib,mip,dep,s)::lrecspec ->
      let (sp,tyi) = mind in
      let listdepkind = 
    	(mind,mib,mip, dep,s)::
    	(List.map
	   (function (mind',mibi',mipi',dep',s') ->
	      let (sp',_) = mind' in
	      if sp=sp' then 
                let (mibi',mipi') = lookup_mind_specif env mind' in
		(mind',mibi',mipi',dep',s') 
	      else 
		raise (RecursionSchemeError (NotMutualInScheme (mind,mind'))))
	   lrecspec)
      in
      let _ = check_arities listdepkind in 
      mis_make_indrec env sigma listdepkind mib
  | _ -> anomaly "build_indrec expects a non empty list of inductive types"

let build_indrec env sigma ind =
  let (mib,mip) = lookup_mind_specif env ind in
  let kind = inductive_sort_family mip in
  let dep = kind <> InProp in
    List.hd (mis_make_indrec env sigma [(ind,mib,mip,dep,kind)] mib)

(**********************************************************************)
(* To handle old Case/Match syntax in Pretyping                       *)

(*****************************************)
(* To interpret Case and Match operators *)
(* Expects a dependent predicate *)

let type_rec_branches recursive env sigma indt p c = 
  let IndType (indf,realargs,raimps) = indt in
  let (ind,params,pimps) = dest_ind_family indf in
  let (mib,mip) = lookup_mind_specif env ind in
  let recargs = mip.mind_recargs in
  let tyi = snd ind in
  let init_depPvec i = if i = tyi then Some(true,p) else None in
  let depPvec = Array.init mib.mind_ntypes init_depPvec in
  let constructors = get_constructors env indf in
  let lft =
    array_map2
      (type_rec_branch recursive true env sigma (params,depPvec,0) tyi)
      constructors (dest_subterms recargs) in
  (lft,Reduction.beta_appvect p (Array.of_list (realargs@[c]))
    (Array.of_list(raimps@[Expl])))
(* Non recursive case. Pb: does not deal with unification
    let (p,ra,_) = type_case_branches env (ind,params@realargs) pj c in
    (p,ra)
*)

(*s Eliminations. *)

let elimination_suffix = function
  | InProp -> "_ind"
  | InSet  -> "_rec"
  | InType -> "_rect"

let make_elimination_ident id s = add_suffix id (elimination_suffix s)

(* Look up function for the default elimination constant *)

let lookup_eliminator ind_sp s =
  let kn,i = ind_sp in
  let mp,dp,l = repr_kn kn in
  let ind_id = (Global.lookup_mind kn).mind_packets.(i).mind_typename in
  let id = add_suffix ind_id (elimination_suffix s) in
  (* Try first to get an eliminator defined in the same section as the *)
  (* inductive type *)
  let ref = ConstRef (make_con mp dp (label_of_id id)) in
  try 
    let _ = sp_of_global ref in
    constr_of_global ref
  with Not_found ->
  (* Then try to get a user-defined eliminator in some other places *)
  (* using short name (e.g. for "eq_rec") *)
  try constr_of_global (Nametab.locate (make_short_qualid id))
  with Not_found ->
    errorlabstrm "default_elim"
      (str "Cannot find the elimination combinator " ++
       pr_id id ++ spc () ++
       str "The elimination of the inductive definition " ++
       pr_id id ++ spc () ++ str "on sort " ++ 
       spc () ++ pr_sort_family s ++
       str " is probably not allowed")


(*  let env = Global.env() in
  let path = sp_of_global None (IndRef ind_sp) in
  let dir, base = repr_path path in
  let id = add_suffix base (elimination_suffix s) in
  (* Try first to get an eliminator defined in the same section as the *)
  (* inductive type *)
  try construct_absolute_reference (Names.make_path dir id)
  with Not_found ->
  (* Then try to get a user-defined eliminator in some other places *)
  (* using short name (e.g. for "eq_rec") *)
    try constr_of_global (Nametab.locate (make_short_qualid id))
    with Not_found ->
      errorlabstrm "default_elim"
	(str "Cannot find the elimination combinator " ++
           pr_id id ++ spc () ++
	   str "The elimination of the inductive definition " ++
           pr_id base ++ spc () ++ str "on sort " ++ 
           spc () ++ pr_sort_family s ++
	   str " is probably not allowed")
*)

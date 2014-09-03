open Names
open Declarations
open Term
open Environ
open Inductive
open Reduction 
open Vm

(*******************************************)
(* Calcul de la forme normal d'un terme    *)
(*******************************************)

let crazy_type = mkSet 

let decompose_prod env t =
  let (name,imp,dom,codom as res) = destProd (whd_betadeltaiota env t) in
  if name = Anonymous then (Name (id_of_string "x"),imp,dom,codom)
  else res

exception Find_at of int

(* rend le numero du constructeur correspondant au tag [tag],
   [cst] = true si c'est un constructeur constant *)

let invert_tag cst tag reloc_tbl =
  try 
    for j = 0 to Array.length reloc_tbl - 1 do
      let tagj,arity = reloc_tbl.(j) in
      if tag = tagj && (cst && arity = 0 || not(cst || arity = 0)) then
	raise (Find_at j)
      else ()
    done;raise Not_found 
  with Find_at j -> (j+1)   
             (* Argggg, ces constructeurs de ... qui commencent a 1*)

let find_rectype_a env c =
  let (t, l, imps) = 
    let t = whd_betadeltaiota env c in
    try destApp t with _ -> (t,[||],[||]) in
  match kind_of_term t with
  | Ind ind -> (ind, l, imps)
  | _ -> raise Not_found

(* Instantiate inductives and parameters in constructor type *)

let type_constructor mind mib typ params = 
  let s = ind_subst mind mib in
  let ctyp = substl s typ in
  let nparams = Array.length params in
  if nparams = 0 then ctyp
  else
    let _,ctyp = decompose_prod_n nparams ctyp in   
    substl (List.rev (Array.to_list params)) ctyp

(* arnaud: to clean 
(* spiwack: auxiliary fonction for decompiling 31-bit integers
   into their corresponding constr *)
let constr_of_int31 =
  let nth_digit_plus_one i n = (* calculates the nth (starting with 0)
                                  digit of i and adds 1 to it 
                                  (nth_digit_plus_one 1 3 = 2) *)
      if (land) i ((lsl) 1 n) = 0 then
         1
      else
         2
  in
  fun tag -> fun ind->
  let digit_ind = Retroknowledge.digits_of_int31 ind 
  in
  let array_of_int i =
    Array.init 31 (fun n -> mkConstruct(digit_ind, nth_digit_plus_one i (30-n)))
  in
    mkApp(mkConstruct(ind, 1), array_of_int tag) *)

(* /spiwack *)
(* arnaud
let construct_of_constr_const env tag typ =
  let ind,params = find_rectype env typ in
  (* arnaud:improve comment ? *)
  (* spiwack: branching for 31-bits integers *)
(* arnaud:
  if Retroknowledge.isInt31t ind then
    constr_of_int31 tag ind
  else *)
  try 
    retroknowledge Retroknowledge.get_vm_decompile_constant_info env (Ind ind) tag
  with Not_found ->
    let (_,mip) = lookup_mind_specif env ind in
    let i = invert_tag true tag mip.mind_reloc_tbl in
    applistc (mkConstruct(ind,i))  params *)

let construct_of_constr const env tag typ =
  let (mind,_ as ind), allargs, _ = find_rectype_a env typ in
  (* spiwack : here be a branch for specific decompilation handled by retroknowledge *)
  try
    if const then
      ((retroknowledge Retroknowledge.get_vm_decompile_constant_info env (Ind ind) tag),
       typ) (*spiwack: this may need to be changed in case there are parameters in the
	               type which may cause a constant value to have an arity.
	               (type_constructor seems to be all about parameters actually)
	               but it shouldn't really matter since constant values don't use
	               their ctyp in the rest of the code.*)
    else
      raise Not_found (* No retroknowledge function (yet) for block decompilation *)
  with Not_found ->
    let mib,mip = lookup_mind_specif env ind in
    let nparams = mib.mind_nparams in
    let i = invert_tag const tag mip.mind_reloc_tbl in
    let params = Array.sub allargs 0 nparams in
    let imps = Array.create nparams Impl in
    let ctyp = type_constructor mind mib (mip.mind_nf_lc.(i-1)) params in
      (mkApp(mkConstruct(ind,i), params, imps), ctyp)

let construct_of_constr_const env tag typ = 
  fst (construct_of_constr true env tag typ)

let construct_of_constr_block = construct_of_constr false

let constr_type_of_idkey env idkey =
  match idkey with
  | ConstKey cst ->
      mkConst cst, Typeops.type_of_constant env cst
  | VarKey id -> 
      let (_,_,_,ty) = lookup_named id env in 
      mkVar id, ty
  | RelKey i -> 
      let n = (nb_rel env - i) in
      let (_,_,_,ty) = lookup_rel n env in
      mkRel n, lift n ty

let type_of_ind env ind = 
  type_of_inductive env (Inductive.lookup_mind_specif env ind)

let build_branches_type env (mind,_ as _ind) mib mip params dep p =
  let rtbl = mip.mind_reloc_tbl in
  (* [build_one_branch i cty] construit le type de la ieme branche (commence
     a 0) et les lambda correspondant aux realargs *)
  let build_one_branch i cty =
    let typi = type_constructor mind mib cty params in
    let decl,indapp = Sign.decompose_prod_assum typi in
    let ind,cargs,imps = find_rectype_a env indapp in
    let nparams = Array.length params in
    let carity = snd (rtbl.(i)) in
    let crealargs = Array.sub cargs nparams (Array.length cargs - nparams) in
    let crealimps = Array.sub imps nparams (Array.length cargs - nparams) in
    let codom = 
      let papp = mkApp(p,crealargs,crealimps) in
      if dep then
	let cstr = ith_constructor_of_inductive ind (i+1) in
        let relargs = Array.init carity (fun i -> mkRel (carity-i)) in
        let pimps = Array.map (fun _ -> Impl) params in
	let dep_cstr =
          mkApp(mkApp(mkConstruct cstr,params,pimps),relargs,crealimps) in
	mkApp(papp,[|dep_cstr|],[|Expl|])
      else papp
    in 
    decl, codom
  in Array.mapi build_one_branch mip.mind_nf_lc

let build_case_type dep p realargs imps c = 
  if dep then mkApp(mkApp(p, realargs, imps), [|c|], [|Expl|])
  else mkApp(p, realargs, imps)

(* La fonction de normalisation *)

let rec nf_val env v t = nf_whd env (whd_val v) t 

and nf_vtype env v =  nf_val env v crazy_type

and nf_whd env whd typ =
  match whd with
  | Vsort s -> mkSort s
  | Vprod p ->
      let dom = nf_vtype env (dom p) in
      let name = Name (id_of_string "x") in
      let vc = body_of_vfun (nb_rel env) (codom p) in
      let imp = imp p in
      let codom = nf_vtype (push_rel (name,Expl,None,dom) env) vc  in      
      mkProd(name,imp,dom,codom)
  | Vfun f -> nf_fun env f typ
  | Vfix(f,None) -> nf_fix env f
  | Vfix(f,Some vargs) -> fst (nf_fix_app env f vargs)
  | Vcofix(cf,_,None) -> nf_cofix env cf 
  | Vcofix(cf,_,Some vargs) -> 
      let cfd = nf_cofix env cf in
      let i,(_,ta,_) = destCoFix cfd in
      let t = ta.(i) in
      let _, args, imps = nf_args env vargs t in
      mkApp(cfd,args,imps) 
  | Vconstr_const n -> construct_of_constr_const env n typ
  | Vconstr_block b ->
      let capp,ctyp = construct_of_constr_block env (btag b) typ in
      let args,imps = nf_bargs env b ctyp in
      mkApp(capp,args,imps)
  | Vatom_stk(Aid idkey, stk) ->
      let c,typ = constr_type_of_idkey env idkey in
      nf_stk env c typ stk
  | Vatom_stk(Aiddef(idkey,v), stk) ->
      nf_whd env (whd_stack v stk) typ
  | Vatom_stk(Aind ind, stk) ->
      nf_stk env (mkInd ind) (type_of_ind env ind) stk 
	
and nf_stk env c t stk  =
  match stk with
  | [] -> c
  | Zapp vargs :: stk ->
      let t, args, imps = nf_args env vargs t in
      nf_stk env (mkApp(c,args,imps)) t stk 
  | Zfix (f,vargs) :: stk ->  
      let fa, typ = nf_fix_app env f vargs in
      let _,imp,_,codom = decompose_prod env typ in
      nf_stk env (mkApp(fa,[|c|],[|imp|])) (subst1 c codom) stk
  | Zswitch sw :: stk -> 
      let (mind,_ as ind),allargs,imps = find_rectype_a env t in
      let (mib,mip) = Inductive.lookup_mind_specif env ind in
      let nparams = mib.mind_nparams in
      let params,realargs = Util.array_chop nparams allargs in
      let pimps, rimps = Util.array_chop nparams imps in
      let pT = 
	hnf_prod_applist env (type_of_ind env ind) (Array.to_list params) in
      let dep, p =
        nf_predicate env ind mip params pimps (type_of_switch sw) pT in
      (* Calcul du type des branches *)
      let btypes = build_branches_type env ind mib mip params dep p in
      (* calcul des branches *)
      let bsw = branch_of_switch (nb_rel env) sw in
      let mkbranch i (n,v) =
	let decl,codom = btypes.(i) in
	let env =  push_rel_context decl env in
	let b = nf_val env v codom in
	Sign.it_mkProd_or_LetIn b decl
      in 
      let branchs = Array.mapi mkbranch bsw in
      let tcase = build_case_type dep p realargs rimps c in
      let ci = case_info sw in
      nf_stk env (mkCase(ci, p, c, branchs)) tcase stk

and nf_predicate env ind mip params pimps v pT =
  match whd_val v, kind_of_term pT with
  | Vfun f, Prod _ ->
      let k = nb_rel env in
      let vb = body_of_vfun k f in
      let name,imp,dom,codom = decompose_prod env pT in
      let dep,body = 
	nf_predicate (push_rel (name,imp,None,dom) env) 
          ind mip params pimps vb codom in
      dep, mkLambda(name,imp,dom,body)
  | Vfun f, _ -> 
      let k = nb_rel env in
      let vb = body_of_vfun k f in
      let name = Name (id_of_string "c") in
      let n = mip.mind_nrealargs in
      let rargs = Array.init n (fun i -> mkRel (n-i)) in
      let rimps = Sign.imps_from_rel_context mip.mind_arity_ctxt in
      let dom =
        mkApp(mkApp(mkInd ind,params,pimps),rargs,Array.of_list rimps) in
      let body = nf_vtype (push_rel (name,Expl,None,dom) env) vb in
      true, mkLambda(name,Expl,dom,body)
  | _, _ -> false, nf_val env v crazy_type
	
and nf_args env vargs t =
  let t = ref t in
  let len = nargs vargs in
  let imps = Array.create len Expl in
  let args = 
    Array.init len 
      (fun i ->
	let _,imp,dom,codom = decompose_prod env !t in
        imps.(i) <- imp;
	let c = nf_val env (arg vargs i) dom in
	t := subst1 c codom; c) in
  !t,args,imps

and nf_bargs env b t =
  let t = ref t in
  let len = bsize b in
  let imps = Array.create len Expl in
  let args =
    Array.init len 
      (fun i -> 
	let _,imp,dom,codom = decompose_prod env !t in
        imps.(i) <- imp;
	let c = nf_val env (bfield b i) dom in
	t := subst1 c codom; c) in
  args,imps

and nf_fun env f typ =
  let k = nb_rel env in
  let vb = body_of_vfun k f in
  let name,imp,dom,codom = decompose_prod env typ in
  let body = nf_val (push_rel (name,imp,None,dom) env) vb codom in
  mkLambda(name,imp,dom,body)

and nf_fix env f =
  let init = current_fix f in
  let rec_args = rec_args f in
  let k = nb_rel env in
  let vb, vt = reduce_fix k f in
  let ndef = Array.length vt in
  let ft = Array.map (fun v -> nf_val env v crazy_type) vt in
  let name = Array.init ndef (fun _ -> (Name (id_of_string "Ffix"))) in
  let env = push_rec_types (name,ft,ft) env in 
  let fb = Util.array_map2 (fun v t -> nf_fun env v t) vb ft in
  mkFix ((rec_args,init),(name,ft,fb))
      
and nf_fix_app env f vargs =
  let fd = nf_fix env f in
  let (_,i),(_,ta,_) = destFix fd in
  let t = ta.(i) in
  let t, args, imps = nf_args env vargs t in
  mkApp(fd,args,imps),t
  
and nf_cofix env cf =
  let init = current_cofix cf in
  let k = nb_rel env in
  let vb,vt = reduce_cofix k cf in
  let ndef = Array.length vt in
  let cft = Array.map (fun v -> nf_val env v crazy_type) vt in
  let name = Array.init ndef (fun _ -> (Name (id_of_string "Fcofix"))) in
  let env = push_rec_types (name,cft,cft) env in 
  let cfb = Util.array_map2 (fun v t -> nf_val env v t) vb cft in
  mkCoFix (init,(name,cft,cfb))
  
let cbv_vm env c t  =
  let transp = transp_values () in
  if not transp then set_transp_values true; 
  let v = Vconv.val_of_constr env c in
  let c = nf_val env v t in
  if not transp then set_transp_values false; 
  c
  

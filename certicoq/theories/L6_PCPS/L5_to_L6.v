(* Convertion from 
       simple_cps.cps 
              to
       cps.exp
    resulting in globally unique names  

  2015 - Olivier Savary Belanger 




   DONE: fix recursive definition of list-based convert for termination checker
      for some reason wouldn't accept termination even when rewritten with fold_right, had to pull up all 3 list-based convert as definitions 
   DONE : modify convert_v s.t. it doesn't bind Var and KVar to a new name (e.g. by returning list of bindings) 
   TODO : populate the types (ty atm) within expressions

*)     
Require Import ZArith.
Require Import Znumtheory.
Require Import List.
Require Import Bool.
Require Maps.
Require Recdef.
Import Nnat.
Require Import CpdtTactics.


Require Import List.
Add LoadPath "../L4_Cps".
Add LoadPath "./L4_Cps".
Require Import simple_cps. (* using cps for db cps terms *)
Require Import cps. (* shadows exp from simple_cps for nominal cps terms *)


(* applicative context on cps.exp *)
Inductive ctx_exp : Type :=
| Chole : ctx_exp
| Cconstr : var -> type -> tag -> list var -> ctx_exp -> ctx_exp
| Cproj: var -> type -> N -> var -> ctx_exp -> ctx_exp
| Cfun1: ctx_fundefs -> exp -> ctx_exp
| Cfun2: fundefs -> ctx_exp -> ctx_exp
| Cprim : var -> type -> prim -> list var -> ctx_exp -> ctx_exp
with ctx_fundefs :=
     | Ccons1 : var -> type -> list var -> ctx_exp -> fundefs -> ctx_fundefs
     | Ccons2 : var -> type -> list var -> exp -> ctx_fundefs -> ctx_fundefs
.


Fixpoint app_ctx_exp_f (c:ctx_exp) (e:exp) : exp :=
  match c with
  | Chole => e
  | Cconstr v t g lv c' => Econstr v t g lv (app_ctx_exp_f c' e)
  | Cprim v t p lv c' => Eprim v t p lv (app_ctx_exp_f c' e)
  | Cfun1 cfds e' => Efun (app_ctx_fds_f cfds e) e'
  | Cfun2 fds c' => Efun fds (app_ctx_exp_f c' e)
  | Cproj v t n y c' => Eproj v t n y (app_ctx_exp_f c' e)
  end
with app_ctx_fds_f (c:ctx_fundefs) (e:exp) : fundefs :=
       match c with
       | Ccons1 f t ys c' fds => Fcons f t ys (app_ctx_exp_f c' e) fds
       | Ccons2 f t ys e' cfds' => Fcons f t ys e' (app_ctx_fds_f cfds' e)
       end.


Fixpoint comp_ctx_exp_f (c1:ctx_exp) (c2:ctx_exp) : ctx_exp :=
  match c1 with
  | Chole => c2
  | Cconstr v t g lv c' => Cconstr v t g lv (comp_ctx_exp_f c' c2)
  | Cprim v t p lv c' => Cprim v t p lv (comp_ctx_exp_f c' c2)
  | Cfun1 cfds e' => Cfun1 (comp_ctx_fds_f cfds c2) e'
  | Cfun2 fds c' => Cfun2 fds (comp_ctx_exp_f c' c2)
  | Cproj v t n y c' => Cproj v t n y (comp_ctx_exp_f c' c2)
  end
with comp_ctx_fds_f (c1:ctx_fundefs) (c2:ctx_exp) : ctx_fundefs :=
       match c1 with
       | Ccons1 f t ys c' fds => Ccons1 f t ys (comp_ctx_exp_f c' c2) fds
       | Ccons2 f t ys e' cfds' => Ccons2 f t ys e' (comp_ctx_fds_f cfds' c2)
       end.



(* returns list of numbers from n to n+m (excluding n+m) *)
Fixpoint fromN (n:positive) (m:nat) : list positive :=
  match m with
  | O => nil
  | S m' => n::(fromN (n+1) (m'))
  end.





(* placeholder *)
Variable default_tag : M.elt.
Definition dcon_to_tag: dcon -> tag := N.succ_pos. (* should probably change dcon to positive in simple_cps *)
Variable var_tag : M.elt.
Variable kvar_tag : M.elt.
Variable rec_tag : M.elt.

Variable ty_fun : positive. (* Regular function (lam) in simple_cps *)
Variable ty_con : positive. (* continuation in simple_cps *)
Variable ty : positive.  (* everything else *)

(* create a context binding m projections of var n to var (n+1+m)
 i.e. each binding has form  ({| let var (n + m + 1) := \pi_(m-1) var n in [] |})
 *)
SearchAbout (N -> N -> Prop).

Function ctx_bind_proj (n:positive) (m:N) {wf N.lt m}: ctx_exp :=
  if N.eqb m 0%N then
    Chole
  else
    let ctx_p' := ctx_bind_proj n (N.pred m) in
    Cproj (Pos.add n (N.succ_pos m)) ty (N.pred m ) n ctx_p'.
Proof.
  intros. apply N.lt_pred_l.  apply N.eqb_neq in teq. assumption. apply N.lt_wf_0. 
Qed.



(* Translates a list of branch cps into
   (1) a set of cps.exp functions (fundefs) representing the branches' continuation
   (2) a list of pairs grouping the tag with their continuation name
   (3) the next fresh name *)
Definition convert_branches (convert: cps -> (list var) -> (list var) -> var -> (exp * var)) (bl: list (branch cps)) (sv: list var) (sk: list var) (n:var) (* {| struct bl |} *): (fundefs * list (tag * var) * var)  :=
  fold_right
             (* {| n -> k, \ n+1 . (let n+2 <- \pi_1 n+1 ... n+m+1 <- \pi_m n+1 in  ce |}  *) 
             (fun (b:branch cps) (fltv: fundefs * list (tag * var) * var) => 
                let (dm, e) := b in
                let (dcn, m) := dm in
                let  (ll, n') := fltv in
                let (cfds, cbl) := ll in
                let ctx_p := ctx_bind_proj (Pos.succ n') m in 
                let nm2 := Pos.add n' (Pos.succ (N.succ_pos m)) in (* compute next available var name after binding m projections starting at n'+2 *)
                let xs := fromN (Pos.add n' 2) (N.to_nat m) in
                let (ce, n'') :=  convert e (xs++sv) sk nm2 in 
                (Fcons n' ty_con ((Pos.succ n')::nil) (app_ctx_exp_f ctx_p ce) cfds, ((dcon_to_tag dcn), n')::cbl ,   n''))
             (Fnil, nil, n)
             bl.


Definition convert_v_list (convert_v: val_c -> (list var) -> (list var) -> var -> (ctx_exp * var * var)) (lv :list val_c) (sv : list var) (sk: list var) (n: var) : (ctx_exp * list var * var) :=
      
           fold_right
             (fun  v (flvv:ctx_exp * list var * var)  =>
               let (ll, n') := flvv in
               let (ctx_lv', ln') := ll in
               let (ll, n'') := convert_v v sv sk n' in
               let (ctx_v, vn) := ll in
               (comp_ctx_exp_f ctx_v ctx_lv', (vn::ln'), n''))
             (Chole, nil, n)
             lv.



(* convert a list of simple_cps cps functions into 
 (1) a set of cps.exp functions (fundefs), each referring to a local variable (n'+1), a local continuation variable (n'+2) and the records' name nfds
 (2) the functions' name (as a list var) 
 (3) the next fresh name *)
Definition convert_fds (convert: cps -> (list var) -> (list var) -> var -> (exp * var)) ( fds : list cps)  (sv: list var) (sk : list var) (n : var) (nfds: var) : (fundefs * list var *  var)  :=
           fold_right
             (fun e (flvv: fundefs * list var * var) =>
                 let (ll, n') := flvv in
                 let (cfds, ln) := ll in
                 let (ce, n'') := convert e ((Pos.succ n')::nfds::sv) ((Pos.add n' 2)::sk) ((Pos.add n' 3)) in
                 (Fcons n' ty_fun ((Pos.succ n')::(Pos.add n' 2)::nil) ce cfds, n'::ln, n''))
             (Fnil, nil, n)
             fds.



(* 
  sv is a stack used to convert variable indices to name
sk is a stack mapping continuation indices to name
n is the next available name.

returns pair of converted expression e' and the next available variable name n'
        The names bound in e' are exactly [n, n'[

note : var "2" is taken as an external function standing for "halt"
       var "1" is taken as error and will be proven not to appear when input is well-scoped                           

      Mutually recursive function are bound as a single (explicit) record
      Continuation for pattern matching take a single argument whose m projections are bound to unique variables 


*)

Fixpoint convert (e:cps) (sv:list var) (sk:list var) (n:var) (*{| struct e |}*) : exp * var :=
       match e with
       | Halt_c v => let (ll, n') := convert_v v sv sk n in
                     let (ctx_v, vn) := ll in
                         (app_ctx_exp_f ctx_v (Eapp (2%positive) (vn::nil) ), n')
       | Ret_c k v => let (ll1, n') := convert_v k sv sk n in
                      let (ctx_k, kn) := ll1 in
                      let (ll2, n'') := convert_v v sv sk n' in
                      let (ctx_v, vn) := ll2 in
                       (app_ctx_exp_f (comp_ctx_exp_f ctx_k ctx_v) (Eapp kn (vn::nil)), n'')
       | Call_c f k v =>
         let (ll1, n') := convert_v f sv sk n in
         let (ctx_f, fn) := ll1 in
         let (ll2, n'') := convert_v k sv sk n' in
         let (ctx_k, kn) := ll2 in
         let (ll3, n''') := convert_v v sv sk n'' in
         let (ctx_v, vn) := ll3 in
         let ctx_fkv := comp_ctx_exp_f ctx_f (comp_ctx_exp_f ctx_k ctx_v) in
         (app_ctx_exp_f ctx_fkv (Eapp fn (vn::kn::nil)), n''')
         
      | Match_c v bl =>
        let (ll, n') := convert_v v sv sk n in
        let (ctx_v, vn) := ll in
        let (fl, n'') := convert_branches convert bl sv sk n' in
        let (fds, tvl) := fl in
         (app_ctx_exp_f ctx_v (Efun fds (Ecase vn tvl)), n'')
      | Proj_c f nth k =>
        let (ll1, n') := convert_v f sv sk n in
        let (ctx_f, fn) := ll1 in
        let (ll2, n'') := convert_v k sv sk n' in
        let (ctx_k, kn) := ll2 in
        let ctx_fk := comp_ctx_exp_f ctx_f ctx_k in
        (* projection from the record is applied to the (converted) continuation k *) 
            (Eproj n'' ty nth (Pos.pred n') (Eapp (Pos.pred n'') (n''::nil)), Pos.succ n'')
       end
(* returns converted context * new binding (usually n'-1 except for var and kvar) * next fresh name *)
    with convert_v (v:val_c) (sv: list var) (sk: list var) (n:var) (* {| struct v |} *): (ctx_exp * var * var) :=
           match v with
           | Var_c m => (Chole, (nth (N.to_nat m) sv (1%positive)), n)   (* {| ( Cconstr n ty var_tag ((nth (N.to_nat m) sv (1%positive))::nil)  Chole, Pos.succ n  ) |} *)
           | KVar_c m => (Chole, (nth (N.to_nat m) sk (1%positive)), n) (* {| ( Cconstr n ty kvar_tag ((nth (N.to_nat m) sk (1%positive))::nil) Chole, Pos.succ n) |} *)
           | Lam_c e => let (e', n') := convert e (n::sv) ((Pos.succ n)::sk) (Pos.add n (2%positive)) in
                        let fds := Fcons n' ty_fun (n::(Pos.succ n)::nil) e' Fnil in
                        (Cfun2 fds Chole, n' , (Pos.succ n'))
           | Cont_c e => let (e', n') := convert e sv (n::sk) (Pos.succ n) in
                         let fds := Fcons n' ty_con (n::nil) e' Fnil in
                         (Cfun2 fds Chole, n',  Pos.succ n')
           | Con_c dcn lv =>
             let (ll, n') := convert_v_list convert_v lv sv sk n in
             let (lv_ctx, nl) := ll in
             (comp_ctx_exp_f lv_ctx (Cconstr n' ty (dcon_to_tag dcn) nl Chole), n', Pos.succ n')
           | Fix_c le =>
             let (fn, n') := convert_fds convert le sv sk (Pos.succ n) n in
             let (fds, ln) := fn in
             (* the record should disappear during shrink reduction *) 
             (Cfun2 fds (Cconstr n ty rec_tag ln Chole), n,  n' )
           end.



(* 
{| Example e1 : simple_cps.exp := Lam_e (Var_e 0). |}
{| Example e2 : simple_cps.exp := Lam_e (Lam_e (Var_e 1)). |}
{| Eval vm_compute in cps_cvt_prog e1. |}
{| Eval vm_compute in convert_top (cps_cvt_prog e1). |}
*)

Definition convert_top (e:cps) : exp :=
  let (er, n) := convert e nil nil (3%positive) in er.

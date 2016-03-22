Require Import cps cps_util hoisting identifiers.
Require Import Znumtheory.
Require Import List MSets MSetRBT BinNums BinNat BinPos.
Require Import ExtLib.Structures.Monads ExtLib.Data.Monads.StateMonad.
Import ListNotations Nnat MonadNotation.
Require Maps.

Record FunInfo : Type :=
  mkFunInfo
    { (* free variable set of the fix definition *)
      fv_set_def : FVSet.t;
      (* the names of the functions that are mut. recursive *)
      rec_names  : FVSet.t }.
 
Definition FunInfoMap := Maps.PTree.t FunInfo.

Definition TypeMap := Maps.PTree.t type.

Inductive VarInfo : Type :=
| FVar : N -> type -> VarInfo
| MRFun : var -> type -> type -> VarInfo
| BoundVar : type -> VarInfo.
    
Definition VarInfoMap := Maps.PTree.t VarInfo.

Definition ccstate := state (var * TDict.t).

Definition get_name : ccstate var :=
  p <- get ;;
  let '(n, d) := p in
  put ((n+1)%positive, d) ;;
  ret n.

Definition set_typeinfo (t : typeinfo) : ccstate type :=
  p <- get ;;
  let '(n, d) := p in
  let (h, d') := TDict.hash t d in
  put (n, d') ;;
  ret h.

Definition get_typeinfo (i : type) : ccstate typeinfo :=
  p <- get ;;
  let '(n, d) := p in
  match TDict.get i d with
    | Some typinfo => ret typinfo
    | None => ret Tunknown (* should not happen *)
  end.

Fixpoint exp_info (e : exp) (acc : FunInfoMap) : FunInfoMap :=
  match e with
    | Econstr x tau c ys e =>
      exp_info e acc
    | Ecase x pats => acc
    | Eproj x tau n y e =>
      exp_info e acc
    | Efun defs e =>
      let names := fundefs_names defs in
      let acc' := fundefs_info defs (fundefs_fv defs names) names acc in
      exp_info e acc'
    | Eapp x xs => acc
    | Eprim x tau prim ys e =>
      exp_info e acc
  end
with fundefs_info (defs : fundefs) (fv : FVSet.t) (names : FVSet.t)
                  (acc : FunInfoMap) : FunInfoMap :=
       match defs with
         | Fcons f tau ys e defs' =>
           let acc' := Maps.PTree.set f
                                      {| fv_set_def := fv;
                                         rec_names := names |}
                                      acc in
           let acc'' := exp_info e acc' in
           fundefs_info defs' names fv acc'' 
         | Fnil => acc
       end.

Section CC.
  Context (map : FunInfoMap)
          (utag : tag) (* Tag for types with unique constructor *)
          (env_tag : tag) (* Tag for the type of environments *)
          (tag_bij : tag -> tag) (* mapping from function tags to closure 
                                 records tags *)
          (unknown_type : type).
  
  Definition get_var (x : var) (map : VarInfoMap) (f : exp -> exp) (env : var)
: ccstate (var * type * (exp -> exp)) :=
    match Maps.PTree.get x map with
      | Some entry =>
        match entry with
          | FVar pos typ =>
            y <- get_name ;;
            ret (y, typ, fun e => Eproj y typ pos env (f e))   
          | MRFun code_ptr typ cl_typ =>
            y <- get_name ;;
            ret (y, cl_typ, fun e => Econstr y cl_typ utag [code_ptr; env] (f e))
          | BoundVar typ => ret (x, typ, f)
        end
      | None => ret (x, 1%positive, f) (* should not happen *)
    end.
      
  Definition get_vars (xs : list var) (map : VarInfoMap) (f : exp -> exp)
             (cl : var) : ccstate (list var * (exp -> exp)) :=
    fold_right (fun x t =>
                  t1 <- t ;; 
                  let '(ys, f') := t1 in
                  t2 <- get_var x map f' cl ;;
                  let '(y, f'') := t2 in
                  ret (fst y :: ys, f'')
               ) (ret ([], f)) xs.

  Definition get_vars_with_types (xs : list var) (map : VarInfoMap)
             (f : exp -> exp) (cl : var)
  : ccstate (list (var * type) * (exp -> exp)) :=
    fold_right (fun x t =>
                  t1 <- t ;; 
                  let '(ys, f') := t1 in
                  t2 <- get_var x map f' cl ;;
                  let '(y, f'') := t2 in
                  ret (y :: ys, f'')
               ) (ret ([], f)) xs.

  (* not sure if needed *)
  Definition get_tvars (xs : list (tag * var)) (map : VarInfoMap)
             (f : exp -> exp) (cl : var)
  : ccstate (list (tag * var) * (exp -> exp)) :=
    fold_right (fun tx t =>
                  let '(tag, x) := tx in
                  t1 <- t ;;
                  let '(ys, f') := t1 in
                  t2 <- get_var x map f' cl ;;   
                  let '(y, f'') := t2  in
                  ret ((tag, fst y) :: ys, f'')
               ) (ret ([], f)) xs.

  Definition make_env (fv : FVSet.t) (mapfv_new : VarInfoMap)
             (mapfv_old : VarInfoMap) (env_new env_old : var) (g : exp -> exp)
  : ccstate (type * VarInfoMap * (exp -> exp)) :=
    t1 <- get_vars_with_types (FVSet.elements fv) mapfv_old g env_old ;;
    let '(vars, g') :=  t1 in
    let (map_new', _) :=
        FVSet.fold (fun x arg =>
                let '(map, n) := arg in
                let typ :=
                    match Maps.PTree.get x mapfv_old with
                      | Some entry  =>
                        match entry with
                          | FVar _ t | BoundVar t
                          | MRFun _ _ t => t
                        end
                      | None => 1%positive (* should not happen *)
                    end
                in
                (Maps.PTree.set x (FVar n typ) map, (n + 1)%N))
             fv (mapfv_new, 0%N)
    in
    env_typ <- set_typeinfo (Tdata [(env_tag, List.map snd vars)]) ;;
    ret (env_typ, map_new',
         fun e => g' (Econstr env_new env_typ utag (List.map fst vars) e)).

  Fixpoint mapM {M : Type -> Type} {A B : Type} `{Monad M} (f : A -> M B)
           (l : list A)  : M (list B) :=
    match l with
      | [] => ret []
      | x :: xs =>
        x' <- (f x) ;;
        xs' <- mapM f xs ;;
        ret (x' :: xs')
    end.

(* recursive lookup for types -- needs termination proof *)
(* Fixpoint closure_type (fun_typ env_type : type) : ccstate type := *)
(*   ftyp <- get_typeinfo fun_typ ;; *)
(*   match ftyp with *)
(*     | Tfun tag lst => *)
(*       lst' <- mapM (fun f => closure_type f env_type) lst ;; *)
(*       let ptr_inf := Tfun tag (env_type :: lst') in *)
(*       ptr_typ <- set_typeinfo ptr_inf ;;  *)
(*       let clo_inf := Tdata [(tag_bij tag, [ptr_typ; env_type])] in *)
(*       typ <- set_typeinfo clo_inf ;; *)
(*       ret typ *)
(*     | _ => ret fun_typ *)
(*   end. *)
  
  Fixpoint make_full_closure (defs : fundefs) (mapfv_new mapfv_old : VarInfoMap)
           (env : var) (env_type : type) (g : exp -> exp)
  : ccstate (VarInfoMap * VarInfoMap * (exp -> exp)) :=
    match defs with
      | Fcons f typ xs e defs' =>
        code_ptr <- get_name ;;
        tinf <- get_typeinfo typ ;;
        p <- match tinf with
               | Tfun tag args =>
                 (* The new type of the code pointer *)
                 (* XXX change args type *)
                 let tinf' := Tfun tag (env_type :: args) in
                 typ' <- set_typeinfo tinf' ;;
                 (* The type of the closure *)
                 let tinf'' := Tdata [(tag_bij tag, [typ'; unknown_type])] in
                 typ'' <- set_typeinfo tinf'' ;;
                  ret (typ', typ'') 
               | _ => ret (1%positive, 1%positive)
             end ;;
        let (typ', typ'') := p in (* (type of code ptr * type of closure) *)
        let mapfv_new' :=
            Maps.PTree.set f (MRFun code_ptr typ' typ'') mapfv_new
        in
        let mapfv_old' :=
            Maps.PTree.set f (BoundVar typ'') mapfv_old
        in
        t <- make_full_closure defs' mapfv_new' mapfv_old' env env_type g ;;
        let '(mapfv_new'', mapfv_old'', g') := t in
        let ptr := (* this is silly but it helps a proof *)
            match Maps.PTree.get f mapfv_new'' with
              | Some (MRFun ptr _ _) => ptr
              | _ => code_ptr
            end
        in
        ret (mapfv_new'', mapfv_old'',
             (fun e => Econstr f typ'' utag [ptr; env] (g' e)))
      | Fnil => ret (mapfv_new, mapfv_old, g)
    end.

  Definition add_params args args_typ mapfv :=
    fold_left (fun map p =>
                 let '(var, typ) := p in
                 Maps.PTree.set var (BoundVar typ) map)
              (combine args args_typ) mapfv.

  (* TODO : fix argument types bug *)
  Fixpoint exp_closure_conv (e : exp) (mapfv : VarInfoMap)
           (env : var) : ccstate exp := 
    match e with
      | Econstr x typ c ys e' =>
        t1 <- get_vars ys mapfv id env ;;
        let '(ys', f) := t1 in
        e'' <- exp_closure_conv e' (Maps.PTree.set x (BoundVar typ) mapfv) env ;;
        ret (f (Econstr x typ c ys' e''))
      | Ecase x xs =>
        t1 <- get_var x mapfv id env ;;
        let '(x', _, f1) := t1 in
        t2 <- get_tvars xs mapfv f1 env ;;
        let '(xs', f2) := t2 in
        ret (f2 (Ecase x' xs'))
      | Eproj x typ n y e' =>
        t1 <- get_var y mapfv id env ;;
        let '(y', _, f) := t1 in
        e'' <- exp_closure_conv e' (Maps.PTree.set x (BoundVar typ) mapfv) env ;;
        ret (f (Eproj x typ n y' e''))
      | Efun defs e =>
        let fv :=
            match defs with
              | Fcons f _ _ _ _ =>
                match Maps.PTree.get f map with
                  | Some entry => fv_set_def entry
                  | None => FVSet.empty
                end
              | Fnil => FVSet.empty
            end in
        env' <- get_name ;;
        t1 <- make_env fv (Maps.PTree.empty VarInfo) mapfv env' env id ;;
        let '(env_type, mapfv_new, g1) := t1 in
        t2 <- make_full_closure defs mapfv_new mapfv env' env_type id ;;
        let '(mapfv_new', mapfv_old', g2) := t2 in
        e' <- exp_closure_conv e mapfv_old' env ;;
        defs' <- fundefs_closure_conv defs mapfv_new' ;;
        ret (Efun defs' (g1 (g2 e')))
      | Eapp f xs =>
        t1 <- get_vars xs mapfv id env ;;
        let '(xs', g1) := t1 in
        t2 <- get_var f mapfv g1 env ;;
        let '(f', typ, g2) := t2 in     
        ptr <- get_name ;;
        env <- get_name ;;
        typinf <- get_typeinfo typ;;    
        let ftyp :=
            match typinf with
              | Tdata [(_, (ftyp :: _))] => ftyp
              | _ => 1%positive (* should not happen *) 
            end
        in
        ret (g2 (Eproj ptr ftyp 0 f'
                       (Eproj env unknown_type 1 f'
                              (Eapp ptr (env :: xs')))))
    | Eprim x typ prim ys e' =>
      t1 <- get_vars ys mapfv id env ;;
      let '(ys', f) := t1 in
      e'' <- exp_closure_conv e' (Maps.PTree.set x (BoundVar typ) mapfv) env ;;
      ret (f (Eprim x typ prim ys' e''))
    end
  with fundefs_closure_conv (defs : fundefs) (mapfv : VarInfoMap)
       : ccstate fundefs  :=
         match defs with
           | Fcons f typ ys e defs' =>
             typinf <- get_typeinfo typ ;;
             let args_typ :=
                 match typinf with
                   | Tfun _ typs => typs
                   | _ => []
                 end
             in
             let mapfv' := add_params ys args_typ mapfv in
             (* formal parameter for the environment pointer *)
             env <- get_name ;;
             e' <- exp_closure_conv e mapfv' env ;;
             defs'' <- fundefs_closure_conv defs' mapfv ;;
             let (code_ptr, typ') :=
                 match Maps.PTree.get f mapfv with
                   | Some entry =>
                     match entry with
                       | MRFun ptr typ _ => (ptr, typ)
                       | _ => (f, 1%positive) (* should not happen *)
                     end
                   | None => (f, 1%positive) (* should not happen *)
                 end
             in
             ret (Fcons code_ptr typ' (env::ys) e' defs'')
           | Fnil => ret Fnil
         end.

End CC.


Fixpoint max_list ls : positive :=
  let fix aux ls (n : positive) :=
      match ls with
        | nil => n
        | cons x xs => aux xs (Pos.max x n)
      end
  in
    aux ls 1%positive.

Fixpoint max_var e z :=
  match e with
  | Econstr x _ _ ys e => max_var e (max_list (z::x::ys)) 
  | Ecase x ys => max_list (z::x::(List.map fst ys))
  | Eproj x _ _ y e => max_var e (max_list (z::x::y::nil))
  | Efun defs e =>
    let z' := max_var_fundefs defs z in
    max_var e z'
  | Eapp f xs => max_list (z::f::xs)
  | Eprim x _ _ ys e => max_var e (max_list (z::x::ys))
  end
with max_var_fundefs defs z :=
       match defs with
         | Fcons f _ ys e defs =>
           let z' := max_var e z in
           max_var_fundefs defs (max_list (z::f::ys))
         | Fnil => z
       end.

(* types are bogus because they rely on parameters instantiated with dummies *)
Definition closure_conversion (e : exp) : exp :=
  let map := exp_info e (Maps.PTree.empty FunInfo) in
  let next :=
      let x := max_var e 1%positive in
      if Pos.leb x 3%positive then 3%positive else (x+1)%positive
  in
  let state := (next, TDict.empty) in
  exp_hoist (fst (runState
                    (exp_closure_conv map 1%positive 1%positive id 1%positive
                                      e (Maps.PTree.empty VarInfo) 1%positive)
                    state)) Fnil id.

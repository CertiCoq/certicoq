open BinNat
open Datatypes
open List0
open Maps
open Monad0
open StateMonad
open String0
open Cps
open Hoisting
open Identifiers
open Set_util
open State

let __ = let rec f _ = Obj.repr f in Obj.repr f

type coq_VarInfo =
| FVar of int
| MRFun of var
| BoundVar

type coq_VarInfoMap = coq_VarInfo M.t

type coq_GFunInfo = var
  (* singleton inductive, whose constructor was GFun *)

type coq_GFunMap = coq_GFunInfo M.t

type 't ccstate = (unit, 't) compM

(** val clo_env_suffix : char list **)

let clo_env_suffix =
  '_'::('e'::('n'::('v'::[])))

(** val clo_suffix : char list **)

let clo_suffix =
  '_'::('c'::('l'::('o'::[])))

(** val code_suffix : char list **)

let code_suffix =
  '_'::('c'::('o'::('d'::('e'::[]))))

(** val proj_suffix : char list **)

let proj_suffix =
  '_'::('p'::('r'::('o'::('j'::[]))))

(** val get_var :
    cTag -> var -> coq_VarInfoMap -> coq_GFunMap -> cTag -> var ->
    (var * (exp -> exp)) ccstate **)

let get_var clo_tag x map gfuns c _UU0393_ =
  match PTree.get x map with
  | Some entry ->
    (match entry with
     | FVar pos ->
       pbind (coq_PMonad_Monad (Obj.magic coq_Monad_state)) (Obj.magic __)
         (Obj.magic get_name x proj_suffix) (fun y ->
         ret (Obj.magic coq_Monad_state) (y, (fun e -> Eproj (y, c, pos,
           _UU0393_, e))))
     | MRFun code_ptr ->
       pbind (coq_PMonad_Monad (Obj.magic coq_Monad_state)) (Obj.magic __)
         (Obj.magic get_name x clo_suffix) (fun y ->
         ret (Obj.magic coq_Monad_state) (y, (fun e -> Econstr (y, clo_tag,
           (code_ptr :: (_UU0393_ :: [])), e))))
     | BoundVar -> ret (Obj.magic coq_Monad_state) (x, id))
  | None ->
    (match M.get x gfuns with
     | Some g ->
       pbind (coq_PMonad_Monad (Obj.magic coq_Monad_state)) (Obj.magic __)
         (Obj.magic make_record_cTag 0) (fun c_env ->
         pbind (coq_PMonad_Monad (Obj.magic coq_Monad_state)) (Obj.magic __)
           (Obj.magic get_name x
             ('b'::('o'::('g'::('u'::('s'::('_'::('e'::('n'::('v'::[]))))))))))
           (fun g_env ->
           pbind (coq_PMonad_Monad (Obj.magic coq_Monad_state))
             (Obj.magic __) (Obj.magic get_name x clo_suffix) (fun y ->
             ret (Obj.magic coq_Monad_state) (y, (fun e -> Econstr (g_env,
               c_env, [], (Econstr (y, clo_tag, (g :: (_UU0393_ :: [])),
               e))))))))
     | None -> ret (Obj.magic coq_Monad_state) (x, id))

(** val get_vars :
    cTag -> var list -> coq_VarInfoMap -> coq_GFunMap -> cTag -> var -> (var
    list * (exp -> exp)) ccstate **)

let rec get_vars clo_tag xs map gfuns c _UU0393_ =
  match xs with
  | [] -> ret (Obj.magic coq_Monad_state) ([], id)
  | x :: xs0 ->
    pbind (coq_PMonad_Monad (Obj.magic coq_Monad_state)) (Obj.magic __)
      (Obj.magic get_var clo_tag x map gfuns c _UU0393_) (fun t1 ->
      let (y, f) = t1 in
      pbind (coq_PMonad_Monad (Obj.magic coq_Monad_state)) (Obj.magic __)
        (get_vars clo_tag xs0 map gfuns c _UU0393_) (fun t2 ->
        let (ys, f') = t2 in
        ret (Obj.magic coq_Monad_state) ((y :: ys), (fun e -> f (f' e)))))

(** val add_params : int list -> coq_VarInfoMap -> coq_VarInfoMap **)

let rec add_params args mapfv =
  match args with
  | [] -> mapfv
  | x :: xs -> M.set x BoundVar (add_params xs mapfv)

(** val make_env :
    cTag -> var list -> coq_VarInfoMap -> coq_VarInfoMap -> cTag -> var ->
    var -> coq_GFunMap -> ((cTag * coq_VarInfoMap) * (exp -> exp)) ccstate **)

let make_env clo_tag fvs _ mapfv_old c_old _UU0393__new _UU0393__old gfuns =
  let (map_new', n) =
    let rec add_fvs l n map =
      match l with
      | [] -> (map, n)
      | x :: xs -> add_fvs xs (N.add n 1) (PTree.set x (FVar n) map)
    in add_fvs fvs 0 PTree.empty
  in
  pbind (coq_PMonad_Monad (Obj.magic coq_Monad_state)) (Obj.magic __)
    (Obj.magic get_vars clo_tag fvs mapfv_old gfuns c_old _UU0393__old)
    (fun t1 ->
    let (fv', g') = t1 in
    pbind (coq_PMonad_Monad (Obj.magic coq_Monad_state)) (Obj.magic __)
      (Obj.magic make_record_cTag n) (fun c_new ->
      ret (Obj.magic coq_Monad_state) ((c_new, map_new'), (fun e ->
        g' (Econstr (_UU0393__new, c_new, fv', e))))))

(** val make_full_closure :
    cTag -> fundefs -> coq_VarInfoMap -> coq_VarInfoMap -> coq_GFunMap -> var
    -> bool -> (((coq_VarInfoMap * coq_VarInfoMap) * coq_GFunMap) * (exp ->
    exp)) ccstate **)

let rec make_full_closure clo_tag defs mapfv_new mapfv_old gfuns _UU0393_ is_closed =
  match defs with
  | Fcons (f, _, _, _, defs') ->
    pbind (coq_PMonad_Monad (Obj.magic coq_Monad_state)) (Obj.magic __)
      (Obj.magic get_name f []) (fun code_ptr ->
      pbind (coq_PMonad_Monad (Obj.magic coq_Monad_state)) (Obj.magic __)
        (make_full_closure clo_tag defs' mapfv_new mapfv_old gfuns _UU0393_
          is_closed) (fun t0 ->
        let (p, g') = t0 in
        let (p0, gfuns') = p in
        let (mapfv_new', mapfv_old') = p0 in
        let mapfv_new'' = PTree.set f (MRFun code_ptr) mapfv_new' in
        let mapfv_old'' = PTree.set f BoundVar mapfv_old' in
        pbind (coq_PMonad_Monad (Obj.magic coq_Monad_state)) (Obj.magic __)
          (if is_closed
           then pbind (coq_PMonad_Monad (Obj.magic coq_Monad_state))
                  (Obj.magic __) (Obj.magic get_pp_name f) (fun f_str ->
                  pbind (coq_PMonad_Monad (Obj.magic coq_Monad_state))
                    (Obj.magic __)
                    (Obj.magic log_msg
                      (append
                        ('A'::('d'::('d'::('i'::('n'::('g'::(' '::[])))))))
                        f_str)) (fun _ ->
                    ret (Obj.magic coq_Monad_state) (M.set f code_ptr gfuns')))
           else ret (Obj.magic coq_Monad_state) gfuns') (fun gfuns'' ->
          ret (Obj.magic coq_Monad_state) (((mapfv_new'', mapfv_old''),
            gfuns''), (fun e -> Econstr (f, clo_tag,
            (code_ptr :: (_UU0393_ :: [])), (g' e)))))))
  | Fnil ->
    ret (Obj.magic coq_Monad_state) (((mapfv_new, mapfv_old), gfuns), id)

(** val bool_to_string : bool -> char list **)

let bool_to_string = function
| true -> 't'::('r'::('u'::('e'::[])))
| false -> 'f'::('a'::('l'::('s'::('e'::[]))))

(** val exp_closure_conv :
    cTag -> exp -> coq_VarInfoMap -> coq_GFunMap -> cTag -> var ->
    (exp * (exp -> exp)) ccstate **)

let exp_closure_conv clo_tag =
  let rec exp_closure_conv0 e mapfv gfuns c _UU0393_ =
    match e with
    | Econstr (x, tag, ys, e') ->
      pbind (coq_PMonad_Monad (Obj.magic coq_Monad_state)) (Obj.magic __)
        (Obj.magic get_vars clo_tag ys mapfv gfuns c _UU0393_) (fun t1 ->
        let (ys', f) = t1 in
        pbind (coq_PMonad_Monad (Obj.magic coq_Monad_state)) (Obj.magic __)
          (exp_closure_conv0 e' (PTree.set x BoundVar mapfv) gfuns c _UU0393_)
          (fun ef ->
          ret (Obj.magic coq_Monad_state) ((Econstr (x, tag, ys',
            (snd ef (fst ef)))), f)))
    | Ecase (x, pats) ->
      pbind (coq_PMonad_Monad (Obj.magic coq_Monad_state)) (Obj.magic __)
        (let rec mapM_cc = function
         | [] -> ret (Obj.magic coq_Monad_state) []
         | y0 :: xs ->
           let (y, e0) = y0 in
           pbind (coq_PMonad_Monad (Obj.magic coq_Monad_state))
             (Obj.magic __) (exp_closure_conv0 e0 mapfv gfuns c _UU0393_)
             (fun ef ->
             pbind (coq_PMonad_Monad (Obj.magic coq_Monad_state))
               (Obj.magic __) (mapM_cc xs) (fun xs' ->
               ret (Obj.magic coq_Monad_state) ((y, (snd ef (fst ef))) :: xs')))
         in mapM_cc pats) (fun pats' ->
        pbind (coq_PMonad_Monad (Obj.magic coq_Monad_state)) (Obj.magic __)
          (Obj.magic get_var clo_tag x mapfv gfuns c _UU0393_) (fun t1 ->
          let (x', f1) = t1 in
          ret (Obj.magic coq_Monad_state) ((Ecase (x', pats')), f1)))
    | Eproj (x, tag, n, y, e') ->
      pbind (coq_PMonad_Monad (Obj.magic coq_Monad_state)) (Obj.magic __)
        (Obj.magic get_var clo_tag y mapfv gfuns c _UU0393_) (fun t1 ->
        let (y', f) = t1 in
        pbind (coq_PMonad_Monad (Obj.magic coq_Monad_state)) (Obj.magic __)
          (exp_closure_conv0 e' (PTree.set x BoundVar mapfv) gfuns c _UU0393_)
          (fun ef ->
          ret (Obj.magic coq_Monad_state) ((Eproj (x, tag, n, y',
            (snd ef (fst ef)))), f)))
    | Efun (defs, e0) ->
      let fv = fundefs_fv defs in
      let fvs =
        filter (fun x ->
          match M.get x gfuns with
          | Some _ -> false
          | None -> true) (PS.elements fv)
      in
      pbind (coq_PMonad_Monad (Obj.magic coq_Monad_state)) (Obj.magic __)
        (Obj.magic get_name_no_suff ('e'::('n'::('v'::[]))))
        (fun _UU0393_' ->
        pbind (coq_PMonad_Monad (Obj.magic coq_Monad_state)) (Obj.magic __)
          (Obj.magic make_env clo_tag fvs PTree.empty mapfv c _UU0393_'
            _UU0393_ gfuns) (fun t1 ->
          let (p, g1) = t1 in
          let (c', mapfv_new) = p in
          let is_closed = match fvs with
                          | [] -> true
                          | _ :: _ -> false in
          pbind (coq_PMonad_Monad (Obj.magic coq_Monad_state)) (Obj.magic __)
            (Obj.magic get_pp_names_list fvs) (fun fv_names ->
            pbind (coq_PMonad_Monad (Obj.magic coq_Monad_state))
              (Obj.magic __)
              (Obj.magic log_msg
                (concat (' '::[])
                  (('C'::('l'::('o'::('s'::('e'::('d'::[])))))) :: ((bool_to_string
                                                                    is_closed) :: (('B'::('l'::('o'::('c'::('k'::(' '::('h'::('a'::('s'::(' '::('f'::('v'::('s'::(' '::(':'::[]))))))))))))))) :: fv_names)))))
              (fun _ ->
              pbind (coq_PMonad_Monad (Obj.magic coq_Monad_state))
                (Obj.magic __)
                (Obj.magic make_full_closure clo_tag defs mapfv_new mapfv
                  gfuns _UU0393_' is_closed) (fun t2 ->
                let (p0, g2) = t2 in
                let (p1, gfuns') = p0 in
                let (mapfv_new', mapfv_old') = p1 in
                pbind (coq_PMonad_Monad (Obj.magic coq_Monad_state))
                  (Obj.magic __)
                  (exp_closure_conv0 e0 mapfv_old' gfuns' c _UU0393_)
                  (fun ef ->
                  pbind (coq_PMonad_Monad (Obj.magic coq_Monad_state))
                    (Obj.magic __)
                    (fundefs_closure_conv defs mapfv_new' gfuns' c')
                    (fun defs' ->
                    ret (Obj.magic coq_Monad_state) ((Efun (defs',
                      (g2 (snd ef (fst ef))))), g1))))))))
    | Eapp (f, ft, xs) ->
      pbind (coq_PMonad_Monad (Obj.magic coq_Monad_state)) (Obj.magic __)
        (Obj.magic get_var clo_tag f mapfv gfuns c _UU0393_) (fun t1 ->
        let (f', g1) = t1 in
        pbind (coq_PMonad_Monad (Obj.magic coq_Monad_state)) (Obj.magic __)
          (Obj.magic get_vars clo_tag xs mapfv gfuns c _UU0393_) (fun t2 ->
          let (xs', g2) = t2 in
          pbind (coq_PMonad_Monad (Obj.magic coq_Monad_state)) (Obj.magic __)
            (Obj.magic get_name f code_suffix) (fun ptr ->
            pbind (coq_PMonad_Monad (Obj.magic coq_Monad_state))
              (Obj.magic __) (Obj.magic get_name f clo_env_suffix)
              (fun _UU0393_0 ->
              ret (Obj.magic coq_Monad_state) ((Eproj (ptr, clo_tag, 0, f',
                (Eproj (_UU0393_0, clo_tag, 1, f', (Eapp (ptr, ft,
                (_UU0393_0 :: xs'))))))), (fun e0 -> g1 (g2 e0)))))))
    | Eprim (x, prim, ys, e') ->
      pbind (coq_PMonad_Monad (Obj.magic coq_Monad_state)) (Obj.magic __)
        (Obj.magic get_vars clo_tag ys mapfv gfuns c _UU0393_) (fun t1 ->
        let (ys', f) = t1 in
        pbind (coq_PMonad_Monad (Obj.magic coq_Monad_state)) (Obj.magic __)
          (exp_closure_conv0 e' (PTree.set x BoundVar mapfv) gfuns c _UU0393_)
          (fun ef ->
          ret (Obj.magic coq_Monad_state) ((Eprim (x, prim, ys',
            (snd ef (fst ef)))), f)))
    | Ehalt x ->
      pbind (coq_PMonad_Monad (Obj.magic coq_Monad_state)) (Obj.magic __)
        (Obj.magic get_var clo_tag x mapfv gfuns c _UU0393_) (fun t1 ->
        let (x', f) = t1 in ret (Obj.magic coq_Monad_state) ((Ehalt x'), f))
  and fundefs_closure_conv defs mapfv gfuns c =
    match defs with
    | Fcons (f, tag, ys, e, defs') ->
      let mapfv' = add_params ys mapfv in
      pbind (coq_PMonad_Monad (Obj.magic coq_Monad_state)) (Obj.magic __)
        (Obj.magic get_name_no_suff ('e'::('n'::('v'::[])))) (fun _UU0393_ ->
        pbind (coq_PMonad_Monad (Obj.magic coq_Monad_state)) (Obj.magic __)
          (exp_closure_conv0 e mapfv' gfuns c _UU0393_) (fun ef ->
          pbind (coq_PMonad_Monad (Obj.magic coq_Monad_state)) (Obj.magic __)
            (fundefs_closure_conv defs' mapfv gfuns c) (fun defs'' ->
            let code_ptr =
              match PTree.get f mapfv with
              | Some entry -> (match entry with
                               | MRFun ptr -> ptr
                               | _ -> f)
              | None -> f
            in
            ret (Obj.magic coq_Monad_state) (Fcons (code_ptr, tag,
              (_UU0393_ :: ys), (snd ef (fst ef)), defs'')))))
    | Fnil -> ret (Obj.magic coq_Monad_state) Fnil
  in exp_closure_conv0

(** val closure_conversion_hoist :
    cTag -> iTag -> exp -> comp_data -> exp * comp_data **)

let closure_conversion_hoist clo_tag clo_itag e c =
  let (p, p0) =
    run_compM
      (pbind (coq_PMonad_Monad (Obj.magic coq_Monad_state)) (Obj.magic __)
        (Obj.magic get_name_no_suff
          ('d'::('u'::('m'::('m'::('y'::('_'::('e'::('n'::('v'::[]))))))))))
        (fun _UU0393_ ->
        pbind (coq_PMonad_Monad (Obj.magic coq_Monad_state)) (Obj.magic __)
          (Obj.magic register_record_cTag clo_tag clo_itag ((fun p->2*p) 1))
          (fun _ ->
          exp_closure_conv clo_tag e PTree.empty PTree.empty 1 _UU0393_))) c
      ()
  in
  let (e', f') = p in let (c', _) = p0 in ((exp_hoist (f' e')), c')

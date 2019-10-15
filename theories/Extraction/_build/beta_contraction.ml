open Datatypes
open List0
open Monad0
open StateMonad
open String0
open Alpha_fresh
open Cps
open Cps_show
open Shrink_cps
open State

let __ = let rec f _ = Obj.repr f in Obj.repr f

type 'st coq_InlineHeuristic = { update_funDef : (fundefs -> r_map -> 'st ->
                                                 'st * 'st);
                                 update_inFun : (var -> tag -> var list ->
                                                exp -> r_map -> 'st -> 'st);
                                 update_App : (var -> tag -> var list -> 'st
                                              -> 'st * bool) }

(** val update_funDef :
    'a1 coq_InlineHeuristic -> fundefs -> r_map -> 'a1 -> 'a1 * 'a1 **)

let update_funDef x = x.update_funDef

(** val update_inFun :
    'a1 coq_InlineHeuristic -> var -> tag -> var list -> exp -> r_map -> 'a1
    -> 'a1 **)

let update_inFun x = x.update_inFun

(** val update_App :
    'a1 coq_InlineHeuristic -> var -> tag -> var list -> 'a1 -> 'a1 * bool **)

let update_App x = x.update_App

type fun_map = ((tag * var list) * exp) M.t

(** val freshen_exp : exp -> exp freshM **)

let freshen_exp e =
  freshen_term e M.empty

(** val add_fundefs : fundefs -> fun_map -> fun_map **)

let rec add_fundefs fds fm =
  match fds with
  | Fcons (f, t0, xs, e, fds0) -> M.set f ((t0, xs), e) (add_fundefs fds0 fm)
  | Fnil -> fm

(** val debug_st : ('a1 -> nEnv -> char list) -> 'a1 -> unit freshM **)

let debug_st pp_St s =
  pbind (coq_PMonad_Monad (Obj.magic coq_Monad_state)) (Obj.magic __)
    (Obj.magic get_name_env ()) (fun nenv ->
    pbind (coq_PMonad_Monad (Obj.magic coq_Monad_state)) (Obj.magic __)
      (log_msg (pp_St s nenv)) (fun _ -> log_msg newline))

(** val beta_contract :
    ('a1 -> nEnv -> char list) -> 'a1 coq_InlineHeuristic -> nat -> exp ->
    M.elt M.t -> fun_map -> 'a1 -> exp freshM **)

let rec beta_contract pp_St iH d =
  let beta_contract_aux =
    let rec beta_contract_aux e sig0 fm s =
      match e with
      | Econstr (x, t0, ys, e0) ->
        let ys' = apply_r_list sig0 ys in
        pbind (coq_PMonad_Monad coq_Monad_state) (Obj.magic __)
          (beta_contract_aux e0 sig0 fm s) (fun e' ->
          ret coq_Monad_state (Econstr (x, t0, ys', e')))
      | Ecase (v, cl) ->
        let v' = apply_r sig0 v in
        pbind (coq_PMonad_Monad coq_Monad_state) (Obj.magic __)
          (let rec beta_list = function
           | [] -> ret coq_Monad_state []
           | p :: br' ->
             let (t0, e0) = p in
             pbind (coq_PMonad_Monad coq_Monad_state) (Obj.magic __)
               (beta_contract_aux e0 sig0 fm s) (fun e' ->
               pbind (coq_PMonad_Monad coq_Monad_state) (Obj.magic __)
                 (beta_list br') (fun br'' ->
                 ret coq_Monad_state ((t0, e') :: br'')))
           in beta_list cl) (fun cl' -> ret coq_Monad_state (Ecase (v', cl')))
      | Eproj (x, t0, n, y, e0) ->
        let y' = apply_r sig0 y in
        pbind (coq_PMonad_Monad coq_Monad_state) (Obj.magic __)
          (beta_contract_aux e0 sig0 fm s) (fun e' ->
          ret coq_Monad_state (Eproj (x, t0, n, y', e')))
      | Efun (fds, e0) ->
        let fm' = add_fundefs fds fm in
        let (s1, s2) = iH.update_funDef fds sig0 s in
        pbind (coq_PMonad_Monad coq_Monad_state) (Obj.magic __)
          (Obj.magic debug_st pp_St s1) (fun _ ->
          pbind (coq_PMonad_Monad coq_Monad_state) (Obj.magic __)
            (let rec beta_contract_fds fds0 s0 =
               match fds0 with
               | Fcons (f, t0, xs, e1, fds') ->
                 let s' = iH.update_inFun f t0 xs e1 sig0 s0 in
                 pbind (coq_PMonad_Monad coq_Monad_state) (Obj.magic __)
                   (beta_contract_aux e1 sig0 fm' s') (fun e' ->
                   pbind (coq_PMonad_Monad coq_Monad_state) (Obj.magic __)
                     (beta_contract_fds fds' s0) (fun fds'' ->
                     ret coq_Monad_state (Fcons (f, t0, xs, e', fds''))))
               | Fnil -> ret coq_Monad_state Fnil
             in beta_contract_fds fds s2) (fun fds' ->
            pbind (coq_PMonad_Monad coq_Monad_state) (Obj.magic __)
              (beta_contract_aux e0 sig0 fm' s1) (fun e' ->
              ret coq_Monad_state (Efun (fds', e')))))
      | Eapp (f, t0, ys) ->
        let f' = apply_r sig0 f in
        let ys' = apply_r_list sig0 ys in
        let (s', inl) = iH.update_App f' t0 ys' s in
        pbind (coq_PMonad_Monad coq_Monad_state) (Obj.magic __)
          (Obj.magic get_pp_name f') (fun fstr ->
          pbind (coq_PMonad_Monad coq_Monad_state) (Obj.magic __)
            (Obj.magic log_msg
              (append
                ('A'::('p'::('p'::('l'::('i'::('c'::('a'::('t'::('i'::('o'::('n'::(' '::('o'::('f'::(' '::[])))))))))))))))
                (append fstr
                  (append (' '::('i'::('s'::(' '::[]))))
                    (if inl
                     then []
                     else append ('n'::('o'::('t'::(' '::[]))))
                            ('i'::('n'::('l'::('i'::('n'::('e'::('d'::[]))))))))))))
            (fun _ ->
            let p = (inl, (M.get f' fm)) in
            let (b, o) = p in
            if b
            then (match o with
                  | Some p0 ->
                    let (p1, e0) = p0 in
                    let (_, xs) = p1 in
                    (match d with
                     | O -> ret coq_Monad_state (Eapp (f', t0, ys'))
                     | S d' ->
                       let sig' = set_list (combine xs ys') sig0 in
                       pbind (coq_PMonad_Monad coq_Monad_state)
                         (Obj.magic __) (Obj.magic freshen_exp e0) (fun e' ->
                         Obj.magic beta_contract pp_St iH d' e' sig' fm s'))
                  | None -> ret coq_Monad_state (Eapp (f', t0, ys')))
            else ret coq_Monad_state (Eapp (f', t0, ys'))))
      | Eprim (x, t0, ys, e0) ->
        let ys' = apply_r_list sig0 ys in
        pbind (coq_PMonad_Monad coq_Monad_state) (Obj.magic __)
          (beta_contract_aux e0 sig0 fm s) (fun e' ->
          ret coq_Monad_state (Eprim (x, t0, ys', e')))
      | Ehalt x -> let x' = apply_r sig0 x in ret coq_Monad_state (Ehalt x')
    in beta_contract_aux
  in
  Obj.magic beta_contract_aux

(** val beta_contract_top :
    ('a1 -> nEnv -> char list) -> 'a1 coq_InlineHeuristic -> exp -> nat ->
    'a1 -> comp_data -> exp * comp_data **)

let beta_contract_top pp_St iH e d s c =
  let (e', p) = run_compM (beta_contract pp_St iH d e M.empty M.empty s) c ()
  in
  let (st', _) = p in (e', st')

(** val show_map : 'a1 M.t -> nEnv -> ('a1 -> char list) -> char list **)

let show_map m nenv str =
  let show_lst =
    let rec show_lst = function
    | [] -> []
    | p :: lst0 ->
      let (x, a) = p in
      append (show_tree (show_var nenv x))
        (append (' '::('-'::('>'::(' '::[]))))
          (append (str a) (append (';'::(' '::[])) (show_lst lst0))))
    in show_lst
  in
  append ('S'::('{'::[])) (append (show_lst (M.elements m)) ('}'::[]))

(** val show_map_bool : bool M.t -> nEnv -> char list **)

let show_map_bool m nenv =
  show_map m nenv (fun b ->
    if b
    then 't'::('r'::('u'::('e'::[])))
    else 'f'::('a'::('l'::('s'::('e'::[])))))

(** val find_uncurried : fundefs -> bool M.t -> bool M.t **)

let rec find_uncurried fds s =
  match fds with
  | Fcons (f, _, l, e, fds') ->
    (match l with
     | [] -> s
     | _ :: _ ->
       (match e with
        | Efun (f0, e0) ->
          (match f0 with
           | Fcons (_, _, _, _, f1) ->
             (match f1 with
              | Fcons (_, _, _, _, _) -> s
              | Fnil ->
                (match e0 with
                 | Eapp (_, _, l0) ->
                   (match l0 with
                    | [] -> s
                    | _ :: l1 ->
                      (match l1 with
                       | [] ->
                         let s' = M.set f true s in find_uncurried fds' s'
                       | _ :: _ -> s))
                 | _ -> s))
           | Fnil -> s)
        | _ -> s))
  | Fnil -> s

(** val coq_InineUncurried : bool M.t coq_InlineHeuristic **)

let coq_InineUncurried =
  { update_funDef = (fun fds _ s ->
    let s' = find_uncurried fds s in (s', s')); update_inFun =
    (fun f _ _ _ _ s -> M.remove f s); update_App = (fun f _ _ s ->
    match M.get f s with
    | Some b -> (s, b)
    | None -> (s, false)) }

(** val inline_uncurry :
    exp -> nat M.t -> nat -> nat -> comp_data -> exp * comp_data **)

let inline_uncurry e _ _ d =
  beta_contract_top show_map_bool coq_InineUncurried e d M.empty

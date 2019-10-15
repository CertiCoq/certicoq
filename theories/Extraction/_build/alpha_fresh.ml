open Monad0
open StateMonad
open Cps
open Shrink_cps
open State

let __ = let rec f _ = Obj.repr f in Obj.repr f

type 'x freshM = (unit, 'x) compM

(** val freshen_term : exp -> int M.t -> exp freshM **)

let rec freshen_term e sigma =
  match e with
  | Econstr (x, t0, ys, e0) ->
    pbind (coq_PMonad_Monad (Obj.magic coq_Monad_state)) (Obj.magic __)
      (Obj.magic get_name x []) (fun x' ->
      let ys' = apply_r_list sigma ys in
      pbind (coq_PMonad_Monad (Obj.magic coq_Monad_state)) (Obj.magic __)
        (freshen_term e0 (M.set x x' sigma)) (fun e' ->
        ret (Obj.magic coq_Monad_state) (Econstr (x', t0, ys', e'))))
  | Ecase (v, cl) ->
    pbind (coq_PMonad_Monad (Obj.magic coq_Monad_state)) (Obj.magic __)
      (let rec alpha_list = function
       | [] -> ret (Obj.magic coq_Monad_state) []
       | pat :: pats0 ->
         let (t0, e0) = pat in
         pbind (coq_PMonad_Monad (Obj.magic coq_Monad_state)) (Obj.magic __)
           (freshen_term e0 sigma) (fun e' ->
           pbind (coq_PMonad_Monad (Obj.magic coq_Monad_state))
             (Obj.magic __) (alpha_list pats0) (fun pats' ->
             ret (Obj.magic coq_Monad_state) ((t0, e') :: pats')))
       in alpha_list cl) (fun cl' ->
      ret (Obj.magic coq_Monad_state) (Ecase ((apply_r sigma v), cl')))
  | Eproj (x, t0, n, y, e0) ->
    pbind (coq_PMonad_Monad (Obj.magic coq_Monad_state)) (Obj.magic __)
      (Obj.magic get_name x []) (fun x' ->
      let y' = apply_r sigma y in
      pbind (coq_PMonad_Monad (Obj.magic coq_Monad_state)) (Obj.magic __)
        (freshen_term e0 (M.set x x' sigma)) (fun e' ->
        ret (Obj.magic coq_Monad_state) (Eproj (x', t0, n, y', e'))))
  | Efun (fds, e0) ->
    let f_names = all_fun_name fds in
    pbind (coq_PMonad_Monad (Obj.magic coq_Monad_state)) (Obj.magic __)
      (Obj.magic get_names_lst f_names []) (fun f_names' ->
      match setlist f_names f_names' sigma with
      | Some sigma' ->
        pbind (coq_PMonad_Monad (Obj.magic coq_Monad_state)) (Obj.magic __)
          (Obj.magic freshen_fun fds sigma') (fun fds' ->
          pbind (coq_PMonad_Monad (Obj.magic coq_Monad_state)) (Obj.magic __)
            (freshen_term e0 sigma') (fun e' ->
            ret (Obj.magic coq_Monad_state) (Efun (fds', e'))))
      | None -> ret (Obj.magic coq_Monad_state) (Efun (Fnil, e0)))
  | Eapp (f, t0, ys) ->
    let f' = apply_r sigma f in
    let ys' = apply_r_list sigma ys in
    ret (Obj.magic coq_Monad_state) (Eapp (f', t0, ys'))
  | Eprim (x, t0, ys, e0) ->
    pbind (coq_PMonad_Monad (Obj.magic coq_Monad_state)) (Obj.magic __)
      (Obj.magic get_name x []) (fun x' ->
      let ys' = apply_r_list sigma ys in
      pbind (coq_PMonad_Monad (Obj.magic coq_Monad_state)) (Obj.magic __)
        (freshen_term e0 (M.set x x' sigma)) (fun e' ->
        ret (Obj.magic coq_Monad_state) (Eprim (x', t0, ys', e'))))
  | Ehalt x ->
    let x' = apply_r sigma x in ret (Obj.magic coq_Monad_state) (Ehalt x')

(** val freshen_fun : fundefs -> int M.t -> fundefs freshM **)

and freshen_fun fds sigma =
  match fds with
  | Fcons (f, t0, xs, e, fds0) ->
    let f' = apply_r sigma f in
    pbind (coq_PMonad_Monad (Obj.magic coq_Monad_state)) (Obj.magic __)
      (Obj.magic get_names_lst xs []) (fun xs' ->
      match setlist xs xs' sigma with
      | Some sigma' ->
        pbind (coq_PMonad_Monad (Obj.magic coq_Monad_state)) (Obj.magic __)
          (Obj.magic freshen_term e sigma') (fun e' ->
          pbind (coq_PMonad_Monad (Obj.magic coq_Monad_state)) (Obj.magic __)
            (freshen_fun fds0 sigma) (fun fds' ->
            ret (Obj.magic coq_Monad_state) (Fcons (f', t0, xs', e', fds'))))
      | None -> ret (Obj.magic coq_Monad_state) Fnil)
  | Fnil -> ret (Obj.magic coq_Monad_state) Fnil

open BinNat
open BinPos
open Datatypes
open Monad0
open Nat0
open StateMonad
open Cps
open State

let __ = let rec f _ = Obj.repr f in Obj.repr f

(** val eq_var : int -> int -> bool **)

let eq_var =
  Pos.eqb

(** val occurs_in_vars : var -> var list -> bool **)

let rec occurs_in_vars k = function
| [] -> false
| x :: xs1 -> (||) (eq_var k x) (occurs_in_vars k xs1)

(** val occurs_in_exp : var -> exp -> bool **)

let rec occurs_in_exp k = function
| Econstr (z, _, xs, e1) ->
  (||) ((||) (eq_var z k) (occurs_in_vars k xs)) (occurs_in_exp k e1)
| Ecase (x, arms) ->
  (||) (eq_var k x)
    (let rec occurs_in_arms = function
     | [] -> false
     | p :: arms1 ->
       let (_, e0) = p in (||) (occurs_in_exp k e0) (occurs_in_arms arms1)
     in occurs_in_arms arms)
| Eproj (z, _, _, x, e1) ->
  (||) ((||) (eq_var z k) (eq_var k x)) (occurs_in_exp k e1)
| Efun (fds, e0) -> (||) (occurs_in_fundefs k fds) (occurs_in_exp k e0)
| Eapp (x, _, xs) -> (||) (eq_var k x) (occurs_in_vars k xs)
| Eprim (z, _, xs, e1) ->
  (||) ((||) (eq_var z k) (occurs_in_vars k xs)) (occurs_in_exp k e1)
| Ehalt x -> eq_var x k

(** val occurs_in_fundefs : var -> fundefs -> bool **)

and occurs_in_fundefs k = function
| Fcons (z, _, zs, e, fds1) ->
  (||) ((||) ((||) (eq_var z k) (occurs_in_vars k zs)) (occurs_in_exp k e))
    (occurs_in_fundefs k fds1)
| Fnil -> false

type coq_St = nat * nat M.t

type arityMap = fTag M.t

type localMap = bool M.t

type stateType = ((bool * arityMap) * localMap) * coq_St

type 't uncurryM = (stateType, 't) compM

(** val markToInline : nat -> var -> var -> unit uncurryM **)

let markToInline n f k =
  pbind (coq_PMonad_Monad (Obj.magic coq_Monad_state)) (Obj.magic __)
    (Obj.magic get_state ()) (fun st ->
    let (y, s) = st in
    let (y0, lm) = y in
    let (b, aenv) = y0 in
    put_state (((b, aenv), lm), ((max (fst s) n),
      (M.set f (S O) (M.set k (S (S O)) (snd s))))))

(** val mark_as_uncurried : var -> unit uncurryM **)

let mark_as_uncurried x =
  pbind (coq_PMonad_Monad (Obj.magic coq_Monad_state)) (Obj.magic __)
    (Obj.magic get_state ()) (fun st ->
    let (y, s) = st in
    let (y0, lm) = y in
    let (b, aenv) = y0 in put_state (((b, aenv), (M.set x true lm)), s))

(** val click : unit uncurryM **)

let click =
  pbind (coq_PMonad_Monad (Obj.magic coq_Monad_state)) (Obj.magic __)
    (Obj.magic get_state ()) (fun st ->
    let (y, s) = st in
    let (y0, lm) = y in
    let (_, aenv) = y0 in put_state (((true, aenv), lm), s))

(** val has_clicked : bool uncurryM **)

let has_clicked =
  pbind (coq_PMonad_Monad (Obj.magic coq_Monad_state)) (Obj.magic __)
    (Obj.magic get_state ()) (fun st ->
    let (y, _) = st in
    let (y0, _) = y in let (b, _) = y0 in ret (Obj.magic coq_Monad_state) b)

(** val already_uncurried : var -> bool uncurryM **)

let already_uncurried f =
  pbind (coq_PMonad_Monad (Obj.magic coq_Monad_state)) (Obj.magic __)
    (Obj.magic get_state ()) (fun st ->
    let (y, _) = st in
    let (_, lm) = y in
    (match M.get f lm with
     | Some y0 -> ret (Obj.magic coq_Monad_state) y0
     | None -> ret (Obj.magic coq_Monad_state) false))

(** val get_fTag : int -> fTag uncurryM **)

let get_fTag n =
  pbind (coq_PMonad_Monad (Obj.magic coq_Monad_state)) (Obj.magic __)
    (Obj.magic get_state ()) (fun st ->
    let (y, s) = st in
    let (y0, lm) = y in
    let (b, aenv) = y0 in
    let p3 = N.succ_pos n in
    (match M.get p3 aenv with
     | Some t3 -> ret (Obj.magic coq_Monad_state) t3
     | None ->
       pbind (coq_PMonad_Monad (Obj.magic coq_Monad_state)) (Obj.magic __)
         (get_ftag n) (fun ft ->
         pbind (coq_PMonad_Monad (Obj.magic coq_Monad_state)) (Obj.magic __)
           (Obj.magic put_state (((b, (M.set p3 ft aenv)), lm), s)) (fun _ ->
           ret (Obj.magic coq_Monad_state) ft))))

(** val uncurry_exp : exp -> exp uncurryM **)

let rec uncurry_exp = function
| Econstr (x, ct, vs, e1) ->
  pbind (coq_PMonad_Monad (Obj.magic coq_Monad_state)) (Obj.magic __)
    (uncurry_exp e1) (fun e1' ->
    ret (Obj.magic coq_Monad_state) (Econstr (x, ct, vs, e1')))
| Ecase (x, arms) ->
  pbind (coq_PMonad_Monad (Obj.magic coq_Monad_state)) (Obj.magic __)
    (let rec uncurry_list = function
     | [] -> ret (Obj.magic coq_Monad_state) []
     | h :: t0 ->
       let (s, e0) = h in
       pbind (coq_PMonad_Monad (Obj.magic coq_Monad_state)) (Obj.magic __)
         (uncurry_exp e0) (fun e' ->
         pbind (coq_PMonad_Monad (Obj.magic coq_Monad_state)) (Obj.magic __)
           (uncurry_list t0) (fun t' ->
           ret (Obj.magic coq_Monad_state) ((s, e') :: t')))
     in uncurry_list arms) (fun arms' ->
    ret (Obj.magic coq_Monad_state) (Ecase (x, arms')))
| Eproj (x, ct, n, y, e1) ->
  pbind (coq_PMonad_Monad (Obj.magic coq_Monad_state)) (Obj.magic __)
    (uncurry_exp e1) (fun e1' ->
    ret (Obj.magic coq_Monad_state) (Eproj (x, ct, n, y, e1')))
| Efun (fds, e1) ->
  pbind (coq_PMonad_Monad (Obj.magic coq_Monad_state)) (Obj.magic __)
    (Obj.magic uncurry_fundefs fds) (fun fds' ->
    pbind (coq_PMonad_Monad (Obj.magic coq_Monad_state)) (Obj.magic __)
      (uncurry_exp e1) (fun e1' ->
      ret (Obj.magic coq_Monad_state) (Efun (fds', e1'))))
| Eprim (x, p, xs, e1) ->
  pbind (coq_PMonad_Monad (Obj.magic coq_Monad_state)) (Obj.magic __)
    (uncurry_exp e1) (fun e1' ->
    ret (Obj.magic coq_Monad_state) (Eprim (x, p, xs, e1')))
| x -> ret (Obj.magic coq_Monad_state) x

(** val uncurry_fundefs : fundefs -> fundefs uncurryM **)

and uncurry_fundefs = function
| Fcons (f, f_ft, fvs, fe, fds1) ->
  pbind (coq_PMonad_Monad (Obj.magic coq_Monad_state)) (Obj.magic __)
    (uncurry_fundefs fds1) (fun fds1' ->
    match fvs with
    | [] ->
      pbind (coq_PMonad_Monad (Obj.magic coq_Monad_state)) (Obj.magic __)
        (Obj.magic uncurry_exp fe) (fun fe' ->
        ret (Obj.magic coq_Monad_state) (Fcons (f, f_ft, fvs, fe', fds1')))
    | fk :: fvs0 ->
      (match fe with
       | Efun (f0, e) ->
         (match f0 with
          | Fcons (g, gt, gvs, ge, f1) ->
            (match f1 with
             | Fcons (_, _, _, _, _) ->
               pbind (coq_PMonad_Monad (Obj.magic coq_Monad_state))
                 (Obj.magic __) (Obj.magic uncurry_exp fe) (fun fe' ->
                 ret (Obj.magic coq_Monad_state) (Fcons (f, f_ft, fvs, fe',
                   fds1')))
             | Fnil ->
               (match e with
                | Eapp (fk', fk_ft, l) ->
                  (match l with
                   | [] ->
                     pbind (coq_PMonad_Monad (Obj.magic coq_Monad_state))
                       (Obj.magic __) (Obj.magic uncurry_exp fe) (fun fe' ->
                       ret (Obj.magic coq_Monad_state) (Fcons (f, f_ft, fvs,
                         fe', fds1')))
                   | g' :: l0 ->
                     (match l0 with
                      | [] ->
                        pbind (coq_PMonad_Monad (Obj.magic coq_Monad_state))
                          (Obj.magic __) (Obj.magic already_uncurried g)
                          (fun g_unc ->
                          if (&&)
                               ((&&)
                                 ((&&) ((&&) (eq_var fk fk') (eq_var g g'))
                                   (negb (occurs_in_exp g ge)))
                                 (negb (occurs_in_exp fk ge))) (negb g_unc)
                          then pbind
                                 (coq_PMonad_Monad
                                   (Obj.magic coq_Monad_state))
                                 (Obj.magic __)
                                 (Obj.magic get_names_lst gvs [])
                                 (fun gvs' ->
                                 pbind
                                   (coq_PMonad_Monad
                                     (Obj.magic coq_Monad_state))
                                   (Obj.magic __)
                                   (Obj.magic get_names_lst fvs0 [])
                                   (fun fvs' ->
                                   pbind
                                     (coq_PMonad_Monad
                                       (Obj.magic coq_Monad_state))
                                     (Obj.magic __)
                                     (Obj.magic get_name f
                                       ('_'::('u'::('n'::('c'::('u'::('r'::('r'::('i'::('e'::('d'::[])))))))))))
                                     (fun f' ->
                                     pbind
                                       (coq_PMonad_Monad
                                         (Obj.magic coq_Monad_state))
                                       (Obj.magic __)
                                       (Obj.magic mark_as_uncurried g)
                                       (fun _ ->
                                       pbind
                                         (coq_PMonad_Monad
                                           (Obj.magic coq_Monad_state))
                                         (Obj.magic __) (Obj.magic click)
                                         (fun _ ->
                                         let fp_numargs =
                                           length (app gvs' fvs')
                                         in
                                         pbind
                                           (coq_PMonad_Monad
                                             (Obj.magic coq_Monad_state))
                                           (Obj.magic __)
                                           (Obj.magic markToInline fp_numargs
                                             f g) (fun _ ->
                                           pbind
                                             (coq_PMonad_Monad
                                               (Obj.magic coq_Monad_state))
                                             (Obj.magic __)
                                             (Obj.magic get_fTag
                                               (N.of_nat fp_numargs))
                                             (fun fp_ft ->
                                             ret (Obj.magic coq_Monad_state)
                                               (Fcons (f, f_ft, (fk :: fvs'),
                                               (Efun ((Fcons (g, gt, gvs',
                                               (Eapp (f', fp_ft,
                                               (app gvs' fvs'))), Fnil)),
                                               (Eapp (fk, fk_ft,
                                               (g :: []))))), (Fcons (f',
                                               fp_ft, (app gvs fvs0), ge,
                                               fds1')))))))))))
                          else pbind
                                 (coq_PMonad_Monad
                                   (Obj.magic coq_Monad_state))
                                 (Obj.magic __) (Obj.magic uncurry_exp ge)
                                 (fun ge' ->
                                 ret (Obj.magic coq_Monad_state) (Fcons (f,
                                   f_ft, (fk :: fvs0), (Efun ((Fcons (g, gt,
                                   gvs, ge', Fnil)), (Eapp (fk', fk_ft,
                                   (g' :: []))))), fds1'))))
                      | _ :: _ ->
                        pbind (coq_PMonad_Monad (Obj.magic coq_Monad_state))
                          (Obj.magic __) (Obj.magic uncurry_exp fe)
                          (fun fe' ->
                          ret (Obj.magic coq_Monad_state) (Fcons (f, f_ft,
                            fvs, fe', fds1')))))
                | _ ->
                  pbind (coq_PMonad_Monad (Obj.magic coq_Monad_state))
                    (Obj.magic __) (Obj.magic uncurry_exp fe) (fun fe' ->
                    ret (Obj.magic coq_Monad_state) (Fcons (f, f_ft, fvs,
                      fe', fds1')))))
          | Fnil ->
            pbind (coq_PMonad_Monad (Obj.magic coq_Monad_state))
              (Obj.magic __) (Obj.magic uncurry_exp fe) (fun fe' ->
              ret (Obj.magic coq_Monad_state) (Fcons (f, f_ft, fvs, fe',
                fds1'))))
       | _ ->
         pbind (coq_PMonad_Monad (Obj.magic coq_Monad_state)) (Obj.magic __)
           (Obj.magic uncurry_exp fe) (fun fe' ->
           ret (Obj.magic coq_Monad_state) (Fcons (f, f_ft, fvs, fe', fds1')))))
| Fnil -> ret (Obj.magic coq_Monad_state) Fnil

(** val uncurry : exp -> exp option uncurryM **)

let uncurry e =
  pbind (coq_PMonad_Monad (Obj.magic coq_Monad_state)) (Obj.magic __)
    (Obj.magic uncurry_exp e) (fun e' ->
    pbind (coq_PMonad_Monad (Obj.magic coq_Monad_state)) (Obj.magic __)
      (Obj.magic has_clicked) (fun b ->
      if b
      then ret (Obj.magic coq_Monad_state) (Some e')
      else ret (Obj.magic coq_Monad_state) None))

(** val uncurry_fuel' : nat -> exp -> exp uncurryM **)

let rec uncurry_fuel' n e =
  match n with
  | O -> ret (Obj.magic coq_Monad_state) e
  | S m ->
    pbind (coq_PMonad_Monad (Obj.magic coq_Monad_state)) (Obj.magic __)
      (Obj.magic uncurry e) (fun eo ->
      match eo with
      | Some e' -> uncurry_fuel' m e'
      | None -> ret (Obj.magic coq_Monad_state) e)

(** val uncurry_fuel :
    nat -> exp -> comp_data -> (exp * nat M.t) * comp_data **)

let uncurry_fuel n e c =
  let local_st = (((false, M.empty), M.empty), (O, M.empty)) in
  let (e0, p) = run_compM (uncurry_fuel' n e) c local_st in
  let (c0, s) = p in let (_, s0) = s in let (_, st) = s0 in ((e0, st), c0)

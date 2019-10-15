open BinPos
open Datatypes
open List0
open List_util
open Nat0
open Specif
open Cps

type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

(** val var_dec : int -> int -> bool **)

let var_dec =
  M.elt_eq

type svalue =
| SVconstr of cTag * var list
| SVfun of fTag * var list * exp

type ctx_map = svalue M.t

type r_map = var M.t

type c_map = nat M.t

type b_map = bool M.t

(** val getd : 'a1 -> int -> 'a1 M.t -> 'a1 **)

let getd d v sub0 =
  match M.get v sub0 with
  | Some e -> e
  | None -> d

(** val set_list : (M.elt * 'a1) list -> 'a1 M.t -> 'a1 M.t **)

let set_list l map0 =
  fold_right (fun xv cmap -> M.set (fst xv) (snd xv) cmap) map0 l

(** val apply_r : M.elt M.t -> int -> M.elt **)

let apply_r sigma y =
  match M.get y sigma with
  | Some v -> v
  | None -> y

(** val apply_r_list : M.elt M.t -> int list -> M.elt list **)

let apply_r_list sigma ys =
  map (apply_r sigma) ys

type tag = int

(** val all_fun_name : fundefs -> var list **)

let rec all_fun_name = function
| Fcons (f, _, _, _, fds') -> f :: (all_fun_name fds')
| Fnil -> []

(** val update_census_list :
    r_map -> var list -> (var -> c_map -> nat) -> c_map -> c_map **)

let rec update_census_list sig0 ys fun_delta count =
  match ys with
  | [] -> count
  | y :: ys' ->
    let y' = apply_r sig0 y in
    update_census_list sig0 ys' fun_delta
      (M.set y' (fun_delta y' count) count)

(** val update_census :
    r_map -> exp -> (var -> c_map -> nat) -> c_map -> c_map **)

let rec update_census sig0 e fun_delta count =
  match e with
  | Econstr (_, _, ys, e0) ->
    let count' = update_census_list sig0 ys fun_delta count in
    update_census sig0 e0 fun_delta count'
  | Ecase (v, cl) ->
    let count' = update_census_list sig0 (v :: []) fun_delta count in
    fold_right (fun p c ->
      let (_, e0) = p in update_census sig0 e0 fun_delta c) count' cl
  | Eproj (_, _, _, y, e0) ->
    let count' = update_census_list sig0 (y :: []) fun_delta count in
    update_census sig0 e0 fun_delta count'
  | Efun (fl, e0) ->
    let count' = update_census_f sig0 fl fun_delta count in
    update_census sig0 e0 fun_delta count'
  | Eapp (f, _, ys) -> update_census_list sig0 (f :: ys) fun_delta count
  | Eprim (_, _, ys, e0) ->
    let count' = update_census_list sig0 ys fun_delta count in
    update_census sig0 e0 fun_delta count'
  | Ehalt v -> update_census_list sig0 (v :: []) fun_delta count

(** val update_census_f :
    r_map -> fundefs -> (var -> c_map -> nat) -> c_map -> c_map **)

and update_census_f sig0 fds fun_delta count =
  match fds with
  | Fcons (_, _, _, e, fds') ->
    let count' = update_census sig0 e fun_delta count in
    update_census_f sig0 fds' fun_delta count'
  | Fnil -> count

(** val init_census : exp -> c_map **)

let init_census e =
  update_census M.empty e (fun v c -> add (getd O v c) (S O)) M.empty

(** val dec_census : r_map -> exp -> c_map -> c_map **)

let dec_census sig0 e count =
  update_census sig0 e (fun v c -> sub (getd O v c) (S O)) count

(** val dec_census_list : r_map -> var list -> c_map -> c_map **)

let dec_census_list sig0 ys count =
  update_census_list sig0 ys (fun v c -> sub (getd O v c) (S O)) count

(** val dec_census_all_case : r_map -> (var * exp) list -> c_map -> c_map **)

let rec dec_census_all_case sig0 cl count =
  match cl with
  | [] -> count
  | p :: cl' ->
    let (_, e) = p in
    let count' = dec_census_all_case sig0 cl' count in
    dec_census sig0 e count'

(** val dec_census_case :
    r_map -> (var * exp) list -> var -> c_map -> c_map **)

let rec dec_census_case sig0 cl y count =
  match cl with
  | [] -> count
  | p :: cl' ->
    let (k, e) = p in
    if var_dec k y
    then dec_census_all_case sig0 cl' count
    else let count' = dec_census_case sig0 cl' y count in
         dec_census sig0 e count'

(** val update_count_inlined : var list -> var list -> c_map -> c_map **)

let rec update_count_inlined ys xs count =
  match ys with
  | [] -> count
  | y :: ys' ->
    (match xs with
     | [] -> count
     | x :: xs' ->
       let cy = getd O y count in
       let cx = getd O x count in
       update_count_inlined ys' xs'
         (M.set y (sub (add cy cx) (S O)) (M.set x O count)))

(** val precontractfun :
    r_map -> c_map -> ctx_map -> fundefs -> (fundefs * c_map) * ctx_map **)

let rec precontractfun sig0 count sub0 = function
| Fcons (f, t0, ys, e, fds') ->
  (match getd O f count with
   | O ->
     let count' = dec_census sig0 e count in
     precontractfun sig0 count' sub0 fds'
   | S _ ->
     let (fc', sub') = precontractfun sig0 count sub0 fds' in
     let (fds'', count') = fc' in
     (((Fcons (f, t0, ys, e, fds'')), count'),
     (M.set f (SVfun (t0, ys, e)) sub')))
| Fnil -> ((Fnil, count), sub0)

(** val contractcases :
    ((exp * ctx_map) * b_map) -> (r_map -> c_map -> ((exp * ctx_map) * b_map)
    -> __ -> ((exp * c_map) * b_map, __) sigT) -> r_map -> c_map -> b_map ->
    ctx_map -> (var * exp) list -> (((var * exp) list * c_map) * b_map, __)
    sigT **)

let rec contractcases oes fcon sig0 count inl sub0 = function
| [] -> Coq_existT ((([], count), inl), __)
| p :: cl' ->
  let (y, e) = p in
  let Coq_existT (x, _) = fcon sig0 count ((e, sub0), inl) __ in
  let (p0, inl') = x in
  let (e', count') = p0 in
  let Coq_existT (x0, _) = contractcases oes fcon sig0 count' inl' sub0 cl' in
  let (p1, inl'') = x0 in
  let (cl'', count'') = p1 in
  Coq_existT (((((y, e') :: cl''), count''), inl''), __)

(** val postcontractfun :
    ((exp * ctx_map) * b_map) -> (r_map -> c_map -> ((exp * ctx_map) * b_map)
    -> __ -> ((exp * c_map) * b_map, __) sigT) -> r_map -> c_map -> b_map ->
    ctx_map -> fundefs -> ((fundefs * c_map) * b_map, __) sigT **)

let rec postcontractfun oes fcon sig0 count inl sub0 = function
| Fcons (f, t0, ys, e, fds') ->
  if getd false f inl
  then postcontractfun oes fcon sig0 count inl sub0 fds'
  else (match getd O f count with
        | O ->
          let count' = dec_census sig0 e count in
          postcontractfun oes fcon sig0 count' inl sub0 fds'
        | S _ ->
          let Coq_existT (x, _) = fcon sig0 count ((e, sub0), inl) __ in
          let (p, inl') = x in
          let (e', count') = p in
          let Coq_existT (x0, _) =
            postcontractfun oes fcon sig0 count' inl' sub0 fds'
          in
          let (p0, inl'') = x0 in
          let (fds'', count'') = p0 in
          Coq_existT ((((Fcons (f, t0, ys, e', fds'')), count''), inl''), __))
| Fnil -> Coq_existT (((Fnil, count), inl), __)

(** val contract_func :
    (r_map, (c_map, (exp, (ctx_map, b_map) sigT) sigT) sigT) sigT ->
    ((exp * c_map) * b_map, __) sigT **)

let rec contract_func x =
  let sig0 = projT1 x in
  let count = projT1 (projT2 x) in
  let e = projT1 (projT2 (projT2 x)) in
  let sub0 = projT1 (projT2 (projT2 (projT2 x))) in
  let im = projT2 (projT2 (projT2 (projT2 x))) in
  let contract0 = fun sig1 count0 e0 sub1 im0 ->
    contract_func (Coq_existT (sig1, (Coq_existT (count0, (Coq_existT (e0,
      (Coq_existT (sub1, im0))))))))
  in
  (match e with
   | Econstr (x0, t0, ys, e') ->
     (match getd O x0 count with
      | O ->
        let count' = dec_census_list sig0 ys count in
        contract0 sig0 count' e' sub0 im
      | S _ ->
        let Coq_existT (x1, _) =
          contract0 sig0 count e' (M.set x0 (SVconstr (t0, ys)) sub0) im
        in
        let (p, im') = x1 in
        let (e'', count') = p in
        (match getd O x0 count' with
         | O ->
           let count'' = dec_census_list sig0 ys count' in
           Coq_existT (((e'', count''), im'), __)
         | S _ ->
           let ys' = apply_r_list sig0 ys in
           Coq_existT ((((Econstr (x0, t0, ys', e'')), count'), im'), __)))
   | Ecase (v, cl) ->
     let v' = apply_r sig0 v in
     (match M.get v' sub0 with
      | Some s ->
        (match s with
         | SVconstr (t0, _) ->
           let filtered_var = findtag cl t0 in
           (match filtered_var with
            | Some k ->
              contract0 sig0
                (dec_census_case sig0 cl t0
                  (dec_census_list sig0 (v :: []) count)) k sub0 im
            | None ->
              let filtered_var0 =
                contractcases (((Ecase (v, cl)), sub0), im)
                  (fun rm cm es _ ->
                  contract0 rm cm (fst (fst es)) (snd (fst es)) (snd es))
                  sig0 count im sub0 cl
              in
              let Coq_existT (x0, _) = filtered_var0 in
              let (p, im') = x0 in
              let (cl', count') = p in
              Coq_existT ((((Ecase (v', cl')), count'), im'), __))
         | SVfun (_, _, _) ->
           let filtered_var =
             contractcases (((Ecase (v, cl)), sub0), im) (fun rm cm es _ ->
               contract0 rm cm (fst (fst es)) (snd (fst es)) (snd es)) sig0
               count im sub0 cl
           in
           let Coq_existT (x0, _) = filtered_var in
           let (p, im') = x0 in
           let (cl', count') = p in
           Coq_existT ((((Ecase (v', cl')), count'), im'), __))
      | None ->
        let filtered_var =
          contractcases (((Ecase (v, cl)), sub0), im) (fun rm cm es _ ->
            contract0 rm cm (fst (fst es)) (snd (fst es)) (snd es)) sig0
            count im sub0 cl
        in
        let Coq_existT (x0, _) = filtered_var in
        let (p, im') = x0 in
        let (cl', count') = p in
        Coq_existT ((((Ecase (v', cl')), count'), im'), __))
   | Eproj (v, t0, n, y, e0) ->
     (match getd O v count with
      | O ->
        let count' = dec_census_list sig0 (y :: []) count in
        contract0 sig0 count' e0 sub0 im
      | S _ ->
        let y' = apply_r sig0 y in
        (match M.get y' sub0 with
         | Some s ->
           (match s with
            | SVconstr (_, ys) ->
              (match nthN ys n with
               | Some yn ->
                 let yn' = apply_r sig0 yn in
                 let count' = M.set y' (sub (getd O y' count) (S O)) count in
                 let count'' =
                   M.set v O
                     (M.set yn' (add (getd O v count) (getd O yn' count))
                       count')
                 in
                 contract0 (M.set v yn' sig0) count'' e0 sub0 im
               | None ->
                 let Coq_existT (x0, _) = contract0 sig0 count e0 sub0 im in
                 let (p, im') = x0 in
                 let (e', count') = p in
                 (match getd O v count' with
                  | O ->
                    let count'' = dec_census_list sig0 (y :: []) count' in
                    Coq_existT (((e', count''), im'), __)
                  | S _ ->
                    Coq_existT ((((Eproj (v, t0, n, y', e')), count'), im'),
                      __)))
            | SVfun (_, _, _) ->
              let Coq_existT (x0, _) = contract0 sig0 count e0 sub0 im in
              let (p, im') = x0 in
              let (e', count') = p in
              (match getd O v count' with
               | O ->
                 let count'' = dec_census_list sig0 (y :: []) count' in
                 Coq_existT (((e', count''), im'), __)
               | S _ ->
                 Coq_existT ((((Eproj (v, t0, n, y', e')), count'), im'), __)))
         | None ->
           let Coq_existT (x0, _) = contract0 sig0 count e0 sub0 im in
           let (p, im') = x0 in
           let (e', count') = p in
           (match getd O v count' with
            | O ->
              let count'' = dec_census_list sig0 (y :: []) count' in
              Coq_existT (((e', count''), im'), __)
            | S _ ->
              Coq_existT ((((Eproj (v, t0, n, y', e')), count'), im'), __))))
   | Efun (fl, e0) ->
     let filtered_var = precontractfun sig0 count sub0 fl in
     let (p, sub') = filtered_var in
     let (fl', count') = p in
     let Coq_existT (x0, _) = contract0 sig0 count' e0 sub' im in
     let (p0, im') = x0 in
     let (e', count'') = p0 in
     let Coq_existT (x1, _) =
       postcontractfun (((Efun (fl', e0)), sub0), im') (fun rm cm es _ ->
         contract0 rm cm (fst (fst es)) (snd (fst es)) (snd es)) sig0 count''
         im' sub0 fl'
     in
     let (p1, im'') = x1 in
     let (fl'', count''') = p1 in
     (match fl'' with
      | Fcons (_, _, _, _, _) ->
        Coq_existT ((((Efun (fl'', e')), count'''), im''), __)
      | Fnil -> Coq_existT (((e', count'''), im''), __))
   | Eapp (f, t0, ys) ->
     let f' = apply_r sig0 f in
     let ys' = apply_r_list sig0 ys in
     let filtered_var = getd O f' count in
     (match filtered_var with
      | O -> Coq_existT ((((Eapp (f', t0, ys')), count), im), __)
      | S n ->
        (match n with
         | O ->
           let filtered_var0 = M.get f' sub0 in
           (match filtered_var0 with
            | Some s ->
              (match s with
               | SVconstr (_, _) ->
                 Coq_existT ((((Eapp (f', t0, ys')), count), im), __)
               | SVfun (t', xs, m) ->
                 let filtered_var1 =
                   (&&) (Pos.eqb t' t0)
                     ((&&) (eqb (length ys) (length xs))
                       (negb (getd false f' im)))
                 in
                 if filtered_var1
                 then let im' = M.set f' true im in
                      let count' =
                        update_count_inlined ys' xs (M.set f' O count)
                      in
                      let Coq_existT (x0, _) =
                        contract0 (set_list (combine xs ys') sig0) count' m
                          sub0 im'
                      in
                      Coq_existT (x0, __)
                 else Coq_existT ((((Eapp (f', t0, ys')), count), im), __))
            | None -> Coq_existT ((((Eapp (f', t0, ys')), count), im), __))
         | S _ -> Coq_existT ((((Eapp (f', t0, ys')), count), im), __)))
   | Eprim (x0, f, ys, e0) ->
     (match getd O x0 count with
      | O ->
        let count' = dec_census_list sig0 ys count in
        contract0 sig0 count' e0 sub0 im
      | S _ ->
        let Coq_existT (x1, _) = contract0 sig0 count e0 sub0 im in
        let (p, im') = x1 in
        let (e', count') = p in
        (match getd O x0 count' with
         | O ->
           let count'' = dec_census_list sig0 ys count' in
           Coq_existT (((e', count''), im'), __)
         | S _ ->
           let ys' = apply_r_list sig0 ys in
           Coq_existT ((((Eprim (x0, f, ys', e')), count'), im'), __)))
   | Ehalt v -> Coq_existT ((((Ehalt (apply_r sig0 v)), count), im), __))

(** val contract :
    r_map -> c_map -> exp -> ctx_map -> b_map -> ((exp * c_map) * b_map, __)
    sigT **)

let contract sig0 count e sub0 im =
  contract_func (Coq_existT (sig0, (Coq_existT (count, (Coq_existT (e,
    (Coq_existT (sub0, im))))))))

(** val shrink_top : exp -> exp **)

let shrink_top e =
  let count = init_census e in
  let Coq_existT (x, _) = contract M.empty count e M.empty M.empty in
  let (p, _) = x in let (e', _) = p in e'

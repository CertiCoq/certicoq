open AstCommon
open BasicAst
open BinNat
open BinPos
open Datatypes
open L4_5_to_L5
open List0
open Monad0
open Nat0
open OptionMonad
open Classes0
open Cps
open Cps_util
open Ctx
open PolyEval
open Terms
open VarInterface
open Variables

let __ = let rec f _ = Obj.repr f in Obj.repr f

type coq_L5_conId = dcon

(** val coq_L5_conId_dec : coq_L5_conId -> coq_L5_conId -> bool **)

let coq_L5_conId_dec x y =
  let (i, n) = x in
  let (i0, n0) = y in
  let h = inductive_dec i i0 in if h then eq_dec coq_NEq n n0 else false

type conId_map = (coq_L5_conId * cTag) list

(** val dcon_to_info : cTag -> coq_L5_conId -> conId_map -> cTag **)

let rec dcon_to_info default_tag a = function
| [] -> default_tag
| p :: sig' ->
  let (cId, inf) = p in
  if coq_L5_conId_dec a cId then inf else dcon_to_info default_tag a sig'

(** val dcon_to_tag : cTag -> coq_L5_conId -> conId_map -> cTag **)

let dcon_to_tag =
  dcon_to_info

(** val fromN : int -> nat -> int list * int **)

let rec fromN n = function
| O -> ([], n)
| S m' -> let (l, nm) = fromN (Pos.add n 1) m' in ((n :: l), nm)

(** val ctx_bind_proj : cTag -> int -> nat -> var -> nat -> exp_ctx * var **)

let rec ctx_bind_proj tg r m n p =
  match m with
  | O -> (Hole_c, n)
  | S m' ->
    let (ctx_p', n') = ctx_bind_proj tg r m' n p in
    ((Eproj_c (n', tg, (N.of_nat (add m' p)), r, ctx_p')), (Pos.succ n'))

type t_info = fTag

type t_map = t_info M.t

(** val t_empty : t_map **)

let t_empty =
  M.empty

(** val get_f : fTag -> var -> t_map -> fTag **)

let get_f fun_tag n sig0 =
  match M.get n sig0 with
  | Some v -> v
  | None -> fun_tag

type s_map = var M.t

(** val s_empty : var M.t **)

let s_empty =
  M.empty

(** val get_s : coq_NVar -> s_map -> var **)

let get_s a sig0 =
  match M.get (fst a) sig0 with
  | Some v -> v
  | None -> 1

(** val set_s_list : coq_NVar list -> var list -> s_map -> s_map **)

let rec set_s_list lx ly sig0 =
  match lx with
  | [] -> sig0
  | x :: lx' ->
    (match ly with
     | [] -> sig0
     | y :: ly' -> set_s_list lx' ly' (M.set (fst x) y sig0))

type conv_env = (conId_map * t_map) * nEnv

(** val set_nt : var -> (name * t_info) -> conv_env -> conv_env **)

let set_nt x tn = function
| (p, t3) ->
  let (t1, t2) = p in ((t1, (M.set x (snd tn) t2)), (M.set x (fst tn) t3))

(** val set_t : var -> t_info -> conv_env -> conv_env **)

let set_t x ti = function
| (p, t3) -> let (t1, t2) = p in ((t1, (M.set x ti t2)), t3)

(** val set_n : var -> name -> conv_env -> conv_env **)

let set_n x n = function
| (p, t3) -> (p, (M.set x n t3))

(** val set_t_f_list :
    fTag -> var list -> coq_NVar list -> conv_env -> conv_env **)

let rec set_t_f_list fun_tag ns ts tgm =
  match ns with
  | [] -> tgm
  | n :: ns' ->
    (match ts with
     | [] -> tgm
     | t0 :: ts' ->
       set_t_f_list fun_tag ns' ts' (set_nt n ((snd t0), fun_tag) tgm))

(** val convert :
    cTag -> fTag -> fTag -> (coq_NVar, coq_L5Opid) coq_NTerm -> s_map ->
    s_map -> conv_env -> var -> ((exp * var) * conv_env) option **)

let convert default_tag fun_tag kon_tag =
  let rec convert0 e sv sk tgm n =
    match e with
    | Coq_vterm _ -> None
    | Coq_oterm (l, l0) ->
      (match l with
       | CHalt ->
         (match l0 with
          | [] -> None
          | b :: l1 ->
            let Coq_bterm (l2, h) = b in
            (match l2 with
             | [] ->
               (match l1 with
                | [] ->
                  pbind (coq_PMonad_Monad (Obj.magic coq_Monad_option))
                    (Obj.magic __) (convert_v h sv sk tgm n) (fun r ->
                    let (y, tgm0) = r in
                    let (y0, n') = y in
                    let (ctx_v, vn) = y0 in
                    ret (Obj.magic coq_Monad_option)
                      (((app_ctx_f ctx_v (Ehalt vn)), (Pos.succ n')), tgm0))
                | _ :: _ -> None)
             | _ :: _ -> None))
       | CRet ->
         (match l0 with
          | [] -> None
          | b :: l1 ->
            let Coq_bterm (l2, k) = b in
            (match l2 with
             | [] ->
               (match l1 with
                | [] -> None
                | b0 :: l3 ->
                  let Coq_bterm (l4, v) = b0 in
                  (match l4 with
                   | [] ->
                     (match l3 with
                      | [] ->
                        pbind (coq_PMonad_Monad (Obj.magic coq_Monad_option))
                          (Obj.magic __) (convert_v k sv sk tgm n) (fun r1 ->
                          let (y, tgm0) = r1 in
                          let (y0, n') = y in
                          let (ctx_k, kn) = y0 in
                          pbind
                            (coq_PMonad_Monad (Obj.magic coq_Monad_option))
                            (Obj.magic __) (convert_v v sv sk tgm0 n')
                            (fun r2 ->
                            let (y1, tgm1) = r2 in
                            let (y2, n'') = y1 in
                            let (ctx_v, vn) = y2 in
                            ret (Obj.magic coq_Monad_option)
                              (((app_ctx_f (comp_ctx_f ctx_k ctx_v) (Eapp
                                  (kn, kon_tag, (vn :: [])))), n''), tgm1)))
                      | _ :: _ -> None)
                   | _ :: _ -> None))
             | _ :: _ -> None))
       | CCall ->
         (match l0 with
          | [] -> None
          | b :: l1 ->
            let Coq_bterm (l2, f) = b in
            (match l2 with
             | [] ->
               (match l1 with
                | [] -> None
                | b0 :: l3 ->
                  let Coq_bterm (l4, k) = b0 in
                  (match l4 with
                   | [] ->
                     (match l3 with
                      | [] -> None
                      | b1 :: l5 ->
                        let Coq_bterm (l6, v) = b1 in
                        (match l6 with
                         | [] ->
                           (match l5 with
                            | [] ->
                              pbind
                                (coq_PMonad_Monad
                                  (Obj.magic coq_Monad_option))
                                (Obj.magic __) (getVar (Obj.magic f))
                                (fun f0 ->
                                pbind
                                  (coq_PMonad_Monad
                                    (Obj.magic coq_Monad_option))
                                  (Obj.magic __) (getVar (Obj.magic k))
                                  (fun k0 ->
                                  pbind
                                    (coq_PMonad_Monad
                                      (Obj.magic coq_Monad_option))
                                    (Obj.magic __) (getVar (Obj.magic v))
                                    (fun v0 ->
                                    let fv =
                                      if varClass varClassNVar f0
                                      then sv
                                      else sk
                                    in
                                    let kv =
                                      if varClass varClassNVar k0
                                      then sv
                                      else sk
                                    in
                                    let vv =
                                      if varClass varClassNVar v0
                                      then sv
                                      else sk
                                    in
                                    let f' = get_s f0 fv in
                                    ret (Obj.magic coq_Monad_option) (((Eapp
                                      (f',
                                      (get_f fun_tag f' (snd (fst tgm))),
                                      ((get_s k0 kv) :: ((get_s v0 vv) :: [])))),
                                      n), tgm))))
                            | _ :: _ -> None)
                         | _ :: _ -> None))
                   | _ :: _ -> None))
             | _ :: _ -> None))
       | CMatch ls ->
         (match l0 with
          | [] -> None
          | b :: lbt ->
            let Coq_bterm (l1, v) = b in
            (match l1 with
             | [] ->
               pbind (coq_PMonad_Monad (Obj.magic coq_Monad_option))
                 (Obj.magic __) (convert_v v sv sk tgm n) (fun r1 ->
                 let (y, tgm0) = r1 in
                 let (y0, n') = y in
                 let (ctx_v, vn) = y0 in
                 pbind (coq_PMonad_Monad (Obj.magic coq_Monad_option))
                   (Obj.magic __)
                   (fold_left (fun co b0 ->
                     pbind (coq_PMonad_Monad (Obj.magic coq_Monad_option))
                       (Obj.magic __) co (fun c ->
                       let (y1, n'0) = c in
                       let (y2, r) = y1 in
                       let (y3, tgm1) = y2 in
                       let (y4, sk0) = y3 in
                       let (y5, sv0) = y4 in
                       let (cbl, ls0) = y5 in
                       let Coq_bterm (xs, e0) = b0 in
                       (match ls0 with
                        | [] -> None
                        | y6 :: ls' ->
                          let (dcn, _) = y6 in
                          let lxs = length xs in
                          let tg =
                            dcon_to_tag default_tag dcn (fst (fst tgm1))
                          in
                          let (ctx_p, n'') = ctx_bind_proj tg r lxs n'0 O in
                          let (names, _) = fromN n'0 lxs in
                          let sv' = set_s_list xs names sv0 in
                          pbind
                            (coq_PMonad_Monad (Obj.magic coq_Monad_option))
                            (Obj.magic __) (convert0 e0 sv' sk0 tgm1 n'')
                            (fun r2 ->
                            let (y7, tgm2) = r2 in
                            let (ce, n''') = y7 in
                            ret (Obj.magic coq_Monad_option) ((((((((tg,
                              (app_ctx_f ctx_p ce)) :: cbl), ls'), sv0),
                              sk0), tgm2), r), n'''))))) lbt
                     (ret (Obj.magic coq_Monad_option) (((((([], ls), sv),
                       sk), tgm0), vn), n'))) (fun r2 ->
                   let (y1, n'') = r2 in
                   let (y2, vn0) = y1 in
                   let (y3, tgm1) = y2 in
                   let (y4, _) = y3 in
                   let (y5, _) = y4 in
                   let (cbls, _) = y5 in
                   ret (Obj.magic coq_Monad_option)
                     (((app_ctx_f ctx_v (Ecase (vn0, cbls))), n''), tgm1)))
             | _ :: _ -> None))
       | _ -> None)
  and convert_v v sv sk tgm n =
    match v with
    | Coq_vterm v0 ->
      if varClass varClassNVar v0
      then ret (Obj.magic coq_Monad_option) (((Hole_c, (get_s v0 sv)), n),
             tgm)
      else ret (Obj.magic coq_Monad_option) (((Hole_c, (get_s v0 sk)), n),
             tgm)
    | Coq_oterm (l, lbt) ->
      (match l with
       | CLambda ->
         (match lbt with
          | [] -> None
          | b :: l0 ->
            let Coq_bterm (l1, e) = b in
            (match l1 with
             | [] -> None
             | x :: l2 ->
               (match l2 with
                | [] -> None
                | k :: l3 ->
                  (match l3 with
                   | [] ->
                     (match l0 with
                      | [] ->
                        let tgm0 = set_nt (Pos.succ n) ((snd k), kon_tag) tgm
                        in
                        let tgm1 = set_n n (snd x) tgm0 in
                        pbind (coq_PMonad_Monad (Obj.magic coq_Monad_option))
                          (Obj.magic __)
                          (convert0 e (M.set (fst x) n sv)
                            (M.set (fst k) (Pos.succ n) sk) tgm1
                            (Pos.add n ((fun p->2*p) 1))) (fun r ->
                          let (y, tgm2) = r in
                          let (e', n') = y in
                          let tgm3 = set_t n' fun_tag tgm2 in
                          let fds = Fcons (n', fun_tag,
                            ((Pos.succ n) :: (n :: [])), e', Fnil)
                          in
                          ret (Obj.magic coq_Monad_option) ((((Efun1_c (fds,
                            Hole_c)), n'), (Pos.succ n')), tgm3))
                      | _ :: _ -> None)
                   | _ :: _ -> None))))
       | CKLambda ->
         (match lbt with
          | [] -> None
          | b :: l0 ->
            let Coq_bterm (l1, e) = b in
            (match l1 with
             | [] -> None
             | k :: l2 ->
               (match l2 with
                | [] ->
                  (match l0 with
                   | [] ->
                     let tgm0 = set_n n (snd k) tgm in
                     pbind (coq_PMonad_Monad (Obj.magic coq_Monad_option))
                       (Obj.magic __)
                       (convert0 e sv (M.set (fst k) n sk) tgm0 (Pos.succ n))
                       (fun r ->
                       let (y, tgm1) = r in
                       let (e', n') = y in
                       let fds = Fcons (n', kon_tag, (n :: []), e', Fnil) in
                       ret (Obj.magic coq_Monad_option) ((((Efun1_c (fds,
                         Hole_c)), n'), (Pos.succ n')),
                         (set_t n' kon_tag tgm1)))
                   | _ :: _ -> None)
                | _ :: _ -> None)))
       | CFix (_, i) ->
         (match lbt with
          | [] -> ret (Obj.magic coq_Monad_option) (((Hole_c, 1), n), tgm)
          | b :: _ ->
            let Coq_bterm (fvars, _) = b in
            let convert_fds =
              let rec convert_fds fds sv0 sk0 tgm0 fnames n0 =
                match fds with
                | [] -> ret coq_Monad_option ((Fnil, n0), tgm0)
                | b0 :: fds' ->
                  let Coq_bterm (_, v0) = b0 in
                  (match fnames with
                   | [] -> ret coq_Monad_option ((Fnil, n0), tgm0)
                   | currn :: fnames' ->
                     (match v0 with
                      | Coq_vterm _ -> ret coq_Monad_option ((Fnil, n0), tgm0)
                      | Coq_oterm (l0, l1) ->
                        (match l0 with
                         | CLambda ->
                           (match l1 with
                            | [] -> ret coq_Monad_option ((Fnil, n0), tgm0)
                            | b1 :: l2 ->
                              let Coq_bterm (l3, e) = b1 in
                              (match l3 with
                               | [] -> ret coq_Monad_option ((Fnil, n0), tgm0)
                               | x :: l4 ->
                                 (match l4 with
                                  | [] ->
                                    ret coq_Monad_option ((Fnil, n0), tgm0)
                                  | k :: l5 ->
                                    (match l5 with
                                     | [] ->
                                       (match l2 with
                                        | [] ->
                                          pbind
                                            (coq_PMonad_Monad
                                              coq_Monad_option)
                                            (Obj.magic __)
                                            (Obj.magic convert0 e
                                              (M.set (fst x) n0 sv0)
                                              (M.set (fst k) (Pos.succ n0)
                                                sk0)
                                              (set_nt (Pos.succ n0) (
                                                (snd k), kon_tag)
                                                (set_n n0 (snd x) tgm0))
                                              (Pos.add n0 ((fun p->2*p) 1)))
                                            (fun r1 ->
                                            let (y, tgm1) = r1 in
                                            let (ce, n') = y in
                                            pbind
                                              (coq_PMonad_Monad
                                                coq_Monad_option)
                                              (Obj.magic __)
                                              (convert_fds fds' sv0 sk0 tgm1
                                                fnames' n') (fun r2 ->
                                              let (y0, tgm2) = r2 in
                                              let (cfds, n'') = y0 in
                                              ret coq_Monad_option (((Fcons
                                                (currn, fun_tag,
                                                ((Pos.succ n0) :: (n0 :: [])),
                                                ce, cfds)), n''), tgm2)))
                                        | _ :: _ ->
                                          ret coq_Monad_option ((Fnil, n0),
                                            tgm0))
                                     | _ :: _ ->
                                       ret coq_Monad_option ((Fnil, n0), tgm0)))))
                         | _ -> ret coq_Monad_option ((Fnil, n0), tgm0))))
              in convert_fds
            in
            let (nfds, newn) = fromN n (length fvars) in
            let sv' = set_s_list fvars nfds sv in
            let tgm0 = set_t_f_list fun_tag nfds fvars tgm in
            pbind (coq_PMonad_Monad (Obj.magic coq_Monad_option))
              (Obj.magic __)
              (Obj.magic convert_fds lbt sv' sk tgm0 nfds newn) (fun r ->
              let (y, tgm1) = r in
              let (fds, n') = y in
              ret (Obj.magic coq_Monad_option) ((((Efun1_c (fds, Hole_c)),
                (nth i nfds 1)), n'), tgm1)))
       | CDCon (dcn, _) ->
         let convert_v_list =
           let rec convert_v_list lv sv0 sk0 tgm0 n0 =
             match lv with
             | [] -> ret coq_Monad_option (((Hole_c, []), n0), tgm0)
             | y :: lv' ->
               let Coq_bterm (_, v0) = y in
               pbind (coq_PMonad_Monad coq_Monad_option) (Obj.magic __)
                 (Obj.magic convert_v v0 sv0 sk0 tgm0 n0) (fun r1 ->
                 let (y0, tgm1) = r1 in
                 let (y1, n') = y0 in
                 let (ctx_v, vn) = y1 in
                 pbind (coq_PMonad_Monad coq_Monad_option) (Obj.magic __)
                   (convert_v_list lv' sv0 sk0 tgm1 n') (fun r2 ->
                   let (y2, tgm2) = r2 in
                   let (y3, n'') = y2 in
                   let (ctx_lv', ln') = y3 in
                   ret coq_Monad_option ((((comp_ctx_f ctx_v ctx_lv'),
                     (vn :: ln')), n''), tgm2)))
           in convert_v_list
         in
         let ctag = dcon_to_info default_tag dcn (fst (fst tgm)) in
         pbind (coq_PMonad_Monad (Obj.magic coq_Monad_option)) (Obj.magic __)
           (Obj.magic convert_v_list lbt sv sk tgm n) (fun r ->
           let (y, tgm0) = r in
           let (y0, n') = y in
           let (lv_ctx, nl) = y0 in
           ret (Obj.magic coq_Monad_option)
             ((((comp_ctx_f lv_ctx (Econstr_c (n', ctag, nl, Hole_c))), n'),
             (Pos.succ n')), (set_t n' ctag tgm0)))
       | _ -> None)
  in convert0

type ienv = (char list * itypPack) list

(** val convert_cnstrs :
    char list -> cTag list -> coq_Cnstr list -> inductive -> int -> iTag ->
    cEnv -> conId_map -> cEnv * conId_map **)

let rec convert_cnstrs tyname cct itC ind nCon niT ce dcm =
  match cct with
  | [] -> (ce, dcm)
  | cn :: cct' ->
    (match itC with
     | [] -> (ce, dcm)
     | cst :: icT' ->
       let { coq_CnstrNm = cname; coq_CnstrArity = ccn } = cst in
       convert_cnstrs tyname cct' icT' ind (N.add nCon 1) niT
         (M.set cn (((((Coq_nNamed cname), (Coq_nNamed tyname)), niT),
           (N.of_nat ccn)), nCon) ce) (((ind, nCon), cn) :: dcm))

(** val convert_typack :
    ityp list -> char list -> nat ->
    ((((iEnv * cEnv) * cTag) * iTag) * conId_map) ->
    (((iEnv * cEnv) * cTag) * iTag) * conId_map **)

let rec convert_typack typ idBundle n ice = match ice with
| (p, dcm) ->
  let (p0, niT) = p in
  let (p1, ncT) = p0 in
  let (ie, ce) = p1 in
  (match typ with
   | [] -> ice
   | y :: typ' ->
     let { itypNm = itN; itypCnstrs = itC } = y in
     let (cct, ncT') = fromN ncT (length itC) in
     let (ce', dcm') =
       convert_cnstrs itN cct itC { inductive_mind = idBundle;
         inductive_ind = n } 0 niT ce dcm
     in
     let ityi =
       combine cct
         (map (fun c ->
           let { coq_CnstrNm = _; coq_CnstrArity = n0 } = c in N.of_nat n0)
           itC)
     in
     convert_typack typ' idBundle (add n (S O)) (((((M.set niT ityi ie),
       ce'), ncT'), (Pos.succ niT)), dcm'))

(** val convert_env' :
    ienv -> ((((iEnv * cEnv) * cTag) * iTag) * conId_map) ->
    (((iEnv * cEnv) * cTag) * iTag) * conId_map **)

let rec convert_env' g ice =
  match g with
  | [] -> ice
  | p :: g' ->
    let (id, ty) = p in convert_env' g' (convert_typack ty id O ice)

(** val convert_env :
    cTag -> iTag -> ienv -> (((iEnv * cEnv) * cTag) * iTag) * conId_map **)

let convert_env default_tag default_itag g =
  let default_iEnv = M.set default_itag ((default_tag, 0) :: []) M.empty in
  let default_cEnv =
    M.set default_tag ((((Coq_nAnon, Coq_nAnon), default_itag), 0), 0) M.empty
  in
  convert_env' g ((((default_iEnv, default_cEnv), (Pos.succ default_tag)),
    (Pos.succ default_itag)), [])

(** val convert_top :
    cTag -> iTag -> fTag -> fTag -> (ienv * (coq_NVar, coq_L5Opid) coq_NTerm)
    -> (((((cEnv * nEnv) * fEnv) * cTag) * iTag) * exp) option **)

let convert_top default_tag default_itag fun_tag kon_tag ee =
  let (p, dcm) = convert_env default_tag default_itag (fst ee) in
  let (p0, itag) = p in
  let (p1, ctag) = p0 in
  let (_, cG) = p1 in
  pbind (coq_PMonad_Monad (Obj.magic coq_Monad_option)) (Obj.magic __)
    (Obj.magic convert default_tag fun_tag kon_tag (snd ee) s_empty s_empty
      ((dcm, t_empty), n_empty) ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p)
      ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) 1))))))) (fun r ->
    let (y, tgm) = r in
    let (er, _) = y in
    let (_, nM) = tgm in
    let fenv =
      M.set fun_tag (((fun p->2*p) 1), (0 :: (1 :: [])))
        (M.set kon_tag (1, (0 :: [])) M.empty)
    in
    ret (Obj.magic coq_Monad_option) (((((cG, nM), fenv), ctag), itag), er))

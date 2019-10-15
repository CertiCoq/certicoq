open BasicAst
open Basics
open Datatypes
open List0
open String1
open String0
open UsefulTypes
open List1
open PolyEval
open Terms
open VarInterface0
open VarInterface

type coq_L4_5Opid =
| NLambda
| NFix of nat * nat
| NDCon of dcon * nat
| NApply
| NLet
| NMatch of (dcon * nat) list

type coq_L5Opid =
| CLambda
| CKLambda
| CLet
| CFix of nat * nat
| CDCon of dcon * nat
| CHalt
| CRet
| CCall
| CMatch of (dcon * nat) list

(** val coq_Lam_e :
    'a1 -> ('a1, coq_L4_5Opid) coq_NTerm -> ('a1, coq_L4_5Opid) coq_NTerm **)

let coq_Lam_e v b =
  Coq_oterm (NLambda, ((Coq_bterm ((v :: []), b)) :: []))

(** val coq_Fix_e' :
    ('a1, coq_L4_5Opid) coq_BTerm list -> nat -> ('a1, coq_L4_5Opid) coq_NTerm **)

let coq_Fix_e' lbt n =
  Coq_oterm ((NFix ((Datatypes.length lbt), n)), lbt)

(** val coq_Lam_c :
    'a1 -> 'a1 -> ('a1, coq_L5Opid) coq_NTerm -> ('a1, coq_L5Opid) coq_NTerm **)

let coq_Lam_c v vk b =
  Coq_oterm (CLambda, ((Coq_bterm ((v :: (vk :: [])), b)) :: []))

(** val coq_KLam_c :
    'a1 -> ('a1, coq_L5Opid) coq_NTerm -> ('a1, coq_L5Opid) coq_NTerm **)

let coq_KLam_c v b =
  Coq_oterm (CKLambda, ((Coq_bterm ((v :: []), b)) :: []))

(** val coq_ContApp_c :
    ('a1, coq_L5Opid) coq_NTerm -> ('a1, coq_L5Opid) coq_NTerm -> ('a1,
    coq_L5Opid) coq_NTerm **)

let coq_ContApp_c f a =
  Coq_oterm (CRet, ((Coq_bterm ([], f)) :: ((Coq_bterm ([], a)) :: [])))

(** val coq_Halt_c :
    ('a1, coq_L5Opid) coq_NTerm -> ('a1, coq_L5Opid) coq_NTerm **)

let coq_Halt_c v =
  Coq_oterm (CHalt, ((Coq_bterm ([], v)) :: []))

(** val coq_Call_c :
    ('a1, coq_L5Opid) coq_NTerm -> ('a1, coq_L5Opid) coq_NTerm -> ('a1,
    coq_L5Opid) coq_NTerm -> ('a1, coq_L5Opid) coq_NTerm **)

let coq_Call_c f k a =
  Coq_oterm (CCall, ((Coq_bterm ([], f)) :: ((Coq_bterm ([],
    k)) :: ((Coq_bterm ([], a)) :: []))))

(** val coq_Con_c :
    dcon -> ('a1, coq_L5Opid) coq_NTerm list -> ('a1, coq_L5Opid) coq_NTerm **)

let coq_Con_c dc args =
  Coq_oterm ((CDCon (dc, (Datatypes.length args))),
    (map (fun x -> Coq_bterm ([], x)) args))

(** val is_valueb : ('a1, coq_L4_5Opid) coq_NTerm -> bool **)

let rec is_valueb = function
| Coq_vterm _ -> true
| Coq_oterm (c, lb) ->
  (match c with
   | NLambda -> true
   | NFix (_, _) -> true
   | NDCon (_, _) -> ball (map (compose is_valueb get_nt) lb)
   | _ -> false)

(** val contVars :
    ('a1, bool) coq_FreshVars -> nat -> 'a1 list -> 'a1 list **)

let contVars freshv n suggestions =
  freshVars freshv n (Some false) [] suggestions

(** val mkSuggestion :
    'a1 coq_Deq -> ('a1, bool) coq_VarClass -> ('a1, bool) coq_FreshVars ->
    'a1 coq_UpdateName -> char list -> 'a1 **)

let mkSuggestion deqnvar varcl freshv upnm s =
  updateName upnm ((nvarx deqnvar varcl freshv), (Coq_nNamed s))

(** val contVar :
    'a1 coq_Deq -> ('a1, bool) coq_VarClass -> ('a1, bool) coq_FreshVars ->
    'a1 coq_UpdateName -> 'a1 **)

let contVar deqnvar varcl freshv upnm =
  nth O
    (freshVars freshv (S O) (Some false) []
      ((mkSuggestion deqnvar varcl freshv upnm ('k'::[])) :: []))
    (nvarx deqnvar varcl freshv)

(** val haltCont :
    'a1 coq_Deq -> ('a1, bool) coq_VarClass -> ('a1, bool) coq_FreshVars ->
    'a1 coq_UpdateName -> ('a1, coq_L5Opid) coq_NTerm **)

let haltCont deqnvar varcl freshv upnm =
  coq_KLam_c (contVar deqnvar varcl freshv upnm)
    (coq_Halt_c (Coq_vterm (contVar deqnvar varcl freshv upnm)))

(** val cps_cvt_apply_aux :
    ('a1, coq_L5Opid) coq_NTerm -> ('a1, coq_L5Opid) coq_NTerm -> ('a1,
    coq_L5Opid) coq_NTerm -> 'a1 -> 'a1 -> ('a1, coq_L5Opid) coq_NTerm **)

let cps_cvt_apply_aux ce1 e2 k k1 k2 =
  coq_ContApp_c ce1
    (coq_KLam_c k1
      (coq_ContApp_c e2
        (coq_KLam_c k2 (coq_Call_c (Coq_vterm k1) k (Coq_vterm k2)))))

(** val cps_cvt_apply :
    'a1 coq_Deq -> ('a1, bool) coq_VarClass -> ('a1, bool) coq_FreshVars ->
    'a1 coq_UpdateName -> (('a1, coq_L4_5Opid) coq_NTerm -> ('a1, coq_L5Opid)
    coq_NTerm) -> ('a1, coq_L5Opid) coq_NTerm -> ('a1, coq_L4_5Opid)
    coq_NTerm -> ('a1, coq_L5Opid) coq_NTerm **)

let cps_cvt_apply deqnvar varcl freshv upnm cps_cvt0 ce1 e2 =
  let knames =
    ('k'::[]) :: (('k'::('a'::('p'::('f'::[])))) :: (('k'::('a'::('p'::('A'::('r'::('g'::[])))))) :: []))
  in
  let kvars =
    contVars freshv (S (S (S O)))
      (map (mkSuggestion deqnvar varcl freshv upnm) knames)
  in
  let k = nth O kvars (nvarx deqnvar varcl freshv) in
  let k1 = nth (S O) kvars (nvarx deqnvar varcl freshv) in
  let k2 = nth (S (S O)) kvars (nvarx deqnvar varcl freshv) in
  coq_KLam_c k (cps_cvt_apply_aux ce1 (cps_cvt0 e2) (Coq_vterm k) k1 k2)

(** val cps_cvt_lambda :
    'a1 coq_Deq -> ('a1, bool) coq_VarClass -> ('a1, bool) coq_FreshVars ->
    'a1 coq_UpdateName -> (('a1, coq_L4_5Opid) coq_NTerm -> ('a1, coq_L5Opid)
    coq_NTerm) -> 'a1 -> ('a1, coq_L4_5Opid) coq_NTerm -> ('a1, coq_L5Opid)
    coq_NTerm **)

let cps_cvt_lambda deqnvar varcl freshv upnm cps_cvt0 x b =
  let kv = contVar deqnvar varcl freshv upnm in
  coq_Lam_c x kv (coq_ContApp_c (cps_cvt0 b) (Coq_vterm kv))

(** val cps_cvt_fn_list' :
    (('a1, coq_L4_5Opid) coq_NTerm -> ('a1, coq_L5Opid) coq_NTerm) -> ('a1,
    coq_L4_5Opid) coq_BTerm list -> ('a1, coq_L5Opid) coq_BTerm list **)

let cps_cvt_fn_list' f es =
  map (fun b ->
    let e = get_nt b in let vars = get_vars b in Coq_bterm (vars, (f e))) es

(** val cps_cvt_val' :
    'a1 coq_Deq -> ('a1, bool) coq_VarClass -> ('a1, bool) coq_FreshVars ->
    'a1 coq_UpdateName -> (('a1, coq_L4_5Opid) coq_NTerm -> ('a1, coq_L5Opid)
    coq_NTerm) -> ('a1, coq_L4_5Opid) coq_NTerm -> ('a1, coq_L5Opid) coq_NTerm **)

let rec cps_cvt_val' deqnvar varcl freshv upnm cps_cvt0 e = match e with
| Coq_vterm n -> Coq_vterm n
| Coq_oterm (l0, lb) ->
  (match l0 with
   | NLambda ->
     (match lb with
      | [] ->
        Coq_oterm (CLambda,
          (map (compose (fun x -> Coq_bterm ([], x)) (fun x -> Coq_vterm x))
            (free_vars deqnvar e)))
      | b0 :: l ->
        let Coq_bterm (l1, b) = b0 in
        (match l1 with
         | [] ->
           Coq_oterm (CLambda,
             (map
               (compose (fun x -> Coq_bterm ([], x)) (fun x -> Coq_vterm x))
               (free_vars deqnvar e)))
         | x :: l2 ->
           (match l2 with
            | [] ->
              (match l with
               | [] -> cps_cvt_lambda deqnvar varcl freshv upnm cps_cvt0 x b
               | _ :: _ ->
                 Coq_oterm (CLambda,
                   (map
                     (compose (fun x0 -> Coq_bterm ([], x0)) (fun x0 ->
                       Coq_vterm x0)) (free_vars deqnvar e))))
            | _ :: _ ->
              Coq_oterm (CLambda,
                (map
                  (compose (fun x0 -> Coq_bterm ([], x0)) (fun x0 ->
                    Coq_vterm x0)) (free_vars deqnvar e))))))
   | NFix (nargs, i) ->
     Coq_oterm ((CFix (nargs, i)),
       (cps_cvt_fn_list' (cps_cvt_val' deqnvar varcl freshv upnm cps_cvt0) lb))
   | NDCon (d, l) ->
     let fb = fun b -> Coq_bterm ([],
       (cps_cvt_val' deqnvar varcl freshv upnm cps_cvt0 (get_nt b)))
     in
     Coq_oterm ((CDCon (d, l)), (map fb lb))
   | NApply ->
     Coq_oterm (CLambda,
       (map (compose (fun x -> Coq_bterm ([], x)) (fun x -> Coq_vterm x))
         (free_vars deqnvar e)))
   | NLet ->
     Coq_oterm (CLambda,
       (map (compose (fun x -> Coq_bterm ([], x)) (fun x -> Coq_vterm x))
         (free_vars deqnvar e)))
   | NMatch _ ->
     Coq_oterm (CLambda,
       (map (compose (fun x -> Coq_bterm ([], x)) (fun x -> Coq_vterm x))
         (free_vars deqnvar e))))

(** val cps_cvts_chain :
    'a1 coq_Deq -> ('a1, bool) coq_VarClass -> ('a1, bool) coq_FreshVars ->
    (('a1, coq_L4_5Opid) coq_NTerm -> ('a1, coq_L5Opid) coq_NTerm) -> 'a1
    list -> ('a1, coq_L4_5Opid) coq_BTerm list -> ('a1, coq_L5Opid) coq_NTerm
    -> ('a1, coq_L5Opid) coq_NTerm **)

let rec cps_cvts_chain deqnvar varcl freshv cps_cvt0 vs es c =
  match es with
  | [] -> c
  | b :: es0 ->
    let Coq_bterm (_, e) = b in
    (match vs with
     | [] ->
       coq_ContApp_c (cps_cvt0 e)
         (coq_KLam_c (nvarx deqnvar varcl freshv)
           (cps_cvts_chain deqnvar varcl freshv cps_cvt0 [] es0 c))
     | kvh :: kvt ->
       coq_ContApp_c (cps_cvt0 e)
         (coq_KLam_c kvh
           (cps_cvts_chain deqnvar varcl freshv cps_cvt0 kvt es0 c)))

(** val cps_cvt_branch :
    (('a1, coq_L4_5Opid) coq_NTerm -> ('a1, coq_L5Opid) coq_NTerm) -> ('a1,
    coq_L5Opid) coq_NTerm -> ('a1, coq_L4_5Opid) coq_BTerm -> ('a1,
    coq_L5Opid) coq_BTerm **)

let cps_cvt_branch cps_cvt0 kv = function
| Coq_bterm (vars, nt) -> Coq_bterm (vars, (coq_ContApp_c (cps_cvt0 nt) kv))

(** val cps_cvt_branches :
    (('a1, coq_L4_5Opid) coq_NTerm -> ('a1, coq_L5Opid) coq_NTerm) -> ('a1,
    coq_L5Opid) coq_NTerm -> ('a1, coq_L4_5Opid) coq_BTerm list -> ('a1,
    coq_L5Opid) coq_BTerm list **)

let cps_cvt_branches cps_cvt0 kv =
  map (cps_cvt_branch cps_cvt0 kv)

(** val val_outer :
    'a1 coq_Deq -> ('a1, bool) coq_VarClass -> ('a1, bool) coq_FreshVars ->
    'a1 coq_UpdateName -> ('a1, coq_L5Opid) coq_NTerm -> ('a1, coq_L5Opid)
    coq_NTerm **)

let val_outer deqnvar varcl freshv upnm ce =
  let kv = contVar deqnvar varcl freshv upnm in
  coq_KLam_c kv (coq_ContApp_c (Coq_vterm kv) ce)

(** val cps_cvt :
    'a1 coq_Deq -> ('a1, bool) coq_VarClass -> ('a1, bool) coq_FreshVars ->
    'a1 coq_UpdateName -> ('a1, coq_L4_5Opid) coq_NTerm -> ('a1, coq_L5Opid)
    coq_NTerm **)

let rec cps_cvt deqnvar varcl freshv upnm e =
  if is_valueb e
  then val_outer deqnvar varcl freshv upnm
         (cps_cvt_val' deqnvar varcl freshv upnm
           (cps_cvt deqnvar varcl freshv upnm) e)
  else (match e with
        | Coq_vterm _ ->
          Coq_oterm (CLambda,
            (map
              (compose (fun x -> Coq_bterm ([], x)) (fun x -> Coq_vterm x))
              (free_vars deqnvar e)))
        | Coq_oterm (l, es) ->
          (match l with
           | NLambda ->
             Coq_oterm (CLambda,
               (map
                 (compose (fun x -> Coq_bterm ([], x)) (fun x -> Coq_vterm x))
                 (free_vars deqnvar e)))
           | NFix (_, _) ->
             Coq_oterm (CLambda,
               (map
                 (compose (fun x -> Coq_bterm ([], x)) (fun x -> Coq_vterm x))
                 (free_vars deqnvar e)))
           | NDCon (d, _) ->
             let knames =
               map
                 (compose
                   (compose (mkSuggestion deqnvar varcl freshv upnm)
                     (fun x ->
                     append ('x'::[])
                       (append x ('k'::('d'::('c'::('o'::('n'::[]))))))))
                   nat2string10) (List0.seq O (Datatypes.length es))
             in
             let kvars =
               contVars freshv (S (Datatypes.length es))
                 ((mkSuggestion deqnvar varcl freshv upnm ('k'::[])) :: knames)
             in
             let k = hd (nvarx deqnvar varcl freshv) kvars in
             let tlkv = tl kvars in
             coq_KLam_c k
               (cps_cvts_chain deqnvar varcl freshv
                 (cps_cvt deqnvar varcl freshv upnm) tlkv es
                 (coq_ContApp_c (Coq_vterm k)
                   (coq_Con_c d (map (fun x -> Coq_vterm x) tlkv))))
           | NApply ->
             (match es with
              | [] ->
                Coq_oterm (CLambda,
                  (map
                    (compose (fun x -> Coq_bterm ([], x)) (fun x -> Coq_vterm
                      x)) (free_vars deqnvar e)))
              | b :: l0 ->
                let Coq_bterm (l1, e1) = b in
                (match l1 with
                 | [] ->
                   (match l0 with
                    | [] ->
                      Coq_oterm (CLambda,
                        (map
                          (compose (fun x -> Coq_bterm ([], x)) (fun x ->
                            Coq_vterm x)) (free_vars deqnvar e)))
                    | b0 :: l2 ->
                      let Coq_bterm (l3, e2) = b0 in
                      (match l3 with
                       | [] ->
                         (match l2 with
                          | [] ->
                            cps_cvt_apply deqnvar varcl freshv upnm
                              (cps_cvt deqnvar varcl freshv upnm)
                              (cps_cvt deqnvar varcl freshv upnm e1) e2
                          | _ :: _ ->
                            Coq_oterm (CLambda,
                              (map
                                (compose (fun x -> Coq_bterm ([], x))
                                  (fun x -> Coq_vterm x))
                                (free_vars deqnvar e))))
                       | _ :: _ ->
                         Coq_oterm (CLambda,
                           (map
                             (compose (fun x -> Coq_bterm ([], x)) (fun x ->
                               Coq_vterm x)) (free_vars deqnvar e)))))
                 | _ :: _ ->
                   Coq_oterm (CLambda,
                     (map
                       (compose (fun x -> Coq_bterm ([], x)) (fun x ->
                         Coq_vterm x)) (free_vars deqnvar e)))))
           | NLet ->
             (match es with
              | [] ->
                Coq_oterm (CLambda,
                  (map
                    (compose (fun x -> Coq_bterm ([], x)) (fun x -> Coq_vterm
                      x)) (free_vars deqnvar e)))
              | b :: l0 ->
                let Coq_bterm (l1, e1) = b in
                (match l1 with
                 | [] ->
                   (match l0 with
                    | [] ->
                      Coq_oterm (CLambda,
                        (map
                          (compose (fun x -> Coq_bterm ([], x)) (fun x ->
                            Coq_vterm x)) (free_vars deqnvar e)))
                    | b0 :: l2 ->
                      let Coq_bterm (l3, e2) = b0 in
                      (match l3 with
                       | [] ->
                         Coq_oterm (CLambda,
                           (map
                             (compose (fun x -> Coq_bterm ([], x)) (fun x ->
                               Coq_vterm x)) (free_vars deqnvar e)))
                       | x :: l4 ->
                         (match l4 with
                          | [] ->
                            (match l2 with
                             | [] ->
                               let cpsLam =
                                 val_outer deqnvar varcl freshv upnm
                                   (cps_cvt_lambda deqnvar varcl freshv upnm
                                     (cps_cvt deqnvar varcl freshv upnm) x e2)
                               in
                               cps_cvt_apply deqnvar varcl freshv upnm
                                 (cps_cvt deqnvar varcl freshv upnm) cpsLam e1
                             | _ :: _ ->
                               Coq_oterm (CLambda,
                                 (map
                                   (compose (fun x0 -> Coq_bterm ([], x0))
                                     (fun x0 -> Coq_vterm x0))
                                   (free_vars deqnvar e))))
                          | _ :: _ ->
                            Coq_oterm (CLambda,
                              (map
                                (compose (fun x0 -> Coq_bterm ([], x0))
                                  (fun x0 -> Coq_vterm x0))
                                (free_vars deqnvar e))))))
                 | _ :: _ ->
                   Coq_oterm (CLambda,
                     (map
                       (compose (fun x -> Coq_bterm ([], x)) (fun x ->
                         Coq_vterm x)) (free_vars deqnvar e)))))
           | NMatch brl ->
             (match es with
              | [] ->
                Coq_oterm (CLambda,
                  (map
                    (compose (fun x -> Coq_bterm ([], x)) (fun x -> Coq_vterm
                      x)) (free_vars deqnvar e)))
              | b :: brr ->
                let Coq_bterm (l0, discriminee) = b in
                (match l0 with
                 | [] ->
                   let knames = ('k'::[]) :: (('k'::('m'::('d'::[]))) :: [])
                   in
                   let kvars =
                     contVars freshv (S (S O))
                       (map (mkSuggestion deqnvar varcl freshv upnm) knames)
                   in
                   let k = nth O kvars (nvarx deqnvar varcl freshv) in
                   let kd = nth (S O) kvars (nvarx deqnvar varcl freshv) in
                   let brrc = (Coq_bterm ([], (Coq_vterm
                     kd))) :: (cps_cvt_branches
                                (cps_cvt deqnvar varcl freshv upnm)
                                (Coq_vterm k) brr)
                   in
                   coq_KLam_c k
                     (coq_ContApp_c
                       (cps_cvt deqnvar varcl freshv upnm discriminee)
                       (coq_KLam_c kd (Coq_oterm ((CMatch brl), brrc))))
                 | _ :: _ ->
                   Coq_oterm (CLambda,
                     (map
                       (compose (fun x -> Coq_bterm ([], x)) (fun x ->
                         Coq_vterm x)) (free_vars deqnvar e)))))))

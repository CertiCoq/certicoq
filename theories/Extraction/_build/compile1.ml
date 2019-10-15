open Ast0
open AstCommon
open BasicAst
open Datatypes
open List0
open Nat0
open PeanoNat
open Compile0
open Utils

type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

type coq_L1gTerm = coq_Term

type coq_L1gTerms = coq_Term list

type coq_L1gBrs = coq_Brs

type coq_L1gDefs = coq_Defs

type coq_L1gPgm = coq_L1gTerm coq_Program

type coq_L1gEC = coq_L1gTerm envClass

type coq_L1gEnv = coq_L1gTerm environ

type projection = inductive * nat

(** val project_dec : projection -> projection -> bool **)

let project_dec s1 s2 =
  let (i, n) = s1 in
  let (i0, n0) = s2 in
  let s = inductive_dec i i0 in if s then Nat.eq_dec n n0 else false

type coq_Term =
| TRel of nat
| TProof
| TLambda of name * coq_Term
| TLetIn of name * coq_Term * coq_Term
| TApp of coq_Term * coq_Term
| TConst of char list
| TConstruct of inductive * nat * coq_Terms
| TCase of inductive * coq_Term * coq_Brs
| TFix of coq_Defs * nat
| TProj of projection * coq_Term
| TWrong of char list
and coq_Terms =
| Coq_tnil
| Coq_tcons of coq_Term * coq_Terms
and coq_Brs =
| Coq_bnil
| Coq_bcons of nat * coq_Term * coq_Brs
and coq_Defs =
| Coq_dnil
| Coq_dcons of name * coq_Term * nat * coq_Defs

(** val coq_Term_rect :
    (nat -> 'a1) -> 'a1 -> (name -> coq_Term -> 'a1 -> 'a1) -> (name ->
    coq_Term -> 'a1 -> coq_Term -> 'a1 -> 'a1) -> (coq_Term -> 'a1 ->
    coq_Term -> 'a1 -> 'a1) -> (char list -> 'a1) -> (inductive -> nat ->
    coq_Terms -> 'a1) -> (inductive -> coq_Term -> 'a1 -> coq_Brs -> 'a1) ->
    (coq_Defs -> nat -> 'a1) -> (projection -> coq_Term -> 'a1 -> 'a1) ->
    (char list -> 'a1) -> coq_Term -> 'a1 **)

let rec coq_Term_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 = function
| TRel n -> f n
| TProof -> f0
| TLambda (n, t0) ->
  f1 n t0 (coq_Term_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 t0)
| TLetIn (n, t0, t1) ->
  f2 n t0 (coq_Term_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 t0) t1
    (coq_Term_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 t1)
| TApp (t0, t1) ->
  f3 t0 (coq_Term_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 t0) t1
    (coq_Term_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 t1)
| TConst s -> f4 s
| TConstruct (i, n, t0) -> f5 i n t0
| TCase (i, t0, b) ->
  f6 i t0 (coq_Term_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 t0) b
| TFix (d, n) -> f7 d n
| TProj (p, t0) -> f8 p t0 (coq_Term_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 t0)
| TWrong s -> f9 s

(** val coq_Term_rec :
    (nat -> 'a1) -> 'a1 -> (name -> coq_Term -> 'a1 -> 'a1) -> (name ->
    coq_Term -> 'a1 -> coq_Term -> 'a1 -> 'a1) -> (coq_Term -> 'a1 ->
    coq_Term -> 'a1 -> 'a1) -> (char list -> 'a1) -> (inductive -> nat ->
    coq_Terms -> 'a1) -> (inductive -> coq_Term -> 'a1 -> coq_Brs -> 'a1) ->
    (coq_Defs -> nat -> 'a1) -> (projection -> coq_Term -> 'a1 -> 'a1) ->
    (char list -> 'a1) -> coq_Term -> 'a1 **)

let rec coq_Term_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 = function
| TRel n -> f n
| TProof -> f0
| TLambda (n, t0) -> f1 n t0 (coq_Term_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 t0)
| TLetIn (n, t0, t1) ->
  f2 n t0 (coq_Term_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 t0) t1
    (coq_Term_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 t1)
| TApp (t0, t1) ->
  f3 t0 (coq_Term_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 t0) t1
    (coq_Term_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 t1)
| TConst s -> f4 s
| TConstruct (i, n, t0) -> f5 i n t0
| TCase (i, t0, b) ->
  f6 i t0 (coq_Term_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 t0) b
| TFix (d, n) -> f7 d n
| TProj (p, t0) -> f8 p t0 (coq_Term_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 t0)
| TWrong s -> f9 s

(** val coq_Terms_rect :
    'a1 -> (coq_Term -> coq_Terms -> 'a1 -> 'a1) -> coq_Terms -> 'a1 **)

let rec coq_Terms_rect f f0 = function
| Coq_tnil -> f
| Coq_tcons (t0, t1) -> f0 t0 t1 (coq_Terms_rect f f0 t1)

(** val coq_Terms_rec :
    'a1 -> (coq_Term -> coq_Terms -> 'a1 -> 'a1) -> coq_Terms -> 'a1 **)

let rec coq_Terms_rec f f0 = function
| Coq_tnil -> f
| Coq_tcons (t0, t1) -> f0 t0 t1 (coq_Terms_rec f f0 t1)

(** val coq_Brs_rect :
    'a1 -> (nat -> coq_Term -> coq_Brs -> 'a1 -> 'a1) -> coq_Brs -> 'a1 **)

let rec coq_Brs_rect f f0 = function
| Coq_bnil -> f
| Coq_bcons (n, t, b0) -> f0 n t b0 (coq_Brs_rect f f0 b0)

(** val coq_Brs_rec :
    'a1 -> (nat -> coq_Term -> coq_Brs -> 'a1 -> 'a1) -> coq_Brs -> 'a1 **)

let rec coq_Brs_rec f f0 = function
| Coq_bnil -> f
| Coq_bcons (n, t, b0) -> f0 n t b0 (coq_Brs_rec f f0 b0)

(** val coq_Defs_rect :
    'a1 -> (name -> coq_Term -> nat -> coq_Defs -> 'a1 -> 'a1) -> coq_Defs ->
    'a1 **)

let rec coq_Defs_rect f f0 = function
| Coq_dnil -> f
| Coq_dcons (n, t, n0, d0) -> f0 n t n0 d0 (coq_Defs_rect f f0 d0)

(** val coq_Defs_rec :
    'a1 -> (name -> coq_Term -> nat -> coq_Defs -> 'a1 -> 'a1) -> coq_Defs ->
    'a1 **)

let rec coq_Defs_rec f f0 = function
| Coq_dnil -> f
| Coq_dcons (n, t, n0, d0) -> f0 n t n0 d0 (coq_Defs_rec f f0 d0)

(** val coq_Terms_list : coq_Terms -> coq_Term list **)

let rec coq_Terms_list = function
| Coq_tnil -> []
| Coq_tcons (u, us) -> u :: (coq_Terms_list us)

(** val tlength : coq_Terms -> nat **)

let rec tlength = function
| Coq_tnil -> O
| Coq_tcons (_, ts0) -> S (tlength ts0)

type coq_R_tlength =
| R_tlength_0 of coq_Terms
| R_tlength_1 of coq_Terms * coq_Term * coq_Terms * nat * coq_R_tlength

(** val coq_R_tlength_rect :
    (coq_Terms -> __ -> 'a1) -> (coq_Terms -> coq_Term -> coq_Terms -> __ ->
    nat -> coq_R_tlength -> 'a1 -> 'a1) -> coq_Terms -> nat -> coq_R_tlength
    -> 'a1 **)

let rec coq_R_tlength_rect f f0 _ _ = function
| R_tlength_0 ts -> f ts __
| R_tlength_1 (ts, _x, ts0, _res, r0) ->
  f0 ts _x ts0 __ _res r0 (coq_R_tlength_rect f f0 ts0 _res r0)

(** val coq_R_tlength_rec :
    (coq_Terms -> __ -> 'a1) -> (coq_Terms -> coq_Term -> coq_Terms -> __ ->
    nat -> coq_R_tlength -> 'a1 -> 'a1) -> coq_Terms -> nat -> coq_R_tlength
    -> 'a1 **)

let rec coq_R_tlength_rec f f0 _ _ = function
| R_tlength_0 ts -> f ts __
| R_tlength_1 (ts, _x, ts0, _res, r0) ->
  f0 ts _x ts0 __ _res r0 (coq_R_tlength_rec f f0 ts0 _res r0)

(** val tlength_rect :
    (coq_Terms -> __ -> 'a1) -> (coq_Terms -> coq_Term -> coq_Terms -> __ ->
    'a1 -> 'a1) -> coq_Terms -> 'a1 **)

let rec tlength_rect f0 f ts =
  let f1 = f0 ts in
  let f2 = f ts in
  (match ts with
   | Coq_tnil -> f1 __
   | Coq_tcons (t, t0) ->
     let f3 = f2 t t0 __ in let hrec = tlength_rect f0 f t0 in f3 hrec)

(** val tlength_rec :
    (coq_Terms -> __ -> 'a1) -> (coq_Terms -> coq_Term -> coq_Terms -> __ ->
    'a1 -> 'a1) -> coq_Terms -> 'a1 **)

let tlength_rec =
  tlength_rect

(** val coq_R_tlength_correct : coq_Terms -> nat -> coq_R_tlength **)

let coq_R_tlength_correct ts _res =
  tlength_rect (fun y _ _ _ -> R_tlength_0 y) (fun y y0 y1 _ y3 _ _ ->
    R_tlength_1 (y, y0, y1, (tlength y1), (y3 (tlength y1) __))) ts _res __

(** val blength : coq_Brs -> nat **)

let rec blength = function
| Coq_bnil -> O
| Coq_bcons (_, _, ts0) -> S (blength ts0)

type coq_R_blength =
| R_blength_0 of coq_Brs
| R_blength_1 of coq_Brs * nat * coq_Term * coq_Brs * nat * coq_R_blength

(** val coq_R_blength_rect :
    (coq_Brs -> __ -> 'a1) -> (coq_Brs -> nat -> coq_Term -> coq_Brs -> __ ->
    nat -> coq_R_blength -> 'a1 -> 'a1) -> coq_Brs -> nat -> coq_R_blength ->
    'a1 **)

let rec coq_R_blength_rect f f0 _ _ = function
| R_blength_0 ts -> f ts __
| R_blength_1 (ts, _x, _x0, ts0, _res, r0) ->
  f0 ts _x _x0 ts0 __ _res r0 (coq_R_blength_rect f f0 ts0 _res r0)

(** val coq_R_blength_rec :
    (coq_Brs -> __ -> 'a1) -> (coq_Brs -> nat -> coq_Term -> coq_Brs -> __ ->
    nat -> coq_R_blength -> 'a1 -> 'a1) -> coq_Brs -> nat -> coq_R_blength ->
    'a1 **)

let rec coq_R_blength_rec f f0 _ _ = function
| R_blength_0 ts -> f ts __
| R_blength_1 (ts, _x, _x0, ts0, _res, r0) ->
  f0 ts _x _x0 ts0 __ _res r0 (coq_R_blength_rec f f0 ts0 _res r0)

(** val blength_rect :
    (coq_Brs -> __ -> 'a1) -> (coq_Brs -> nat -> coq_Term -> coq_Brs -> __ ->
    'a1 -> 'a1) -> coq_Brs -> 'a1 **)

let rec blength_rect f0 f ts =
  let f1 = f0 ts in
  let f2 = f ts in
  (match ts with
   | Coq_bnil -> f1 __
   | Coq_bcons (n, t, b) ->
     let f3 = f2 n t b __ in let hrec = blength_rect f0 f b in f3 hrec)

(** val blength_rec :
    (coq_Brs -> __ -> 'a1) -> (coq_Brs -> nat -> coq_Term -> coq_Brs -> __ ->
    'a1 -> 'a1) -> coq_Brs -> 'a1 **)

let blength_rec =
  blength_rect

(** val coq_R_blength_correct : coq_Brs -> nat -> coq_R_blength **)

let coq_R_blength_correct ts _res =
  blength_rect (fun y _ _ _ -> R_blength_0 y) (fun y y0 y1 y2 _ y4 _ _ ->
    R_blength_1 (y, y0, y1, y2, (blength y2), (y4 (blength y2) __))) ts _res
    __

(** val tappend : coq_Terms -> coq_Terms -> coq_Terms **)

let rec tappend ts1 ts2 =
  match ts1 with
  | Coq_tnil -> ts2
  | Coq_tcons (t, ts) -> Coq_tcons (t, (tappend ts ts2))

(** val tdrop : nat -> coq_Terms -> coq_Terms **)

let rec tdrop n ts =
  match n with
  | O -> ts
  | S m ->
    (match ts with
     | Coq_tnil -> Coq_tnil
     | Coq_tcons (_, us) -> tdrop m us)

(** val treverse : coq_Terms -> coq_Terms **)

let rec treverse = function
| Coq_tnil -> Coq_tnil
| Coq_tcons (b, bs) -> tappend (treverse bs) (Coq_tcons (b, Coq_tnil))

(** val dlength : coq_Defs -> nat **)

let rec dlength = function
| Coq_dnil -> O
| Coq_dcons (_, _, _, ts0) -> S (dlength ts0)

(** val isApp_dec : coq_Term -> bool **)

let isApp_dec = function
| TApp (_, _) -> true
| _ -> false

(** val lift : nat -> coq_Term -> coq_Term **)

let rec lift n t = match t with
| TRel m -> TRel (match Nat.compare m n with
                  | Lt -> m
                  | _ -> S m)
| TProof -> TProof
| TLambda (nm, bod) -> TLambda (nm, (lift (S n) bod))
| TLetIn (nm, df, bod) -> TLetIn (nm, (lift n df), (lift (S n) bod))
| TApp (fn, arg) -> TApp ((lift n fn), (lift n arg))
| TConstruct (i, x, args) -> TConstruct (i, x, (lifts n args))
| TCase (i, mch, brs) -> TCase (i, (lift n mch), (liftBs n brs))
| TFix (ds, y) -> TFix ((liftDs (add n (dlength ds)) ds), y)
| TProj (prj, bod) -> TProj (prj, (lift n bod))
| _ -> t

(** val lifts : nat -> coq_Terms -> coq_Terms **)

and lifts n = function
| Coq_tnil -> Coq_tnil
| Coq_tcons (u, us) -> Coq_tcons ((lift n u), (lifts n us))

(** val liftBs : nat -> coq_Brs -> coq_Brs **)

and liftBs n = function
| Coq_bnil -> Coq_bnil
| Coq_bcons (m, b, bs) -> Coq_bcons (m, (lift n b), (liftBs n bs))

(** val liftDs : nat -> coq_Defs -> coq_Defs **)

and liftDs n = function
| Coq_dnil -> Coq_dnil
| Coq_dcons (nm, u, j, es) -> Coq_dcons (nm, (lift n u), j, (liftDs n es))

type coq_R_lift =
| R_lift_0 of nat * coq_Term * nat
| R_lift_1 of nat * coq_Term * nat * comparison
| R_lift_2 of nat * coq_Term
| R_lift_3 of nat * coq_Term * name * coq_Term * coq_Term * coq_R_lift
| R_lift_4 of nat * coq_Term * name * coq_Term * coq_Term * coq_Term
   * coq_R_lift * coq_Term * coq_R_lift
| R_lift_5 of nat * coq_Term * coq_Term * coq_Term * coq_Term * coq_R_lift
   * coq_Term * coq_R_lift
| R_lift_6 of nat * coq_Term * inductive * nat * coq_Terms * coq_Terms
   * coq_R_lifts
| R_lift_7 of nat * coq_Term * inductive * coq_Term * coq_Brs * coq_Term
   * coq_R_lift * coq_Brs * coq_R_liftBs
| R_lift_8 of nat * coq_Term * coq_Defs * nat * coq_Defs * coq_R_liftDs
| R_lift_9 of nat * coq_Term * projection * coq_Term * coq_Term * coq_R_lift
| R_lift_10 of nat * coq_Term * coq_Term
and coq_R_lifts =
| R_lifts_0 of nat * coq_Terms
| R_lifts_1 of nat * coq_Terms * coq_Term * coq_Terms * coq_Term * coq_R_lift
   * coq_Terms * coq_R_lifts
and coq_R_liftBs =
| R_liftBs_0 of nat * coq_Brs
| R_liftBs_1 of nat * coq_Brs * nat * coq_Term * coq_Brs * coq_Term
   * coq_R_lift * coq_Brs * coq_R_liftBs
and coq_R_liftDs =
| R_liftDs_0 of nat * coq_Defs
| R_liftDs_1 of nat * coq_Defs * name * coq_Term * nat * coq_Defs * coq_Term
   * coq_R_lift * coq_Defs * coq_R_liftDs

(** val coq_R_lift_rect :
    (nat -> coq_Term -> nat -> __ -> __ -> 'a1) -> (nat -> coq_Term -> nat ->
    __ -> comparison -> __ -> __ -> 'a1) -> (nat -> coq_Term -> __ -> 'a1) ->
    (nat -> coq_Term -> name -> coq_Term -> __ -> coq_Term -> coq_R_lift ->
    'a1 -> 'a1) -> (nat -> coq_Term -> name -> coq_Term -> coq_Term -> __ ->
    coq_Term -> coq_R_lift -> 'a1 -> coq_Term -> coq_R_lift -> 'a1 -> 'a1) ->
    (nat -> coq_Term -> coq_Term -> coq_Term -> __ -> coq_Term -> coq_R_lift
    -> 'a1 -> coq_Term -> coq_R_lift -> 'a1 -> 'a1) -> (nat -> coq_Term ->
    inductive -> nat -> coq_Terms -> __ -> coq_Terms -> coq_R_lifts -> 'a1)
    -> (nat -> coq_Term -> inductive -> coq_Term -> coq_Brs -> __ -> coq_Term
    -> coq_R_lift -> 'a1 -> coq_Brs -> coq_R_liftBs -> 'a1) -> (nat ->
    coq_Term -> coq_Defs -> nat -> __ -> coq_Defs -> coq_R_liftDs -> 'a1) ->
    (nat -> coq_Term -> projection -> coq_Term -> __ -> coq_Term ->
    coq_R_lift -> 'a1 -> 'a1) -> (nat -> coq_Term -> coq_Term -> __ -> __ ->
    'a1) -> nat -> coq_Term -> coq_Term -> coq_R_lift -> 'a1 **)

let rec coq_R_lift_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 _ _ _ = function
| R_lift_0 (n, t, m) -> f n t m __ __
| R_lift_1 (n, t, m, _x) -> f0 n t m __ _x __ __
| R_lift_2 (n, t) -> f1 n t __
| R_lift_3 (n, t, nm, bod, _res, r0) ->
  f2 n t nm bod __ _res r0
    (coq_R_lift_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 (S n) bod _res r0)
| R_lift_4 (n, t, nm, df, bod, _res0, r0, _res, r1) ->
  f3 n t nm df bod __ _res0 r0
    (coq_R_lift_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 n df _res0 r0) _res r1
    (coq_R_lift_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 (S n) bod _res r1)
| R_lift_5 (n, t, fn, arg, _res0, r0, _res, r1) ->
  f4 n t fn arg __ _res0 r0
    (coq_R_lift_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 n fn _res0 r0) _res r1
    (coq_R_lift_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 n arg _res r1)
| R_lift_6 (n, t, i, x, args, _res, r0) -> f5 n t i x args __ _res r0
| R_lift_7 (n, t, i, mch, brs, _res0, r0, _res, r1) ->
  f6 n t i mch brs __ _res0 r0
    (coq_R_lift_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 n mch _res0 r0) _res r1
| R_lift_8 (n, t, ds, y, _res, r0) -> f7 n t ds y __ _res r0
| R_lift_9 (n, t, prj, bod, _res, r0) ->
  f8 n t prj bod __ _res r0
    (coq_R_lift_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 n bod _res r0)
| R_lift_10 (n, t, _x) -> f9 n t _x __ __

(** val coq_R_lift_rec :
    (nat -> coq_Term -> nat -> __ -> __ -> 'a1) -> (nat -> coq_Term -> nat ->
    __ -> comparison -> __ -> __ -> 'a1) -> (nat -> coq_Term -> __ -> 'a1) ->
    (nat -> coq_Term -> name -> coq_Term -> __ -> coq_Term -> coq_R_lift ->
    'a1 -> 'a1) -> (nat -> coq_Term -> name -> coq_Term -> coq_Term -> __ ->
    coq_Term -> coq_R_lift -> 'a1 -> coq_Term -> coq_R_lift -> 'a1 -> 'a1) ->
    (nat -> coq_Term -> coq_Term -> coq_Term -> __ -> coq_Term -> coq_R_lift
    -> 'a1 -> coq_Term -> coq_R_lift -> 'a1 -> 'a1) -> (nat -> coq_Term ->
    inductive -> nat -> coq_Terms -> __ -> coq_Terms -> coq_R_lifts -> 'a1)
    -> (nat -> coq_Term -> inductive -> coq_Term -> coq_Brs -> __ -> coq_Term
    -> coq_R_lift -> 'a1 -> coq_Brs -> coq_R_liftBs -> 'a1) -> (nat ->
    coq_Term -> coq_Defs -> nat -> __ -> coq_Defs -> coq_R_liftDs -> 'a1) ->
    (nat -> coq_Term -> projection -> coq_Term -> __ -> coq_Term ->
    coq_R_lift -> 'a1 -> 'a1) -> (nat -> coq_Term -> coq_Term -> __ -> __ ->
    'a1) -> nat -> coq_Term -> coq_Term -> coq_R_lift -> 'a1 **)

let rec coq_R_lift_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 _ _ _ = function
| R_lift_0 (n, t, m) -> f n t m __ __
| R_lift_1 (n, t, m, _x) -> f0 n t m __ _x __ __
| R_lift_2 (n, t) -> f1 n t __
| R_lift_3 (n, t, nm, bod, _res, r0) ->
  f2 n t nm bod __ _res r0
    (coq_R_lift_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 (S n) bod _res r0)
| R_lift_4 (n, t, nm, df, bod, _res0, r0, _res, r1) ->
  f3 n t nm df bod __ _res0 r0
    (coq_R_lift_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 n df _res0 r0) _res r1
    (coq_R_lift_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 (S n) bod _res r1)
| R_lift_5 (n, t, fn, arg, _res0, r0, _res, r1) ->
  f4 n t fn arg __ _res0 r0
    (coq_R_lift_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 n fn _res0 r0) _res r1
    (coq_R_lift_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 n arg _res r1)
| R_lift_6 (n, t, i, x, args, _res, r0) -> f5 n t i x args __ _res r0
| R_lift_7 (n, t, i, mch, brs, _res0, r0, _res, r1) ->
  f6 n t i mch brs __ _res0 r0
    (coq_R_lift_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 n mch _res0 r0) _res r1
| R_lift_8 (n, t, ds, y, _res, r0) -> f7 n t ds y __ _res r0
| R_lift_9 (n, t, prj, bod, _res, r0) ->
  f8 n t prj bod __ _res r0
    (coq_R_lift_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 n bod _res r0)
| R_lift_10 (n, t, _x) -> f9 n t _x __ __

(** val coq_R_lifts_rect :
    (nat -> coq_Terms -> __ -> 'a1) -> (nat -> coq_Terms -> coq_Term ->
    coq_Terms -> __ -> coq_Term -> coq_R_lift -> coq_Terms -> coq_R_lifts ->
    'a1 -> 'a1) -> nat -> coq_Terms -> coq_Terms -> coq_R_lifts -> 'a1 **)

let rec coq_R_lifts_rect f f0 _ _ _ = function
| R_lifts_0 (n, ts) -> f n ts __
| R_lifts_1 (n, ts, u, us, _res0, r0, _res, r1) ->
  f0 n ts u us __ _res0 r0 _res r1 (coq_R_lifts_rect f f0 n us _res r1)

(** val coq_R_lifts_rec :
    (nat -> coq_Terms -> __ -> 'a1) -> (nat -> coq_Terms -> coq_Term ->
    coq_Terms -> __ -> coq_Term -> coq_R_lift -> coq_Terms -> coq_R_lifts ->
    'a1 -> 'a1) -> nat -> coq_Terms -> coq_Terms -> coq_R_lifts -> 'a1 **)

let rec coq_R_lifts_rec f f0 _ _ _ = function
| R_lifts_0 (n, ts) -> f n ts __
| R_lifts_1 (n, ts, u, us, _res0, r0, _res, r1) ->
  f0 n ts u us __ _res0 r0 _res r1 (coq_R_lifts_rec f f0 n us _res r1)

(** val coq_R_liftBs_rect :
    (nat -> coq_Brs -> __ -> 'a1) -> (nat -> coq_Brs -> nat -> coq_Term ->
    coq_Brs -> __ -> coq_Term -> coq_R_lift -> coq_Brs -> coq_R_liftBs -> 'a1
    -> 'a1) -> nat -> coq_Brs -> coq_Brs -> coq_R_liftBs -> 'a1 **)

let rec coq_R_liftBs_rect f f0 _ _ _ = function
| R_liftBs_0 (n, ts) -> f n ts __
| R_liftBs_1 (n, ts, m, b, bs, _res0, r0, _res, r1) ->
  f0 n ts m b bs __ _res0 r0 _res r1 (coq_R_liftBs_rect f f0 n bs _res r1)

(** val coq_R_liftBs_rec :
    (nat -> coq_Brs -> __ -> 'a1) -> (nat -> coq_Brs -> nat -> coq_Term ->
    coq_Brs -> __ -> coq_Term -> coq_R_lift -> coq_Brs -> coq_R_liftBs -> 'a1
    -> 'a1) -> nat -> coq_Brs -> coq_Brs -> coq_R_liftBs -> 'a1 **)

let rec coq_R_liftBs_rec f f0 _ _ _ = function
| R_liftBs_0 (n, ts) -> f n ts __
| R_liftBs_1 (n, ts, m, b, bs, _res0, r0, _res, r1) ->
  f0 n ts m b bs __ _res0 r0 _res r1 (coq_R_liftBs_rec f f0 n bs _res r1)

(** val coq_R_liftDs_rect :
    (nat -> coq_Defs -> __ -> 'a1) -> (nat -> coq_Defs -> name -> coq_Term ->
    nat -> coq_Defs -> __ -> coq_Term -> coq_R_lift -> coq_Defs ->
    coq_R_liftDs -> 'a1 -> 'a1) -> nat -> coq_Defs -> coq_Defs ->
    coq_R_liftDs -> 'a1 **)

let rec coq_R_liftDs_rect f f0 _ _ _ = function
| R_liftDs_0 (n, ds) -> f n ds __
| R_liftDs_1 (n, ds, nm, u, j, es, _res0, r0, _res, r1) ->
  f0 n ds nm u j es __ _res0 r0 _res r1 (coq_R_liftDs_rect f f0 n es _res r1)

(** val coq_R_liftDs_rec :
    (nat -> coq_Defs -> __ -> 'a1) -> (nat -> coq_Defs -> name -> coq_Term ->
    nat -> coq_Defs -> __ -> coq_Term -> coq_R_lift -> coq_Defs ->
    coq_R_liftDs -> 'a1 -> 'a1) -> nat -> coq_Defs -> coq_Defs ->
    coq_R_liftDs -> 'a1 **)

let rec coq_R_liftDs_rec f f0 _ _ _ = function
| R_liftDs_0 (n, ds) -> f n ds __
| R_liftDs_1 (n, ds, nm, u, j, es, _res0, r0, _res, r1) ->
  f0 n ds nm u j es __ _res0 r0 _res r1 (coq_R_liftDs_rec f f0 n es _res r1)

(** val lift_rect :
    (nat -> coq_Term -> nat -> __ -> __ -> 'a1) -> (nat -> coq_Term -> nat ->
    __ -> comparison -> __ -> __ -> 'a1) -> (nat -> coq_Term -> __ -> 'a1) ->
    (nat -> coq_Term -> name -> coq_Term -> __ -> 'a1 -> 'a1) -> (nat ->
    coq_Term -> name -> coq_Term -> coq_Term -> __ -> 'a1 -> 'a1 -> 'a1) ->
    (nat -> coq_Term -> coq_Term -> coq_Term -> __ -> 'a1 -> 'a1 -> 'a1) ->
    (nat -> coq_Term -> inductive -> nat -> coq_Terms -> __ -> 'a1) -> (nat
    -> coq_Term -> inductive -> coq_Term -> coq_Brs -> __ -> 'a1 -> 'a1) ->
    (nat -> coq_Term -> coq_Defs -> nat -> __ -> 'a1) -> (nat -> coq_Term ->
    projection -> coq_Term -> __ -> 'a1 -> 'a1) -> (nat -> coq_Term ->
    coq_Term -> __ -> __ -> 'a1) -> nat -> coq_Term -> 'a1 **)

let rec lift_rect f9 f8 f7 f6 f5 f4 f3 f2 f1 f0 f n t =
  let f10 = f9 n t in
  let f11 = f8 n t in
  let f12 = f7 n t in
  let f13 = f6 n t in
  let f14 = f5 n t in
  let f15 = f4 n t in
  let f16 = f3 n t in
  let f17 = f2 n t in
  let f18 = f1 n t in
  let f19 = f0 n t in
  let f20 = f n t in
  let f21 = f20 t __ in
  (match t with
   | TRel n0 ->
     let f22 = f10 n0 __ in
     let f23 = f11 n0 __ in
     let f24 = let _x = Nat.compare n0 n in f23 _x __ in
     (match Nat.compare n0 n with
      | Lt -> f22 __
      | _ -> f24 __)
   | TProof -> f12 __
   | TLambda (n0, t0) ->
     let f22 = f13 n0 t0 __ in
     let hrec = lift_rect f9 f8 f7 f6 f5 f4 f3 f2 f1 f0 f (S n) t0 in f22 hrec
   | TLetIn (n0, t0, t1) ->
     let f22 = f14 n0 t0 t1 __ in
     let f23 =
       let hrec = lift_rect f9 f8 f7 f6 f5 f4 f3 f2 f1 f0 f n t0 in f22 hrec
     in
     let hrec = lift_rect f9 f8 f7 f6 f5 f4 f3 f2 f1 f0 f (S n) t1 in f23 hrec
   | TApp (t0, t1) ->
     let f22 = f15 t0 t1 __ in
     let f23 =
       let hrec = lift_rect f9 f8 f7 f6 f5 f4 f3 f2 f1 f0 f n t0 in f22 hrec
     in
     let hrec = lift_rect f9 f8 f7 f6 f5 f4 f3 f2 f1 f0 f n t1 in f23 hrec
   | TConstruct (i, n0, t0) -> f16 i n0 t0 __
   | TCase (i, t0, b) ->
     let f22 = f17 i t0 b __ in
     let hrec = lift_rect f9 f8 f7 f6 f5 f4 f3 f2 f1 f0 f n t0 in f22 hrec
   | TFix (d, n0) -> f18 d n0 __
   | TProj (p, t0) ->
     let f22 = f19 p t0 __ in
     let hrec = lift_rect f9 f8 f7 f6 f5 f4 f3 f2 f1 f0 f n t0 in f22 hrec
   | _ -> f21 __)

(** val lift_rec :
    (nat -> coq_Term -> nat -> __ -> __ -> 'a1) -> (nat -> coq_Term -> nat ->
    __ -> comparison -> __ -> __ -> 'a1) -> (nat -> coq_Term -> __ -> 'a1) ->
    (nat -> coq_Term -> name -> coq_Term -> __ -> 'a1 -> 'a1) -> (nat ->
    coq_Term -> name -> coq_Term -> coq_Term -> __ -> 'a1 -> 'a1 -> 'a1) ->
    (nat -> coq_Term -> coq_Term -> coq_Term -> __ -> 'a1 -> 'a1 -> 'a1) ->
    (nat -> coq_Term -> inductive -> nat -> coq_Terms -> __ -> 'a1) -> (nat
    -> coq_Term -> inductive -> coq_Term -> coq_Brs -> __ -> 'a1 -> 'a1) ->
    (nat -> coq_Term -> coq_Defs -> nat -> __ -> 'a1) -> (nat -> coq_Term ->
    projection -> coq_Term -> __ -> 'a1 -> 'a1) -> (nat -> coq_Term ->
    coq_Term -> __ -> __ -> 'a1) -> nat -> coq_Term -> 'a1 **)

let lift_rec =
  lift_rect

(** val lifts_rect :
    (nat -> coq_Terms -> __ -> 'a1) -> (nat -> coq_Terms -> coq_Term ->
    coq_Terms -> __ -> 'a1 -> 'a1) -> nat -> coq_Terms -> 'a1 **)

let rec lifts_rect f0 f n ts =
  let f1 = f0 n ts in
  let f2 = f n ts in
  (match ts with
   | Coq_tnil -> f1 __
   | Coq_tcons (t, t0) ->
     let f3 = f2 t t0 __ in let hrec = lifts_rect f0 f n t0 in f3 hrec)

(** val lifts_rec :
    (nat -> coq_Terms -> __ -> 'a1) -> (nat -> coq_Terms -> coq_Term ->
    coq_Terms -> __ -> 'a1 -> 'a1) -> nat -> coq_Terms -> 'a1 **)

let lifts_rec =
  lifts_rect

(** val liftBs_rect :
    (nat -> coq_Brs -> __ -> 'a1) -> (nat -> coq_Brs -> nat -> coq_Term ->
    coq_Brs -> __ -> 'a1 -> 'a1) -> nat -> coq_Brs -> 'a1 **)

let rec liftBs_rect f0 f n ts =
  let f1 = f0 n ts in
  let f2 = f n ts in
  (match ts with
   | Coq_bnil -> f1 __
   | Coq_bcons (n0, t, b) ->
     let f3 = f2 n0 t b __ in let hrec = liftBs_rect f0 f n b in f3 hrec)

(** val liftBs_rec :
    (nat -> coq_Brs -> __ -> 'a1) -> (nat -> coq_Brs -> nat -> coq_Term ->
    coq_Brs -> __ -> 'a1 -> 'a1) -> nat -> coq_Brs -> 'a1 **)

let liftBs_rec =
  liftBs_rect

(** val liftDs_rect :
    (nat -> coq_Defs -> __ -> 'a1) -> (nat -> coq_Defs -> name -> coq_Term ->
    nat -> coq_Defs -> __ -> 'a1 -> 'a1) -> nat -> coq_Defs -> 'a1 **)

let rec liftDs_rect f0 f n ds =
  let f1 = f0 n ds in
  let f2 = f n ds in
  (match ds with
   | Coq_dnil -> f1 __
   | Coq_dcons (n0, t, n1, d) ->
     let f3 = f2 n0 t n1 d __ in let hrec = liftDs_rect f0 f n d in f3 hrec)

(** val liftDs_rec :
    (nat -> coq_Defs -> __ -> 'a1) -> (nat -> coq_Defs -> name -> coq_Term ->
    nat -> coq_Defs -> __ -> 'a1 -> 'a1) -> nat -> coq_Defs -> 'a1 **)

let liftDs_rec =
  liftDs_rect

(** val coq_R_lift_correct : nat -> coq_Term -> coq_Term -> coq_R_lift **)

let coq_R_lift_correct n t _res =
  let f15 = fun y y0 y1 _ -> R_lift_0 (y, y0, y1) in
  let f14 = fun y y0 y1 y3 _ -> R_lift_1 (y, y0, y1, y3) in
  let f13 = fun y y0 _ -> R_lift_2 (y, y0) in
  let f12 = fun y y0 y1 y2 y4 _ -> R_lift_3 (y, y0, y1, y2, (lift (S y) y2),
    (y4 (lift (S y) y2) __))
  in
  let f11 = fun y y0 y1 y2 y3 y5 y6 _ -> R_lift_4 (y, y0, y1, y2, y3,
    (lift y y2), (y5 (lift y y2) __), (lift (S y) y3),
    (y6 (lift (S y) y3) __))
  in
  let f10 = fun y y0 y1 y2 y4 y5 _ -> R_lift_5 (y, y0, y1, y2, (lift y y1),
    (y4 (lift y y1) __), (lift y y2), (y5 (lift y y2) __))
  in
  let f9 = fun y y0 y1 y2 y3 y5 _ -> R_lift_6 (y, y0, y1, y2, y3,
    (lifts y y3), (y5 (lifts y y3) __))
  in
  let f8 = fun y y0 y1 y2 y3 y5 y6 _ -> R_lift_7 (y, y0, y1, y2, y3,
    (lift y y2), (y5 (lift y y2) __), (liftBs y y3), (y6 (liftBs y y3) __))
  in
  let f7 = fun y y0 y1 y2 y4 _ -> R_lift_8 (y, y0, y1, y2,
    (liftDs (add y (dlength y1)) y1),
    (y4 (liftDs (add y (dlength y1)) y1) __))
  in
  let f6 = fun y y0 y1 y2 y4 _ -> R_lift_9 (y, y0, y1, y2, (lift y y2),
    (y4 (lift y y2) __))
  in
  let f5 = fun y y0 y1 _ -> R_lift_10 (y, y0, y1) in
  let f4 = fun y y0 _ -> R_lifts_0 (y, y0) in
  let f3 = fun y y0 y1 y2 y4 y5 _ -> R_lifts_1 (y, y0, y1, y2, (lift y y1),
    (y4 (lift y y1) __), (lifts y y2), (y5 (lifts y y2) __))
  in
  let f2 = fun y y0 _ -> R_liftBs_0 (y, y0) in
  let f1 = fun y y0 y1 y2 y3 y5 y6 _ -> R_liftBs_1 (y, y0, y1, y2, y3,
    (lift y y2), (y5 (lift y y2) __), (liftBs y y3), (y6 (liftBs y y3) __))
  in
  let f0 = fun y y0 _ -> R_liftDs_0 (y, y0) in
  let f = fun y y0 y1 y2 y3 y4 y6 y7 _ -> R_liftDs_1 (y, y0, y1, y2, y3, y4,
    (lift y y2), (y6 (lift y y2) __), (liftDs y y4), (y7 (liftDs y y4) __))
  in
  let rec lift0 n0 t0 =
    let f16 = fun y1 z -> f15 n0 t0 y1 z in
    let f17 = fun y1 y3 z -> f14 n0 t0 y1 y3 z in
    let f18 = fun z -> f13 n0 t0 z in
    let f19 = fun y1 y2 y4 z -> f12 n0 t0 y1 y2 y4 z in
    let f20 = fun y1 y2 y3 y5 y6 z -> f11 n0 t0 y1 y2 y3 y5 y6 z in
    let f21 = fun y1 y2 y4 y5 z -> f10 n0 t0 y1 y2 y4 y5 z in
    let f22 = fun y1 y2 y3 y5 z -> f9 n0 t0 y1 y2 y3 y5 z in
    let f23 = fun y1 y2 y3 y5 y6 z -> f8 n0 t0 y1 y2 y3 y5 y6 z in
    let f24 = fun y1 y2 y4 z -> f7 n0 t0 y1 y2 y4 z in
    let f25 = fun y1 y2 y4 z -> f6 n0 t0 y1 y2 y4 z in
    let f26 = fun y1 z -> f5 n0 t0 y1 z in
    let f27 = fun z -> f26 t0 z in
    (match t0 with
     | TRel n1 ->
       let f28 = fun z -> f16 n1 z in
       let f29 = fun y3 z -> f17 n1 y3 z in
       let f30 = let _x = Nat.compare n1 n0 in (fun _ z _ -> f29 _x z) in
       (match Nat.compare n1 n0 with
        | Lt -> (fun z _ -> f28 z)
        | _ -> f30 __)
     | TProof -> (fun z _ -> f18 z)
     | TLambda (n1, t1) ->
       let f28 = fun y4 z -> f19 n1 t1 y4 z in
       let hrec = lift0 (S n0) t1 in (fun z _ -> f28 hrec z)
     | TLetIn (n1, t1, t2) ->
       let f28 = fun y5 y6 z -> f20 n1 t1 t2 y5 y6 z in
       let f29 = let hrec = lift0 n0 t1 in (fun y6 z _ -> f28 hrec y6 z) in
       let hrec = lift0 (S n0) t2 in f29 hrec
     | TApp (t1, t2) ->
       let f28 = fun y4 y5 z -> f21 t1 t2 y4 y5 z in
       let f29 = let hrec = lift0 n0 t1 in (fun y5 z _ -> f28 hrec y5 z) in
       let hrec = lift0 n0 t2 in f29 hrec
     | TConstruct (i, n1, t1) ->
       let f28 = fun y5 z -> f22 i n1 t1 y5 z in
       let hrec = lifts0 n0 t1 in (fun z _ -> f28 hrec z)
     | TCase (i, t1, b) ->
       let f28 = fun y5 y6 z -> f23 i t1 b y5 y6 z in
       let f29 = let hrec = lift0 n0 t1 in (fun y6 z _ -> f28 hrec y6 z) in
       let hrec = liftBs0 n0 b in f29 hrec
     | TFix (d, n1) ->
       let f28 = fun y4 z -> f24 d n1 y4 z in
       let hrec = liftDs0 (add n0 (dlength d)) d in (fun z _ -> f28 hrec z)
     | TProj (p, t1) ->
       let f28 = fun y4 z -> f25 p t1 y4 z in
       let hrec = lift0 n0 t1 in (fun z _ -> f28 hrec z)
     | _ -> (fun z _ -> f27 z))
  and lifts0 n0 ts =
    let f16 = fun z -> f4 n0 ts z in
    let f17 = fun y1 y2 y4 y5 z -> f3 n0 ts y1 y2 y4 y5 z in
    (match ts with
     | Coq_tnil -> (fun z _ -> f16 z)
     | Coq_tcons (t0, t1) ->
       let f18 = fun y4 y5 z -> f17 t0 t1 y4 y5 z in
       let f19 = let hrec = lift0 n0 t0 in (fun y5 z _ -> f18 hrec y5 z) in
       let hrec = lifts0 n0 t1 in f19 hrec)
  and liftBs0 n0 ts =
    let f16 = fun z -> f2 n0 ts z in
    let f17 = fun y1 y2 y3 y5 y6 z -> f1 n0 ts y1 y2 y3 y5 y6 z in
    (match ts with
     | Coq_bnil -> (fun z _ -> f16 z)
     | Coq_bcons (n1, t0, b) ->
       let f18 = fun y5 y6 z -> f17 n1 t0 b y5 y6 z in
       let f19 = let hrec = lift0 n0 t0 in (fun y6 z _ -> f18 hrec y6 z) in
       let hrec = liftBs0 n0 b in f19 hrec)
  and liftDs0 n0 ds =
    let f16 = fun z -> f0 n0 ds z in
    let f17 = fun y1 y2 y3 y4 y6 y7 z -> f n0 ds y1 y2 y3 y4 y6 y7 z in
    (match ds with
     | Coq_dnil -> (fun z _ -> f16 z)
     | Coq_dcons (n1, t0, n2, d) ->
       let f18 = fun y6 y7 z -> f17 n1 t0 n2 d y6 y7 z in
       let f19 = let hrec = lift0 n0 t0 in (fun y7 z _ -> f18 hrec y7 z) in
       let hrec = liftDs0 n0 d in f19 hrec)
  in lift0 n t _res __

(** val coq_R_lifts_correct : nat -> coq_Terms -> coq_Terms -> coq_R_lifts **)

let coq_R_lifts_correct n ts _res =
  let f15 = fun y y0 y1 _ -> R_lift_0 (y, y0, y1) in
  let f14 = fun y y0 y1 y3 _ -> R_lift_1 (y, y0, y1, y3) in
  let f13 = fun y y0 _ -> R_lift_2 (y, y0) in
  let f12 = fun y y0 y1 y2 y4 _ -> R_lift_3 (y, y0, y1, y2, (lift (S y) y2),
    (y4 (lift (S y) y2) __))
  in
  let f11 = fun y y0 y1 y2 y3 y5 y6 _ -> R_lift_4 (y, y0, y1, y2, y3,
    (lift y y2), (y5 (lift y y2) __), (lift (S y) y3),
    (y6 (lift (S y) y3) __))
  in
  let f10 = fun y y0 y1 y2 y4 y5 _ -> R_lift_5 (y, y0, y1, y2, (lift y y1),
    (y4 (lift y y1) __), (lift y y2), (y5 (lift y y2) __))
  in
  let f9 = fun y y0 y1 y2 y3 y5 _ -> R_lift_6 (y, y0, y1, y2, y3,
    (lifts y y3), (y5 (lifts y y3) __))
  in
  let f8 = fun y y0 y1 y2 y3 y5 y6 _ -> R_lift_7 (y, y0, y1, y2, y3,
    (lift y y2), (y5 (lift y y2) __), (liftBs y y3), (y6 (liftBs y y3) __))
  in
  let f7 = fun y y0 y1 y2 y4 _ -> R_lift_8 (y, y0, y1, y2,
    (liftDs (add y (dlength y1)) y1),
    (y4 (liftDs (add y (dlength y1)) y1) __))
  in
  let f6 = fun y y0 y1 y2 y4 _ -> R_lift_9 (y, y0, y1, y2, (lift y y2),
    (y4 (lift y y2) __))
  in
  let f5 = fun y y0 y1 _ -> R_lift_10 (y, y0, y1) in
  let f4 = fun y y0 _ -> R_lifts_0 (y, y0) in
  let f3 = fun y y0 y1 y2 y4 y5 _ -> R_lifts_1 (y, y0, y1, y2, (lift y y1),
    (y4 (lift y y1) __), (lifts y y2), (y5 (lifts y y2) __))
  in
  let f2 = fun y y0 _ -> R_liftBs_0 (y, y0) in
  let f1 = fun y y0 y1 y2 y3 y5 y6 _ -> R_liftBs_1 (y, y0, y1, y2, y3,
    (lift y y2), (y5 (lift y y2) __), (liftBs y y3), (y6 (liftBs y y3) __))
  in
  let f0 = fun y y0 _ -> R_liftDs_0 (y, y0) in
  let f = fun y y0 y1 y2 y3 y4 y6 y7 _ -> R_liftDs_1 (y, y0, y1, y2, y3, y4,
    (lift y y2), (y6 (lift y y2) __), (liftDs y y4), (y7 (liftDs y y4) __))
  in
  let rec lift0 n0 t =
    let f16 = fun y1 z -> f15 n0 t y1 z in
    let f17 = fun y1 y3 z -> f14 n0 t y1 y3 z in
    let f18 = fun z -> f13 n0 t z in
    let f19 = fun y1 y2 y4 z -> f12 n0 t y1 y2 y4 z in
    let f20 = fun y1 y2 y3 y5 y6 z -> f11 n0 t y1 y2 y3 y5 y6 z in
    let f21 = fun y1 y2 y4 y5 z -> f10 n0 t y1 y2 y4 y5 z in
    let f22 = fun y1 y2 y3 y5 z -> f9 n0 t y1 y2 y3 y5 z in
    let f23 = fun y1 y2 y3 y5 y6 z -> f8 n0 t y1 y2 y3 y5 y6 z in
    let f24 = fun y1 y2 y4 z -> f7 n0 t y1 y2 y4 z in
    let f25 = fun y1 y2 y4 z -> f6 n0 t y1 y2 y4 z in
    let f26 = fun y1 z -> f5 n0 t y1 z in
    let f27 = fun z -> f26 t z in
    (match t with
     | TRel n1 ->
       let f28 = fun z -> f16 n1 z in
       let f29 = fun y3 z -> f17 n1 y3 z in
       let f30 = let _x = Nat.compare n1 n0 in (fun _ z _ -> f29 _x z) in
       (match Nat.compare n1 n0 with
        | Lt -> (fun z _ -> f28 z)
        | _ -> f30 __)
     | TProof -> (fun z _ -> f18 z)
     | TLambda (n1, t0) ->
       let f28 = fun y4 z -> f19 n1 t0 y4 z in
       let hrec = lift0 (S n0) t0 in (fun z _ -> f28 hrec z)
     | TLetIn (n1, t0, t1) ->
       let f28 = fun y5 y6 z -> f20 n1 t0 t1 y5 y6 z in
       let f29 = let hrec = lift0 n0 t0 in (fun y6 z _ -> f28 hrec y6 z) in
       let hrec = lift0 (S n0) t1 in f29 hrec
     | TApp (t0, t1) ->
       let f28 = fun y4 y5 z -> f21 t0 t1 y4 y5 z in
       let f29 = let hrec = lift0 n0 t0 in (fun y5 z _ -> f28 hrec y5 z) in
       let hrec = lift0 n0 t1 in f29 hrec
     | TConstruct (i, n1, t0) ->
       let f28 = fun y5 z -> f22 i n1 t0 y5 z in
       let hrec = lifts0 n0 t0 in (fun z _ -> f28 hrec z)
     | TCase (i, t0, b) ->
       let f28 = fun y5 y6 z -> f23 i t0 b y5 y6 z in
       let f29 = let hrec = lift0 n0 t0 in (fun y6 z _ -> f28 hrec y6 z) in
       let hrec = liftBs0 n0 b in f29 hrec
     | TFix (d, n1) ->
       let f28 = fun y4 z -> f24 d n1 y4 z in
       let hrec = liftDs0 (add n0 (dlength d)) d in (fun z _ -> f28 hrec z)
     | TProj (p, t0) ->
       let f28 = fun y4 z -> f25 p t0 y4 z in
       let hrec = lift0 n0 t0 in (fun z _ -> f28 hrec z)
     | _ -> (fun z _ -> f27 z))
  and lifts0 n0 ts0 =
    let f16 = fun z -> f4 n0 ts0 z in
    let f17 = fun y1 y2 y4 y5 z -> f3 n0 ts0 y1 y2 y4 y5 z in
    (match ts0 with
     | Coq_tnil -> (fun z _ -> f16 z)
     | Coq_tcons (t, t0) ->
       let f18 = fun y4 y5 z -> f17 t t0 y4 y5 z in
       let f19 = let hrec = lift0 n0 t in (fun y5 z _ -> f18 hrec y5 z) in
       let hrec = lifts0 n0 t0 in f19 hrec)
  and liftBs0 n0 ts0 =
    let f16 = fun z -> f2 n0 ts0 z in
    let f17 = fun y1 y2 y3 y5 y6 z -> f1 n0 ts0 y1 y2 y3 y5 y6 z in
    (match ts0 with
     | Coq_bnil -> (fun z _ -> f16 z)
     | Coq_bcons (n1, t, b) ->
       let f18 = fun y5 y6 z -> f17 n1 t b y5 y6 z in
       let f19 = let hrec = lift0 n0 t in (fun y6 z _ -> f18 hrec y6 z) in
       let hrec = liftBs0 n0 b in f19 hrec)
  and liftDs0 n0 ds =
    let f16 = fun z -> f0 n0 ds z in
    let f17 = fun y1 y2 y3 y4 y6 y7 z -> f n0 ds y1 y2 y3 y4 y6 y7 z in
    (match ds with
     | Coq_dnil -> (fun z _ -> f16 z)
     | Coq_dcons (n1, t, n2, d) ->
       let f18 = fun y6 y7 z -> f17 n1 t n2 d y6 y7 z in
       let f19 = let hrec = lift0 n0 t in (fun y7 z _ -> f18 hrec y7 z) in
       let hrec = liftDs0 n0 d in f19 hrec)
  in lifts0 n ts _res __

(** val coq_R_liftBs_correct : nat -> coq_Brs -> coq_Brs -> coq_R_liftBs **)

let coq_R_liftBs_correct n ts _res =
  let f15 = fun y y0 y1 _ -> R_lift_0 (y, y0, y1) in
  let f14 = fun y y0 y1 y3 _ -> R_lift_1 (y, y0, y1, y3) in
  let f13 = fun y y0 _ -> R_lift_2 (y, y0) in
  let f12 = fun y y0 y1 y2 y4 _ -> R_lift_3 (y, y0, y1, y2, (lift (S y) y2),
    (y4 (lift (S y) y2) __))
  in
  let f11 = fun y y0 y1 y2 y3 y5 y6 _ -> R_lift_4 (y, y0, y1, y2, y3,
    (lift y y2), (y5 (lift y y2) __), (lift (S y) y3),
    (y6 (lift (S y) y3) __))
  in
  let f10 = fun y y0 y1 y2 y4 y5 _ -> R_lift_5 (y, y0, y1, y2, (lift y y1),
    (y4 (lift y y1) __), (lift y y2), (y5 (lift y y2) __))
  in
  let f9 = fun y y0 y1 y2 y3 y5 _ -> R_lift_6 (y, y0, y1, y2, y3,
    (lifts y y3), (y5 (lifts y y3) __))
  in
  let f8 = fun y y0 y1 y2 y3 y5 y6 _ -> R_lift_7 (y, y0, y1, y2, y3,
    (lift y y2), (y5 (lift y y2) __), (liftBs y y3), (y6 (liftBs y y3) __))
  in
  let f7 = fun y y0 y1 y2 y4 _ -> R_lift_8 (y, y0, y1, y2,
    (liftDs (add y (dlength y1)) y1),
    (y4 (liftDs (add y (dlength y1)) y1) __))
  in
  let f6 = fun y y0 y1 y2 y4 _ -> R_lift_9 (y, y0, y1, y2, (lift y y2),
    (y4 (lift y y2) __))
  in
  let f5 = fun y y0 y1 _ -> R_lift_10 (y, y0, y1) in
  let f4 = fun y y0 _ -> R_lifts_0 (y, y0) in
  let f3 = fun y y0 y1 y2 y4 y5 _ -> R_lifts_1 (y, y0, y1, y2, (lift y y1),
    (y4 (lift y y1) __), (lifts y y2), (y5 (lifts y y2) __))
  in
  let f2 = fun y y0 _ -> R_liftBs_0 (y, y0) in
  let f1 = fun y y0 y1 y2 y3 y5 y6 _ -> R_liftBs_1 (y, y0, y1, y2, y3,
    (lift y y2), (y5 (lift y y2) __), (liftBs y y3), (y6 (liftBs y y3) __))
  in
  let f0 = fun y y0 _ -> R_liftDs_0 (y, y0) in
  let f = fun y y0 y1 y2 y3 y4 y6 y7 _ -> R_liftDs_1 (y, y0, y1, y2, y3, y4,
    (lift y y2), (y6 (lift y y2) __), (liftDs y y4), (y7 (liftDs y y4) __))
  in
  let rec lift0 n0 t =
    let f16 = fun y1 z -> f15 n0 t y1 z in
    let f17 = fun y1 y3 z -> f14 n0 t y1 y3 z in
    let f18 = fun z -> f13 n0 t z in
    let f19 = fun y1 y2 y4 z -> f12 n0 t y1 y2 y4 z in
    let f20 = fun y1 y2 y3 y5 y6 z -> f11 n0 t y1 y2 y3 y5 y6 z in
    let f21 = fun y1 y2 y4 y5 z -> f10 n0 t y1 y2 y4 y5 z in
    let f22 = fun y1 y2 y3 y5 z -> f9 n0 t y1 y2 y3 y5 z in
    let f23 = fun y1 y2 y3 y5 y6 z -> f8 n0 t y1 y2 y3 y5 y6 z in
    let f24 = fun y1 y2 y4 z -> f7 n0 t y1 y2 y4 z in
    let f25 = fun y1 y2 y4 z -> f6 n0 t y1 y2 y4 z in
    let f26 = fun y1 z -> f5 n0 t y1 z in
    let f27 = fun z -> f26 t z in
    (match t with
     | TRel n1 ->
       let f28 = fun z -> f16 n1 z in
       let f29 = fun y3 z -> f17 n1 y3 z in
       let f30 = let _x = Nat.compare n1 n0 in (fun _ z _ -> f29 _x z) in
       (match Nat.compare n1 n0 with
        | Lt -> (fun z _ -> f28 z)
        | _ -> f30 __)
     | TProof -> (fun z _ -> f18 z)
     | TLambda (n1, t0) ->
       let f28 = fun y4 z -> f19 n1 t0 y4 z in
       let hrec = lift0 (S n0) t0 in (fun z _ -> f28 hrec z)
     | TLetIn (n1, t0, t1) ->
       let f28 = fun y5 y6 z -> f20 n1 t0 t1 y5 y6 z in
       let f29 = let hrec = lift0 n0 t0 in (fun y6 z _ -> f28 hrec y6 z) in
       let hrec = lift0 (S n0) t1 in f29 hrec
     | TApp (t0, t1) ->
       let f28 = fun y4 y5 z -> f21 t0 t1 y4 y5 z in
       let f29 = let hrec = lift0 n0 t0 in (fun y5 z _ -> f28 hrec y5 z) in
       let hrec = lift0 n0 t1 in f29 hrec
     | TConstruct (i, n1, t0) ->
       let f28 = fun y5 z -> f22 i n1 t0 y5 z in
       let hrec = lifts0 n0 t0 in (fun z _ -> f28 hrec z)
     | TCase (i, t0, b) ->
       let f28 = fun y5 y6 z -> f23 i t0 b y5 y6 z in
       let f29 = let hrec = lift0 n0 t0 in (fun y6 z _ -> f28 hrec y6 z) in
       let hrec = liftBs0 n0 b in f29 hrec
     | TFix (d, n1) ->
       let f28 = fun y4 z -> f24 d n1 y4 z in
       let hrec = liftDs0 (add n0 (dlength d)) d in (fun z _ -> f28 hrec z)
     | TProj (p, t0) ->
       let f28 = fun y4 z -> f25 p t0 y4 z in
       let hrec = lift0 n0 t0 in (fun z _ -> f28 hrec z)
     | _ -> (fun z _ -> f27 z))
  and lifts0 n0 ts0 =
    let f16 = fun z -> f4 n0 ts0 z in
    let f17 = fun y1 y2 y4 y5 z -> f3 n0 ts0 y1 y2 y4 y5 z in
    (match ts0 with
     | Coq_tnil -> (fun z _ -> f16 z)
     | Coq_tcons (t, t0) ->
       let f18 = fun y4 y5 z -> f17 t t0 y4 y5 z in
       let f19 = let hrec = lift0 n0 t in (fun y5 z _ -> f18 hrec y5 z) in
       let hrec = lifts0 n0 t0 in f19 hrec)
  and liftBs0 n0 ts0 =
    let f16 = fun z -> f2 n0 ts0 z in
    let f17 = fun y1 y2 y3 y5 y6 z -> f1 n0 ts0 y1 y2 y3 y5 y6 z in
    (match ts0 with
     | Coq_bnil -> (fun z _ -> f16 z)
     | Coq_bcons (n1, t, b) ->
       let f18 = fun y5 y6 z -> f17 n1 t b y5 y6 z in
       let f19 = let hrec = lift0 n0 t in (fun y6 z _ -> f18 hrec y6 z) in
       let hrec = liftBs0 n0 b in f19 hrec)
  and liftDs0 n0 ds =
    let f16 = fun z -> f0 n0 ds z in
    let f17 = fun y1 y2 y3 y4 y6 y7 z -> f n0 ds y1 y2 y3 y4 y6 y7 z in
    (match ds with
     | Coq_dnil -> (fun z _ -> f16 z)
     | Coq_dcons (n1, t, n2, d) ->
       let f18 = fun y6 y7 z -> f17 n1 t n2 d y6 y7 z in
       let f19 = let hrec = lift0 n0 t in (fun y7 z _ -> f18 hrec y7 z) in
       let hrec = liftDs0 n0 d in f19 hrec)
  in liftBs0 n ts _res __

(** val coq_R_liftDs_correct : nat -> coq_Defs -> coq_Defs -> coq_R_liftDs **)

let coq_R_liftDs_correct n ds _res =
  let f15 = fun y y0 y1 _ -> R_lift_0 (y, y0, y1) in
  let f14 = fun y y0 y1 y3 _ -> R_lift_1 (y, y0, y1, y3) in
  let f13 = fun y y0 _ -> R_lift_2 (y, y0) in
  let f12 = fun y y0 y1 y2 y4 _ -> R_lift_3 (y, y0, y1, y2, (lift (S y) y2),
    (y4 (lift (S y) y2) __))
  in
  let f11 = fun y y0 y1 y2 y3 y5 y6 _ -> R_lift_4 (y, y0, y1, y2, y3,
    (lift y y2), (y5 (lift y y2) __), (lift (S y) y3),
    (y6 (lift (S y) y3) __))
  in
  let f10 = fun y y0 y1 y2 y4 y5 _ -> R_lift_5 (y, y0, y1, y2, (lift y y1),
    (y4 (lift y y1) __), (lift y y2), (y5 (lift y y2) __))
  in
  let f9 = fun y y0 y1 y2 y3 y5 _ -> R_lift_6 (y, y0, y1, y2, y3,
    (lifts y y3), (y5 (lifts y y3) __))
  in
  let f8 = fun y y0 y1 y2 y3 y5 y6 _ -> R_lift_7 (y, y0, y1, y2, y3,
    (lift y y2), (y5 (lift y y2) __), (liftBs y y3), (y6 (liftBs y y3) __))
  in
  let f7 = fun y y0 y1 y2 y4 _ -> R_lift_8 (y, y0, y1, y2,
    (liftDs (add y (dlength y1)) y1),
    (y4 (liftDs (add y (dlength y1)) y1) __))
  in
  let f6 = fun y y0 y1 y2 y4 _ -> R_lift_9 (y, y0, y1, y2, (lift y y2),
    (y4 (lift y y2) __))
  in
  let f5 = fun y y0 y1 _ -> R_lift_10 (y, y0, y1) in
  let f4 = fun y y0 _ -> R_lifts_0 (y, y0) in
  let f3 = fun y y0 y1 y2 y4 y5 _ -> R_lifts_1 (y, y0, y1, y2, (lift y y1),
    (y4 (lift y y1) __), (lifts y y2), (y5 (lifts y y2) __))
  in
  let f2 = fun y y0 _ -> R_liftBs_0 (y, y0) in
  let f1 = fun y y0 y1 y2 y3 y5 y6 _ -> R_liftBs_1 (y, y0, y1, y2, y3,
    (lift y y2), (y5 (lift y y2) __), (liftBs y y3), (y6 (liftBs y y3) __))
  in
  let f0 = fun y y0 _ -> R_liftDs_0 (y, y0) in
  let f = fun y y0 y1 y2 y3 y4 y6 y7 _ -> R_liftDs_1 (y, y0, y1, y2, y3, y4,
    (lift y y2), (y6 (lift y y2) __), (liftDs y y4), (y7 (liftDs y y4) __))
  in
  let rec lift0 n0 t =
    let f16 = fun y1 z -> f15 n0 t y1 z in
    let f17 = fun y1 y3 z -> f14 n0 t y1 y3 z in
    let f18 = fun z -> f13 n0 t z in
    let f19 = fun y1 y2 y4 z -> f12 n0 t y1 y2 y4 z in
    let f20 = fun y1 y2 y3 y5 y6 z -> f11 n0 t y1 y2 y3 y5 y6 z in
    let f21 = fun y1 y2 y4 y5 z -> f10 n0 t y1 y2 y4 y5 z in
    let f22 = fun y1 y2 y3 y5 z -> f9 n0 t y1 y2 y3 y5 z in
    let f23 = fun y1 y2 y3 y5 y6 z -> f8 n0 t y1 y2 y3 y5 y6 z in
    let f24 = fun y1 y2 y4 z -> f7 n0 t y1 y2 y4 z in
    let f25 = fun y1 y2 y4 z -> f6 n0 t y1 y2 y4 z in
    let f26 = fun y1 z -> f5 n0 t y1 z in
    let f27 = fun z -> f26 t z in
    (match t with
     | TRel n1 ->
       let f28 = fun z -> f16 n1 z in
       let f29 = fun y3 z -> f17 n1 y3 z in
       let f30 = let _x = Nat.compare n1 n0 in (fun _ z _ -> f29 _x z) in
       (match Nat.compare n1 n0 with
        | Lt -> (fun z _ -> f28 z)
        | _ -> f30 __)
     | TProof -> (fun z _ -> f18 z)
     | TLambda (n1, t0) ->
       let f28 = fun y4 z -> f19 n1 t0 y4 z in
       let hrec = lift0 (S n0) t0 in (fun z _ -> f28 hrec z)
     | TLetIn (n1, t0, t1) ->
       let f28 = fun y5 y6 z -> f20 n1 t0 t1 y5 y6 z in
       let f29 = let hrec = lift0 n0 t0 in (fun y6 z _ -> f28 hrec y6 z) in
       let hrec = lift0 (S n0) t1 in f29 hrec
     | TApp (t0, t1) ->
       let f28 = fun y4 y5 z -> f21 t0 t1 y4 y5 z in
       let f29 = let hrec = lift0 n0 t0 in (fun y5 z _ -> f28 hrec y5 z) in
       let hrec = lift0 n0 t1 in f29 hrec
     | TConstruct (i, n1, t0) ->
       let f28 = fun y5 z -> f22 i n1 t0 y5 z in
       let hrec = lifts0 n0 t0 in (fun z _ -> f28 hrec z)
     | TCase (i, t0, b) ->
       let f28 = fun y5 y6 z -> f23 i t0 b y5 y6 z in
       let f29 = let hrec = lift0 n0 t0 in (fun y6 z _ -> f28 hrec y6 z) in
       let hrec = liftBs0 n0 b in f29 hrec
     | TFix (d, n1) ->
       let f28 = fun y4 z -> f24 d n1 y4 z in
       let hrec = liftDs0 (add n0 (dlength d)) d in (fun z _ -> f28 hrec z)
     | TProj (p, t0) ->
       let f28 = fun y4 z -> f25 p t0 y4 z in
       let hrec = lift0 n0 t0 in (fun z _ -> f28 hrec z)
     | _ -> (fun z _ -> f27 z))
  and lifts0 n0 ts =
    let f16 = fun z -> f4 n0 ts z in
    let f17 = fun y1 y2 y4 y5 z -> f3 n0 ts y1 y2 y4 y5 z in
    (match ts with
     | Coq_tnil -> (fun z _ -> f16 z)
     | Coq_tcons (t, t0) ->
       let f18 = fun y4 y5 z -> f17 t t0 y4 y5 z in
       let f19 = let hrec = lift0 n0 t in (fun y5 z _ -> f18 hrec y5 z) in
       let hrec = lifts0 n0 t0 in f19 hrec)
  and liftBs0 n0 ts =
    let f16 = fun z -> f2 n0 ts z in
    let f17 = fun y1 y2 y3 y5 y6 z -> f1 n0 ts y1 y2 y3 y5 y6 z in
    (match ts with
     | Coq_bnil -> (fun z _ -> f16 z)
     | Coq_bcons (n1, t, b) ->
       let f18 = fun y5 y6 z -> f17 n1 t b y5 y6 z in
       let f19 = let hrec = lift0 n0 t in (fun y6 z _ -> f18 hrec y6 z) in
       let hrec = liftBs0 n0 b in f19 hrec)
  and liftDs0 n0 ds0 =
    let f16 = fun z -> f0 n0 ds0 z in
    let f17 = fun y1 y2 y3 y4 y6 y7 z -> f n0 ds0 y1 y2 y3 y4 y6 y7 z in
    (match ds0 with
     | Coq_dnil -> (fun z _ -> f16 z)
     | Coq_dcons (n1, t, n2, d) ->
       let f18 = fun y6 y7 z -> f17 n1 t n2 d y6 y7 z in
       let f19 = let hrec = lift0 n0 t in (fun y7 z _ -> f18 hrec y7 z) in
       let hrec = liftDs0 n0 d in f19 hrec)
  in liftDs0 n ds _res __

(** val etaExpand_args_Lam' :
    nat -> (coq_Terms -> coq_Term) -> coq_Terms -> coq_Term **)

let rec etaExpand_args_Lam' nargs body computedArgs =
  match nargs with
  | O -> TLambda (Coq_nAnon, (body computedArgs))
  | S n ->
    etaExpand_args_Lam' n (fun b -> TLambda (Coq_nAnon, (TLambda (Coq_nAnon,
      (body b)))))
      (tappend (lifts O computedArgs) (Coq_tcons ((TRel O), Coq_tnil)))

type coq_R_etaExpand_args_Lam' =
| R_etaExpand_args_Lam'_0 of nat * (coq_Terms -> coq_Term) * coq_Terms
| R_etaExpand_args_Lam'_1 of nat * (coq_Terms -> coq_Term) * coq_Terms * 
   nat * coq_Term * coq_R_etaExpand_args_Lam'

(** val coq_R_etaExpand_args_Lam'_rect :
    (nat -> (coq_Terms -> coq_Term) -> coq_Terms -> __ -> 'a1) -> (nat ->
    (coq_Terms -> coq_Term) -> coq_Terms -> nat -> __ -> coq_Term ->
    coq_R_etaExpand_args_Lam' -> 'a1 -> 'a1) -> nat -> (coq_Terms ->
    coq_Term) -> coq_Terms -> coq_Term -> coq_R_etaExpand_args_Lam' -> 'a1 **)

let rec coq_R_etaExpand_args_Lam'_rect f f0 _ _ _ _ = function
| R_etaExpand_args_Lam'_0 (nargs, body, computedArgs) ->
  f nargs body computedArgs __
| R_etaExpand_args_Lam'_1 (nargs, body, computedArgs, n, _res, r0) ->
  f0 nargs body computedArgs n __ _res r0
    (coq_R_etaExpand_args_Lam'_rect f f0 n (fun b -> TLambda (Coq_nAnon,
      (TLambda (Coq_nAnon, (body b)))))
      (tappend (lifts O computedArgs) (Coq_tcons ((TRel O), Coq_tnil))) _res
      r0)

(** val coq_R_etaExpand_args_Lam'_rec :
    (nat -> (coq_Terms -> coq_Term) -> coq_Terms -> __ -> 'a1) -> (nat ->
    (coq_Terms -> coq_Term) -> coq_Terms -> nat -> __ -> coq_Term ->
    coq_R_etaExpand_args_Lam' -> 'a1 -> 'a1) -> nat -> (coq_Terms ->
    coq_Term) -> coq_Terms -> coq_Term -> coq_R_etaExpand_args_Lam' -> 'a1 **)

let rec coq_R_etaExpand_args_Lam'_rec f f0 _ _ _ _ = function
| R_etaExpand_args_Lam'_0 (nargs, body, computedArgs) ->
  f nargs body computedArgs __
| R_etaExpand_args_Lam'_1 (nargs, body, computedArgs, n, _res, r0) ->
  f0 nargs body computedArgs n __ _res r0
    (coq_R_etaExpand_args_Lam'_rec f f0 n (fun b -> TLambda (Coq_nAnon,
      (TLambda (Coq_nAnon, (body b)))))
      (tappend (lifts O computedArgs) (Coq_tcons ((TRel O), Coq_tnil))) _res
      r0)

(** val etaExpand_args_Lam'_rect :
    (nat -> (coq_Terms -> coq_Term) -> coq_Terms -> __ -> 'a1) -> (nat ->
    (coq_Terms -> coq_Term) -> coq_Terms -> nat -> __ -> 'a1 -> 'a1) -> nat
    -> (coq_Terms -> coq_Term) -> coq_Terms -> 'a1 **)

let rec etaExpand_args_Lam'_rect f0 f nargs body computedArgs =
  let f1 = f0 nargs body computedArgs in
  let f2 = f nargs body computedArgs in
  (match nargs with
   | O -> f1 __
   | S n ->
     let f3 = f2 n __ in
     let hrec =
       etaExpand_args_Lam'_rect f0 f n (fun b -> TLambda (Coq_nAnon, (TLambda
         (Coq_nAnon, (body b)))))
         (tappend (lifts O computedArgs) (Coq_tcons ((TRel O), Coq_tnil)))
     in
     f3 hrec)

(** val etaExpand_args_Lam'_rec :
    (nat -> (coq_Terms -> coq_Term) -> coq_Terms -> __ -> 'a1) -> (nat ->
    (coq_Terms -> coq_Term) -> coq_Terms -> nat -> __ -> 'a1 -> 'a1) -> nat
    -> (coq_Terms -> coq_Term) -> coq_Terms -> 'a1 **)

let etaExpand_args_Lam'_rec =
  etaExpand_args_Lam'_rect

(** val coq_R_etaExpand_args_Lam'_correct :
    nat -> (coq_Terms -> coq_Term) -> coq_Terms -> coq_Term ->
    coq_R_etaExpand_args_Lam' **)

let coq_R_etaExpand_args_Lam'_correct nargs body computedArgs _res =
  etaExpand_args_Lam'_rect (fun y y0 y1 _ _ _ -> R_etaExpand_args_Lam'_0 (y,
    y0, y1)) (fun y y0 y1 y2 _ y4 _ _ -> R_etaExpand_args_Lam'_1 (y, y0, y1,
    y2,
    (etaExpand_args_Lam' y2 (fun b -> TLambda (Coq_nAnon, (TLambda
      (Coq_nAnon, (y0 b)))))
      (tappend (lifts O y1) (Coq_tcons ((TRel O), Coq_tnil)))),
    (y4
      (etaExpand_args_Lam' y2 (fun b -> TLambda (Coq_nAnon, (TLambda
        (Coq_nAnon, (y0 b)))))
        (tappend (lifts O y1) (Coq_tcons ((TRel O), Coq_tnil)))) __))) nargs
    body computedArgs _res __

(** val etaExpand_args_Lam :
    nat -> coq_Terms -> (coq_Terms -> coq_Term) -> coq_Terms -> coq_Term **)

let rec etaExpand_args_Lam nargs actualArgs body computedArgs =
  match nargs with
  | O ->
    (match actualArgs with
     | Coq_tnil -> body computedArgs
     | Coq_tcons (_, _) ->
       TWrong
         ('s'::('t'::('r'::('i'::('p'::(';'::(' '::('C'::('o'::('n'::('s'::('t'::('r'::('u'::('c'::('t'::('o'::('r'::(';'::(' '::('t'::('o'::('o'::(' '::('m'::('a'::('n'::('y'::(' '::('a'::('r'::('g'::('s'::[]))))))))))))))))))))))))))))))))))
  | S n ->
    (match actualArgs with
     | Coq_tnil ->
       etaExpand_args_Lam' n body
         (tappend (lifts O computedArgs) (Coq_tcons ((TRel O), Coq_tnil)))
     | Coq_tcons (u, us) ->
       etaExpand_args_Lam n us body
         (tappend computedArgs (Coq_tcons (u, Coq_tnil))))

type coq_R_etaExpand_args_Lam =
| R_etaExpand_args_Lam_0 of nat * coq_Terms * (coq_Terms -> coq_Term)
   * coq_Terms
| R_etaExpand_args_Lam_1 of nat * coq_Terms * (coq_Terms -> coq_Term)
   * coq_Terms * coq_Term * coq_Terms
| R_etaExpand_args_Lam_2 of nat * coq_Terms * (coq_Terms -> coq_Term)
   * coq_Terms * nat
| R_etaExpand_args_Lam_3 of nat * coq_Terms * (coq_Terms -> coq_Term)
   * coq_Terms * nat * coq_Term * coq_Terms * coq_Term
   * coq_R_etaExpand_args_Lam

(** val coq_R_etaExpand_args_Lam_rect :
    (nat -> coq_Terms -> (coq_Terms -> coq_Term) -> coq_Terms -> __ -> __ ->
    'a1) -> (nat -> coq_Terms -> (coq_Terms -> coq_Term) -> coq_Terms -> __
    -> coq_Term -> coq_Terms -> __ -> 'a1) -> (nat -> coq_Terms -> (coq_Terms
    -> coq_Term) -> coq_Terms -> nat -> __ -> __ -> 'a1) -> (nat -> coq_Terms
    -> (coq_Terms -> coq_Term) -> coq_Terms -> nat -> __ -> coq_Term ->
    coq_Terms -> __ -> coq_Term -> coq_R_etaExpand_args_Lam -> 'a1 -> 'a1) ->
    nat -> coq_Terms -> (coq_Terms -> coq_Term) -> coq_Terms -> coq_Term ->
    coq_R_etaExpand_args_Lam -> 'a1 **)

let rec coq_R_etaExpand_args_Lam_rect f f0 f1 f2 _ _ _ _ _ = function
| R_etaExpand_args_Lam_0 (nargs, actualArgs, body, computedArgs) ->
  f nargs actualArgs body computedArgs __ __
| R_etaExpand_args_Lam_1 (nargs, actualArgs, body, computedArgs, _x, _x0) ->
  f0 nargs actualArgs body computedArgs __ _x _x0 __
| R_etaExpand_args_Lam_2 (nargs, actualArgs, body, computedArgs, n) ->
  f1 nargs actualArgs body computedArgs n __ __
| R_etaExpand_args_Lam_3 (nargs, actualArgs, body, computedArgs, n, u, us,
                          _res, r0) ->
  f2 nargs actualArgs body computedArgs n __ u us __ _res r0
    (coq_R_etaExpand_args_Lam_rect f f0 f1 f2 n us body
      (tappend computedArgs (Coq_tcons (u, Coq_tnil))) _res r0)

(** val coq_R_etaExpand_args_Lam_rec :
    (nat -> coq_Terms -> (coq_Terms -> coq_Term) -> coq_Terms -> __ -> __ ->
    'a1) -> (nat -> coq_Terms -> (coq_Terms -> coq_Term) -> coq_Terms -> __
    -> coq_Term -> coq_Terms -> __ -> 'a1) -> (nat -> coq_Terms -> (coq_Terms
    -> coq_Term) -> coq_Terms -> nat -> __ -> __ -> 'a1) -> (nat -> coq_Terms
    -> (coq_Terms -> coq_Term) -> coq_Terms -> nat -> __ -> coq_Term ->
    coq_Terms -> __ -> coq_Term -> coq_R_etaExpand_args_Lam -> 'a1 -> 'a1) ->
    nat -> coq_Terms -> (coq_Terms -> coq_Term) -> coq_Terms -> coq_Term ->
    coq_R_etaExpand_args_Lam -> 'a1 **)

let rec coq_R_etaExpand_args_Lam_rec f f0 f1 f2 _ _ _ _ _ = function
| R_etaExpand_args_Lam_0 (nargs, actualArgs, body, computedArgs) ->
  f nargs actualArgs body computedArgs __ __
| R_etaExpand_args_Lam_1 (nargs, actualArgs, body, computedArgs, _x, _x0) ->
  f0 nargs actualArgs body computedArgs __ _x _x0 __
| R_etaExpand_args_Lam_2 (nargs, actualArgs, body, computedArgs, n) ->
  f1 nargs actualArgs body computedArgs n __ __
| R_etaExpand_args_Lam_3 (nargs, actualArgs, body, computedArgs, n, u, us,
                          _res, r0) ->
  f2 nargs actualArgs body computedArgs n __ u us __ _res r0
    (coq_R_etaExpand_args_Lam_rec f f0 f1 f2 n us body
      (tappend computedArgs (Coq_tcons (u, Coq_tnil))) _res r0)

(** val etaExpand_args_Lam_rect :
    (nat -> coq_Terms -> (coq_Terms -> coq_Term) -> coq_Terms -> __ -> __ ->
    'a1) -> (nat -> coq_Terms -> (coq_Terms -> coq_Term) -> coq_Terms -> __
    -> coq_Term -> coq_Terms -> __ -> 'a1) -> (nat -> coq_Terms -> (coq_Terms
    -> coq_Term) -> coq_Terms -> nat -> __ -> __ -> 'a1) -> (nat -> coq_Terms
    -> (coq_Terms -> coq_Term) -> coq_Terms -> nat -> __ -> coq_Term ->
    coq_Terms -> __ -> 'a1 -> 'a1) -> nat -> coq_Terms -> (coq_Terms ->
    coq_Term) -> coq_Terms -> 'a1 **)

let rec etaExpand_args_Lam_rect f2 f1 f0 f nargs actualArgs body computedArgs =
  let f3 = f2 nargs actualArgs body computedArgs in
  let f4 = f1 nargs actualArgs body computedArgs in
  let f5 = f0 nargs actualArgs body computedArgs in
  let f6 = f nargs actualArgs body computedArgs in
  (match nargs with
   | O ->
     let f7 = f3 __ in
     let f8 = f4 __ in
     (match actualArgs with
      | Coq_tnil -> f7 __
      | Coq_tcons (t, t0) -> f8 t t0 __)
   | S n ->
     let f7 = f5 n __ in
     let f8 = f6 n __ in
     (match actualArgs with
      | Coq_tnil -> f7 __
      | Coq_tcons (t, t0) ->
        let f9 = f8 t t0 __ in
        let hrec =
          etaExpand_args_Lam_rect f2 f1 f0 f n t0 body
            (tappend computedArgs (Coq_tcons (t, Coq_tnil)))
        in
        f9 hrec))

(** val etaExpand_args_Lam_rec :
    (nat -> coq_Terms -> (coq_Terms -> coq_Term) -> coq_Terms -> __ -> __ ->
    'a1) -> (nat -> coq_Terms -> (coq_Terms -> coq_Term) -> coq_Terms -> __
    -> coq_Term -> coq_Terms -> __ -> 'a1) -> (nat -> coq_Terms -> (coq_Terms
    -> coq_Term) -> coq_Terms -> nat -> __ -> __ -> 'a1) -> (nat -> coq_Terms
    -> (coq_Terms -> coq_Term) -> coq_Terms -> nat -> __ -> coq_Term ->
    coq_Terms -> __ -> 'a1 -> 'a1) -> nat -> coq_Terms -> (coq_Terms ->
    coq_Term) -> coq_Terms -> 'a1 **)

let etaExpand_args_Lam_rec =
  etaExpand_args_Lam_rect

(** val coq_R_etaExpand_args_Lam_correct :
    nat -> coq_Terms -> (coq_Terms -> coq_Term) -> coq_Terms -> coq_Term ->
    coq_R_etaExpand_args_Lam **)

let coq_R_etaExpand_args_Lam_correct nargs actualArgs body computedArgs _res =
  etaExpand_args_Lam_rect (fun y y0 y1 y2 _ _ _ _ -> R_etaExpand_args_Lam_0
    (y, y0, y1, y2)) (fun y y0 y1 y2 _ y4 y5 _ _ _ -> R_etaExpand_args_Lam_1
    (y, y0, y1, y2, y4, y5)) (fun y y0 y1 y2 y3 _ _ _ _ ->
    R_etaExpand_args_Lam_2 (y, y0, y1, y2, y3))
    (fun y y0 y1 y2 y3 _ y5 y6 _ y8 _ _ -> R_etaExpand_args_Lam_3 (y, y0, y1,
    y2, y3, y5, y6,
    (etaExpand_args_Lam y3 y6 y1 (tappend y2 (Coq_tcons (y5, Coq_tnil)))),
    (y8 (etaExpand_args_Lam y3 y6 y1 (tappend y2 (Coq_tcons (y5, Coq_tnil))))
      __))) nargs actualArgs body computedArgs _res __

(** val etaExpand_args_Construct :
    nat -> coq_Terms -> inductive -> nat -> coq_Term **)

let etaExpand_args_Construct nargs actualArgs i m =
  match nargs with
  | O ->
    (match actualArgs with
     | Coq_tnil -> TConstruct (i, m, Coq_tnil)
     | Coq_tcons (_, _) ->
       TWrong
         ('s'::('t'::('r'::('i'::('p'::(';'::(' '::('C'::('o'::('n'::('s'::('t'::('r'::('u'::('c'::('t'::('o'::('r'::(';'::(' '::('t'::('o'::('o'::(' '::('m'::('a'::('n'::('y'::(' '::('a'::('r'::('g'::('s'::[]))))))))))))))))))))))))))))))))))
  | S n ->
    (match actualArgs with
     | Coq_tnil ->
       etaExpand_args_Lam' n (fun x -> TConstruct (i, m, x)) (Coq_tcons
         ((TRel O), Coq_tnil))
     | Coq_tcons (u, us) ->
       etaExpand_args_Lam n us (fun x -> TConstruct (i, m, x)) (Coq_tcons (u,
         Coq_tnil)))

(** val nLambda : nat -> coq_Term -> coq_Term **)

let rec nLambda n f =
  match n with
  | O -> f
  | S m -> TLambda (Coq_nAnon, (nLambda m f))

type coq_R_nLambda =
| R_nLambda_0 of nat * coq_Term
| R_nLambda_1 of nat * coq_Term * nat * coq_Term * coq_R_nLambda

(** val coq_R_nLambda_rect :
    (nat -> coq_Term -> __ -> 'a1) -> (nat -> coq_Term -> nat -> __ ->
    coq_Term -> coq_R_nLambda -> 'a1 -> 'a1) -> nat -> coq_Term -> coq_Term
    -> coq_R_nLambda -> 'a1 **)

let rec coq_R_nLambda_rect f f0 _ _ _ = function
| R_nLambda_0 (n, f1) -> f n f1 __
| R_nLambda_1 (n, f1, m, _res, r0) ->
  f0 n f1 m __ _res r0 (coq_R_nLambda_rect f f0 m f1 _res r0)

(** val coq_R_nLambda_rec :
    (nat -> coq_Term -> __ -> 'a1) -> (nat -> coq_Term -> nat -> __ ->
    coq_Term -> coq_R_nLambda -> 'a1 -> 'a1) -> nat -> coq_Term -> coq_Term
    -> coq_R_nLambda -> 'a1 **)

let rec coq_R_nLambda_rec f f0 _ _ _ = function
| R_nLambda_0 (n, f1) -> f n f1 __
| R_nLambda_1 (n, f1, m, _res, r0) ->
  f0 n f1 m __ _res r0 (coq_R_nLambda_rec f f0 m f1 _res r0)

(** val nLambda_rect :
    (nat -> coq_Term -> __ -> 'a1) -> (nat -> coq_Term -> nat -> __ -> 'a1 ->
    'a1) -> nat -> coq_Term -> 'a1 **)

let rec nLambda_rect f0 f n f1 =
  let f2 = f0 n f1 in
  let f3 = f n f1 in
  (match n with
   | O -> f2 __
   | S n0 ->
     let f4 = f3 n0 __ in let hrec = nLambda_rect f0 f n0 f1 in f4 hrec)

(** val nLambda_rec :
    (nat -> coq_Term -> __ -> 'a1) -> (nat -> coq_Term -> nat -> __ -> 'a1 ->
    'a1) -> nat -> coq_Term -> 'a1 **)

let nLambda_rec =
  nLambda_rect

(** val coq_R_nLambda_correct :
    nat -> coq_Term -> coq_Term -> coq_R_nLambda **)

let coq_R_nLambda_correct n f _res =
  nLambda_rect (fun y y0 _ _ _ -> R_nLambda_0 (y, y0))
    (fun y y0 y1 _ y3 _ _ -> R_nLambda_1 (y, y0, y1, (nLambda y1 y0),
    (y3 (nLambda y1 y0) __))) n f _res __

(** val coq_Lambdan : nat -> coq_Term -> coq_Term **)

let rec coq_Lambdan n f =
  match n with
  | O -> f
  | S m -> coq_Lambdan m (TLambda (Coq_nAnon, f))

type coq_R_Lambdan =
| R_Lambdan_0 of nat * coq_Term
| R_Lambdan_1 of nat * coq_Term * nat * coq_Term * coq_R_Lambdan

(** val coq_R_Lambdan_rect :
    (nat -> coq_Term -> __ -> 'a1) -> (nat -> coq_Term -> nat -> __ ->
    coq_Term -> coq_R_Lambdan -> 'a1 -> 'a1) -> nat -> coq_Term -> coq_Term
    -> coq_R_Lambdan -> 'a1 **)

let rec coq_R_Lambdan_rect f f0 _ _ _ = function
| R_Lambdan_0 (n, f1) -> f n f1 __
| R_Lambdan_1 (n, f1, m, _res, r0) ->
  f0 n f1 m __ _res r0
    (coq_R_Lambdan_rect f f0 m (TLambda (Coq_nAnon, f1)) _res r0)

(** val coq_R_Lambdan_rec :
    (nat -> coq_Term -> __ -> 'a1) -> (nat -> coq_Term -> nat -> __ ->
    coq_Term -> coq_R_Lambdan -> 'a1 -> 'a1) -> nat -> coq_Term -> coq_Term
    -> coq_R_Lambdan -> 'a1 **)

let rec coq_R_Lambdan_rec f f0 _ _ _ = function
| R_Lambdan_0 (n, f1) -> f n f1 __
| R_Lambdan_1 (n, f1, m, _res, r0) ->
  f0 n f1 m __ _res r0
    (coq_R_Lambdan_rec f f0 m (TLambda (Coq_nAnon, f1)) _res r0)

(** val coq_Lambdan_rect :
    (nat -> coq_Term -> __ -> 'a1) -> (nat -> coq_Term -> nat -> __ -> 'a1 ->
    'a1) -> nat -> coq_Term -> 'a1 **)

let rec coq_Lambdan_rect f0 f n f1 =
  let f2 = f0 n f1 in
  let f3 = f n f1 in
  (match n with
   | O -> f2 __
   | S n0 ->
     let f4 = f3 n0 __ in
     let hrec = coq_Lambdan_rect f0 f n0 (TLambda (Coq_nAnon, f1)) in f4 hrec)

(** val coq_Lambdan_rec :
    (nat -> coq_Term -> __ -> 'a1) -> (nat -> coq_Term -> nat -> __ -> 'a1 ->
    'a1) -> nat -> coq_Term -> 'a1 **)

let coq_Lambdan_rec =
  coq_Lambdan_rect

(** val coq_R_Lambdan_correct :
    nat -> coq_Term -> coq_Term -> coq_R_Lambdan **)

let coq_R_Lambdan_correct n f _res =
  coq_Lambdan_rect (fun y y0 _ _ _ -> R_Lambdan_0 (y, y0))
    (fun y y0 y1 _ y3 _ _ -> R_Lambdan_1 (y, y0, y1,
    (coq_Lambdan y1 (TLambda (Coq_nAnon, y0))),
    (y3 (coq_Lambdan y1 (TLambda (Coq_nAnon, y0))) __))) n f _res __

(** val mkExpand : nat -> (coq_Terms -> coq_Term) -> coq_Terms -> coq_Term **)

let rec mkExpand n f cArgs =
  match n with
  | O -> f cArgs
  | S m ->
    TLambda (Coq_nAnon,
      (mkExpand m f
        (tappend (lifts O cArgs) (Coq_tcons ((TRel O), Coq_tnil)))))

type coq_R_mkExpand =
| R_mkExpand_0 of nat * (coq_Terms -> coq_Term) * coq_Terms
| R_mkExpand_1 of nat * (coq_Terms -> coq_Term) * coq_Terms * nat * coq_Term
   * coq_R_mkExpand

(** val coq_R_mkExpand_rect :
    (nat -> (coq_Terms -> coq_Term) -> coq_Terms -> __ -> 'a1) -> (nat ->
    (coq_Terms -> coq_Term) -> coq_Terms -> nat -> __ -> coq_Term ->
    coq_R_mkExpand -> 'a1 -> 'a1) -> nat -> (coq_Terms -> coq_Term) ->
    coq_Terms -> coq_Term -> coq_R_mkExpand -> 'a1 **)

let rec coq_R_mkExpand_rect f f0 _ _ _ _ = function
| R_mkExpand_0 (n, f1, cArgs) -> f n f1 cArgs __
| R_mkExpand_1 (n, f1, cArgs, m, _res, r0) ->
  f0 n f1 cArgs m __ _res r0
    (coq_R_mkExpand_rect f f0 m f1
      (tappend (lifts O cArgs) (Coq_tcons ((TRel O), Coq_tnil))) _res r0)

(** val coq_R_mkExpand_rec :
    (nat -> (coq_Terms -> coq_Term) -> coq_Terms -> __ -> 'a1) -> (nat ->
    (coq_Terms -> coq_Term) -> coq_Terms -> nat -> __ -> coq_Term ->
    coq_R_mkExpand -> 'a1 -> 'a1) -> nat -> (coq_Terms -> coq_Term) ->
    coq_Terms -> coq_Term -> coq_R_mkExpand -> 'a1 **)

let rec coq_R_mkExpand_rec f f0 _ _ _ _ = function
| R_mkExpand_0 (n, f1, cArgs) -> f n f1 cArgs __
| R_mkExpand_1 (n, f1, cArgs, m, _res, r0) ->
  f0 n f1 cArgs m __ _res r0
    (coq_R_mkExpand_rec f f0 m f1
      (tappend (lifts O cArgs) (Coq_tcons ((TRel O), Coq_tnil))) _res r0)

(** val mkExpand_rect :
    (nat -> (coq_Terms -> coq_Term) -> coq_Terms -> __ -> 'a1) -> (nat ->
    (coq_Terms -> coq_Term) -> coq_Terms -> nat -> __ -> 'a1 -> 'a1) -> nat
    -> (coq_Terms -> coq_Term) -> coq_Terms -> 'a1 **)

let rec mkExpand_rect f0 f n f1 cArgs =
  let f2 = f0 n f1 cArgs in
  let f3 = f n f1 cArgs in
  (match n with
   | O -> f2 __
   | S n0 ->
     let f4 = f3 n0 __ in
     let hrec =
       mkExpand_rect f0 f n0 f1
         (tappend (lifts O cArgs) (Coq_tcons ((TRel O), Coq_tnil)))
     in
     f4 hrec)

(** val mkExpand_rec :
    (nat -> (coq_Terms -> coq_Term) -> coq_Terms -> __ -> 'a1) -> (nat ->
    (coq_Terms -> coq_Term) -> coq_Terms -> nat -> __ -> 'a1 -> 'a1) -> nat
    -> (coq_Terms -> coq_Term) -> coq_Terms -> 'a1 **)

let mkExpand_rec =
  mkExpand_rect

(** val coq_R_mkExpand_correct :
    nat -> (coq_Terms -> coq_Term) -> coq_Terms -> coq_Term -> coq_R_mkExpand **)

let coq_R_mkExpand_correct n f cArgs _res =
  mkExpand_rect (fun y y0 y1 _ _ _ -> R_mkExpand_0 (y, y0, y1))
    (fun y y0 y1 y2 _ y4 _ _ -> R_mkExpand_1 (y, y0, y1, y2,
    (mkExpand y2 y0 (tappend (lifts O y1) (Coq_tcons ((TRel O), Coq_tnil)))),
    (y4
      (mkExpand y2 y0 (tappend (lifts O y1) (Coq_tcons ((TRel O), Coq_tnil))))
      __))) n f cArgs _res __

(** val etaExpand_aArgs :
    (coq_Terms -> coq_Term) -> nat -> nat -> coq_Terms -> coq_Terms ->
    coq_Term **)

let rec etaExpand_aArgs f nargs nlams aArgs cArgs =
  match nargs with
  | O ->
    (match aArgs with
     | Coq_tnil -> nLambda nlams (mkExpand nargs f cArgs)
     | Coq_tcons (_, _) ->
       TWrong
         ('s'::('t'::('r'::('i'::('p'::(';'::(' '::('C'::('o'::('n'::('s'::('t'::('r'::('u'::('c'::('t'::('o'::('r'::(';'::(' '::('t'::('o'::('o'::(' '::('m'::('a'::('n'::('y'::(' '::('a'::('r'::('g'::('s'::[]))))))))))))))))))))))))))))))))))
  | S n ->
    (match aArgs with
     | Coq_tnil -> nLambda nlams (mkExpand nargs f cArgs)
     | Coq_tcons (u, us) ->
       etaExpand_aArgs f n nlams us (tappend cArgs (Coq_tcons (u, Coq_tnil))))

type coq_R_etaExpand_aArgs =
| R_etaExpand_aArgs_0 of nat * nat * coq_Terms * coq_Terms * nat * coq_Term
   * coq_Terms * coq_Term * coq_R_etaExpand_aArgs
| R_etaExpand_aArgs_1 of nat * nat * coq_Terms * coq_Terms * coq_Term
   * coq_Terms
| R_etaExpand_aArgs_2 of nat * nat * coq_Terms * coq_Terms * nat

(** val coq_R_etaExpand_aArgs_rect :
    (coq_Terms -> coq_Term) -> (nat -> nat -> coq_Terms -> coq_Terms -> nat
    -> __ -> coq_Term -> coq_Terms -> __ -> coq_Term -> coq_R_etaExpand_aArgs
    -> 'a1 -> 'a1) -> (nat -> nat -> coq_Terms -> coq_Terms -> __ -> coq_Term
    -> coq_Terms -> __ -> 'a1) -> (nat -> nat -> coq_Terms -> coq_Terms ->
    nat -> __ -> __ -> 'a1) -> nat -> nat -> coq_Terms -> coq_Terms ->
    coq_Term -> coq_R_etaExpand_aArgs -> 'a1 **)

let rec coq_R_etaExpand_aArgs_rect f f0 f1 f2 _ _ _ _ _ = function
| R_etaExpand_aArgs_0 (nargs, nlams, aArgs, cArgs, n, u, us, _res, r0) ->
  f0 nargs nlams aArgs cArgs n __ u us __ _res r0
    (coq_R_etaExpand_aArgs_rect f f0 f1 f2 n nlams us
      (tappend cArgs (Coq_tcons (u, Coq_tnil))) _res r0)
| R_etaExpand_aArgs_1 (nargs, nlams, aArgs, cArgs, _x, _x0) ->
  f1 nargs nlams aArgs cArgs __ _x _x0 __
| R_etaExpand_aArgs_2 (nargs, nlams, aArgs, cArgs, n) ->
  f2 nargs nlams aArgs cArgs n __ __

(** val coq_R_etaExpand_aArgs_rec :
    (coq_Terms -> coq_Term) -> (nat -> nat -> coq_Terms -> coq_Terms -> nat
    -> __ -> coq_Term -> coq_Terms -> __ -> coq_Term -> coq_R_etaExpand_aArgs
    -> 'a1 -> 'a1) -> (nat -> nat -> coq_Terms -> coq_Terms -> __ -> coq_Term
    -> coq_Terms -> __ -> 'a1) -> (nat -> nat -> coq_Terms -> coq_Terms ->
    nat -> __ -> __ -> 'a1) -> nat -> nat -> coq_Terms -> coq_Terms ->
    coq_Term -> coq_R_etaExpand_aArgs -> 'a1 **)

let rec coq_R_etaExpand_aArgs_rec f f0 f1 f2 _ _ _ _ _ = function
| R_etaExpand_aArgs_0 (nargs, nlams, aArgs, cArgs, n, u, us, _res, r0) ->
  f0 nargs nlams aArgs cArgs n __ u us __ _res r0
    (coq_R_etaExpand_aArgs_rec f f0 f1 f2 n nlams us
      (tappend cArgs (Coq_tcons (u, Coq_tnil))) _res r0)
| R_etaExpand_aArgs_1 (nargs, nlams, aArgs, cArgs, _x, _x0) ->
  f1 nargs nlams aArgs cArgs __ _x _x0 __
| R_etaExpand_aArgs_2 (nargs, nlams, aArgs, cArgs, n) ->
  f2 nargs nlams aArgs cArgs n __ __

(** val etaExpand_aArgs_rect :
    (coq_Terms -> coq_Term) -> (nat -> nat -> coq_Terms -> coq_Terms -> nat
    -> __ -> coq_Term -> coq_Terms -> __ -> 'a1 -> 'a1) -> (nat -> nat ->
    coq_Terms -> coq_Terms -> __ -> coq_Term -> coq_Terms -> __ -> 'a1) ->
    (nat -> nat -> coq_Terms -> coq_Terms -> nat -> __ -> __ -> 'a1) -> nat
    -> nat -> coq_Terms -> coq_Terms -> 'a1 **)

let rec etaExpand_aArgs_rect f f1 f0 f2 nargs nlams aArgs cArgs =
  let f3 = f1 nargs nlams aArgs cArgs in
  let f4 = f0 nargs nlams aArgs cArgs in
  let f5 = f2 nargs nlams aArgs cArgs in
  let f6 = f5 nargs __ in
  (match nargs with
   | O ->
     let f7 = f4 __ in
     (match aArgs with
      | Coq_tnil -> f6 __
      | Coq_tcons (t, t0) -> f7 t t0 __)
   | S n ->
     let f7 = f3 n __ in
     (match aArgs with
      | Coq_tnil -> f6 __
      | Coq_tcons (t, t0) ->
        let f8 = f7 t t0 __ in
        let hrec =
          etaExpand_aArgs_rect f f1 f0 f2 n nlams t0
            (tappend cArgs (Coq_tcons (t, Coq_tnil)))
        in
        f8 hrec))

(** val etaExpand_aArgs_rec :
    (coq_Terms -> coq_Term) -> (nat -> nat -> coq_Terms -> coq_Terms -> nat
    -> __ -> coq_Term -> coq_Terms -> __ -> 'a1 -> 'a1) -> (nat -> nat ->
    coq_Terms -> coq_Terms -> __ -> coq_Term -> coq_Terms -> __ -> 'a1) ->
    (nat -> nat -> coq_Terms -> coq_Terms -> nat -> __ -> __ -> 'a1) -> nat
    -> nat -> coq_Terms -> coq_Terms -> 'a1 **)

let etaExpand_aArgs_rec =
  etaExpand_aArgs_rect

(** val coq_R_etaExpand_aArgs_correct :
    (coq_Terms -> coq_Term) -> nat -> nat -> coq_Terms -> coq_Terms ->
    coq_Term -> coq_R_etaExpand_aArgs **)

let coq_R_etaExpand_aArgs_correct f nargs nlams aArgs cArgs _res =
  etaExpand_aArgs_rect f (fun y y0 y1 y2 y3 _ y5 y6 _ y8 _ _ ->
    R_etaExpand_aArgs_0 (y, y0, y1, y2, y3, y5, y6,
    (etaExpand_aArgs f y3 y0 y6 (tappend y2 (Coq_tcons (y5, Coq_tnil)))),
    (y8 (etaExpand_aArgs f y3 y0 y6 (tappend y2 (Coq_tcons (y5, Coq_tnil))))
      __))) (fun y y0 y1 y2 _ y4 y5 _ _ _ -> R_etaExpand_aArgs_1 (y, y0, y1,
    y2, y4, y5)) (fun y y0 y1 y2 y3 _ _ _ _ -> R_etaExpand_aArgs_2 (y, y0,
    y1, y2, y3)) nargs nlams aArgs cArgs _res __

(** val etaExpand :
    (coq_Terms -> coq_Term) -> coq_Terms -> nat -> nat -> coq_Term **)

let rec etaExpand f actualArgs npars nargs =
  match actualArgs with
  | Coq_tnil -> etaExpand_aArgs f nargs npars Coq_tnil Coq_tnil
  | Coq_tcons (_, us) ->
    (match npars with
     | O -> etaExpand_aArgs f nargs O actualArgs Coq_tnil
     | S n -> etaExpand f us n nargs)

type coq_R_etaExpand =
| R_etaExpand_0 of coq_Terms * nat * nat * coq_Term * coq_Terms * nat
   * coq_Term * coq_R_etaExpand
| R_etaExpand_1 of coq_Terms * nat * nat * nat
| R_etaExpand_2 of coq_Terms * nat * nat * coq_Terms

(** val coq_R_etaExpand_rect :
    (coq_Terms -> coq_Term) -> (coq_Terms -> nat -> nat -> coq_Term ->
    coq_Terms -> __ -> nat -> __ -> coq_Term -> coq_R_etaExpand -> 'a1 ->
    'a1) -> (coq_Terms -> nat -> nat -> __ -> nat -> __ -> 'a1) -> (coq_Terms
    -> nat -> nat -> coq_Terms -> __ -> __ -> __ -> 'a1) -> coq_Terms -> nat
    -> nat -> coq_Term -> coq_R_etaExpand -> 'a1 **)

let rec coq_R_etaExpand_rect f f0 f1 f2 _ _ _ _ = function
| R_etaExpand_0 (actualArgs, npars, nargs, u, us, n, _res, r0) ->
  f0 actualArgs npars nargs u us __ n __ _res r0
    (coq_R_etaExpand_rect f f0 f1 f2 us n nargs _res r0)
| R_etaExpand_1 (actualArgs, npars, nargs, nlams) ->
  f1 actualArgs npars nargs __ nlams __
| R_etaExpand_2 (actualArgs, npars, nargs, aArgs) ->
  f2 actualArgs npars nargs aArgs __ __ __

(** val coq_R_etaExpand_rec :
    (coq_Terms -> coq_Term) -> (coq_Terms -> nat -> nat -> coq_Term ->
    coq_Terms -> __ -> nat -> __ -> coq_Term -> coq_R_etaExpand -> 'a1 ->
    'a1) -> (coq_Terms -> nat -> nat -> __ -> nat -> __ -> 'a1) -> (coq_Terms
    -> nat -> nat -> coq_Terms -> __ -> __ -> __ -> 'a1) -> coq_Terms -> nat
    -> nat -> coq_Term -> coq_R_etaExpand -> 'a1 **)

let rec coq_R_etaExpand_rec f f0 f1 f2 _ _ _ _ = function
| R_etaExpand_0 (actualArgs, npars, nargs, u, us, n, _res, r0) ->
  f0 actualArgs npars nargs u us __ n __ _res r0
    (coq_R_etaExpand_rec f f0 f1 f2 us n nargs _res r0)
| R_etaExpand_1 (actualArgs, npars, nargs, nlams) ->
  f1 actualArgs npars nargs __ nlams __
| R_etaExpand_2 (actualArgs, npars, nargs, aArgs) ->
  f2 actualArgs npars nargs aArgs __ __ __

(** val etaExpand_rect :
    (coq_Terms -> coq_Term) -> (coq_Terms -> nat -> nat -> coq_Term ->
    coq_Terms -> __ -> nat -> __ -> 'a1 -> 'a1) -> (coq_Terms -> nat -> nat
    -> __ -> nat -> __ -> 'a1) -> (coq_Terms -> nat -> nat -> coq_Terms -> __
    -> __ -> __ -> 'a1) -> coq_Terms -> nat -> nat -> 'a1 **)

let rec etaExpand_rect f f1 f0 f2 actualArgs npars nargs =
  let f3 = f1 actualArgs npars nargs in
  let f4 = f0 actualArgs npars nargs in
  let f5 = f2 actualArgs npars nargs in
  let f6 = f5 actualArgs __ in
  let f7 = fun _ -> f4 __ npars __ in
  (match actualArgs with
   | Coq_tnil -> f7 __
   | Coq_tcons (t, t0) ->
     let f8 = f3 t t0 __ in
     let f9 = fun _ -> f6 __ __ in
     (match npars with
      | O -> f9 __
      | S n ->
        let f10 = f8 n __ in
        let hrec = etaExpand_rect f f1 f0 f2 t0 n nargs in f10 hrec))

(** val etaExpand_rec :
    (coq_Terms -> coq_Term) -> (coq_Terms -> nat -> nat -> coq_Term ->
    coq_Terms -> __ -> nat -> __ -> 'a1 -> 'a1) -> (coq_Terms -> nat -> nat
    -> __ -> nat -> __ -> 'a1) -> (coq_Terms -> nat -> nat -> coq_Terms -> __
    -> __ -> __ -> 'a1) -> coq_Terms -> nat -> nat -> 'a1 **)

let etaExpand_rec =
  etaExpand_rect

(** val coq_R_etaExpand_correct :
    (coq_Terms -> coq_Term) -> coq_Terms -> nat -> nat -> coq_Term ->
    coq_R_etaExpand **)

let coq_R_etaExpand_correct f actualArgs npars nargs _res =
  etaExpand_rect f (fun y y0 y1 y2 y3 _ y5 _ y7 _ _ -> R_etaExpand_0 (y, y0,
    y1, y2, y3, y5, (etaExpand f y3 y5 y1), (y7 (etaExpand f y3 y5 y1) __)))
    (fun y y0 y1 _ y3 _ _ _ -> R_etaExpand_1 (y, y0, y1, y3))
    (fun y y0 y1 y2 _ _ _ _ _ -> R_etaExpand_2 (y, y0, y1, y2)) actualArgs
    npars nargs _res __

(** val coq_CanonicalP :
    (coq_L1gTerm -> coq_Term) -> coq_L1gTerm -> coq_Term -> ((((coq_Terms ->
    coq_Term) * coq_Terms) * nat) * nat) option **)

let rec coq_CanonicalP pre_strip fn arg =
  match fn with
  | Compile0.TApp (gn, brg) ->
    (match coq_CanonicalP pre_strip gn (pre_strip brg) with
     | Some p ->
       let (p0, na) = p in
       let (p1, np) = p0 in
       let (f, brgs) = p1 in
       Some (((f, (tappend brgs (Coq_tcons (arg, Coq_tnil)))), np), na)
     | None -> None)
  | Compile0.TConstruct (i, m, np, na) ->
    Some ((((fun x -> TConstruct (i, m, x)), (Coq_tcons (arg, Coq_tnil))),
      np), na)
  | _ -> None

(** val strips : (coq_L1gTerm -> coq_Term) -> coq_L1gTerms -> coq_Terms **)

let rec strips pre_strip = function
| [] -> Coq_tnil
| u :: us -> Coq_tcons ((pre_strip u), (strips pre_strip us))

type coq_R_strips =
| R_strips_0 of coq_L1gTerms
| R_strips_1 of coq_L1gTerms * Compile0.coq_Term * Compile0.coq_Term list
   * coq_Terms * coq_R_strips

(** val coq_R_strips_rect :
    (coq_L1gTerm -> coq_Term) -> (coq_L1gTerms -> __ -> 'a1) -> (coq_L1gTerms
    -> Compile0.coq_Term -> Compile0.coq_Term list -> __ -> coq_Terms ->
    coq_R_strips -> 'a1 -> 'a1) -> coq_L1gTerms -> coq_Terms -> coq_R_strips
    -> 'a1 **)

let rec coq_R_strips_rect pre_strip f f0 _ _ = function
| R_strips_0 ts -> f ts __
| R_strips_1 (ts, u, us, _res, r0) ->
  f0 ts u us __ _res r0 (coq_R_strips_rect pre_strip f f0 us _res r0)

(** val coq_R_strips_rec :
    (coq_L1gTerm -> coq_Term) -> (coq_L1gTerms -> __ -> 'a1) -> (coq_L1gTerms
    -> Compile0.coq_Term -> Compile0.coq_Term list -> __ -> coq_Terms ->
    coq_R_strips -> 'a1 -> 'a1) -> coq_L1gTerms -> coq_Terms -> coq_R_strips
    -> 'a1 **)

let rec coq_R_strips_rec pre_strip f f0 _ _ = function
| R_strips_0 ts -> f ts __
| R_strips_1 (ts, u, us, _res, r0) ->
  f0 ts u us __ _res r0 (coq_R_strips_rec pre_strip f f0 us _res r0)

(** val strips_rect :
    (coq_L1gTerm -> coq_Term) -> (coq_L1gTerms -> __ -> 'a1) -> (coq_L1gTerms
    -> Compile0.coq_Term -> Compile0.coq_Term list -> __ -> 'a1 -> 'a1) ->
    coq_L1gTerms -> 'a1 **)

let rec strips_rect pre_strip f0 f ts =
  let f1 = f0 ts in
  let f2 = f ts in
  (match ts with
   | [] -> f1 __
   | t :: l ->
     let f3 = f2 t l __ in let hrec = strips_rect pre_strip f0 f l in f3 hrec)

(** val strips_rec :
    (coq_L1gTerm -> coq_Term) -> (coq_L1gTerms -> __ -> 'a1) -> (coq_L1gTerms
    -> Compile0.coq_Term -> Compile0.coq_Term list -> __ -> 'a1 -> 'a1) ->
    coq_L1gTerms -> 'a1 **)

let strips_rec =
  strips_rect

(** val coq_R_strips_correct :
    (coq_L1gTerm -> coq_Term) -> coq_L1gTerms -> coq_Terms -> coq_R_strips **)

let coq_R_strips_correct pre_strip ts _res =
  strips_rect pre_strip (fun y _ _ _ -> R_strips_0 y)
    (fun y y0 y1 _ y3 _ _ -> R_strips_1 (y, y0, y1, (strips pre_strip y1),
    (y3 (strips pre_strip y1) __))) ts _res __

(** val strip : coq_L1gTerm -> coq_Term **)

let rec strip = function
| Compile0.TRel n -> TRel n
| Compile0.TProof -> TProof
| Compile0.TLambda (nm, bod) -> TLambda (nm, (strip bod))
| Compile0.TLetIn (nm, dfn, bod) -> TLetIn (nm, (strip dfn), (strip bod))
| Compile0.TApp (fn, arg) ->
  let sarg = strip arg in
  (match coq_CanonicalP strip fn sarg with
   | Some p ->
     let (p0, nargs) = p in
     let (p1, npars) = p0 in
     let (f, args) = p1 in etaExpand f args npars nargs
   | None -> TApp ((strip fn), sarg))
| Compile0.TConst nm -> TConst nm
| Compile0.TConstruct (i, m, npars, nargs) ->
  etaExpand (fun x -> TConstruct (i, m, x)) Coq_tnil npars nargs
| Compile0.TCase (i, mch, brs) -> TCase ((fst i), (strip mch), (stripBs brs))
| Compile0.TFix (ds, n) -> TFix ((stripDs ds), n)
| Compile0.TProj (p, bod) ->
  let (p0, nargs) = p in
  let (ind, _) = p0 in TProj ((ind, nargs), (strip bod))
| Compile0.TWrong str -> TWrong str

(** val stripBs : coq_L1gBrs -> coq_Brs **)

and stripBs = function
| Compile0.Coq_bnil -> Coq_bnil
| Compile0.Coq_bcons (n, t, ts) -> Coq_bcons (n, (strip t), (stripBs ts))

(** val stripDs : coq_L1gDefs -> coq_Defs **)

and stripDs = function
| Compile0.Coq_dnil -> Coq_dnil
| Compile0.Coq_dcons (nm, t, m, ds) ->
  Coq_dcons (nm, (strip t), m, (stripDs ds))

type coq_R_strip =
| R_strip_0 of coq_L1gTerm * nat
| R_strip_1 of coq_L1gTerm
| R_strip_2 of coq_L1gTerm * name * Compile0.coq_Term * coq_Term * coq_R_strip
| R_strip_3 of coq_L1gTerm * name * Compile0.coq_Term * Compile0.coq_Term
   * coq_Term * coq_R_strip * coq_Term * coq_R_strip
| R_strip_4 of coq_L1gTerm * Compile0.coq_Term * Compile0.coq_Term * 
   coq_Term * coq_R_strip * coq_Term * coq_R_strip
| R_strip_5 of coq_L1gTerm * Compile0.coq_Term * Compile0.coq_Term * 
   coq_Term * coq_R_strip * (coq_Terms -> coq_Term) * coq_Terms * nat * 
   nat
| R_strip_6 of coq_L1gTerm * char list
| R_strip_7 of coq_L1gTerm * inductive * nat * nat * nat
| R_strip_8 of coq_L1gTerm * (inductive * nat) * Compile0.coq_Term
   * Compile0.coq_Brs * coq_Term * coq_R_strip * coq_Brs * coq_R_stripBs
| R_strip_9 of coq_L1gTerm * Compile0.coq_Defs * nat * coq_Defs
   * coq_R_stripDs
| R_strip_10 of coq_L1gTerm * inductive * nat * nat * Compile0.coq_Term
   * coq_Term * coq_R_strip
| R_strip_11 of coq_L1gTerm * char list
and coq_R_stripBs =
| R_stripBs_0 of coq_L1gBrs
| R_stripBs_1 of coq_L1gBrs * nat * Compile0.coq_Term * Compile0.coq_Brs
   * coq_Term * coq_R_strip * coq_Brs * coq_R_stripBs
and coq_R_stripDs =
| R_stripDs_0 of coq_L1gDefs
| R_stripDs_1 of coq_L1gDefs * name * Compile0.coq_Term * nat
   * Compile0.coq_Defs * coq_Term * coq_R_strip * coq_Defs * coq_R_stripDs

(** val coq_R_strip_rect :
    (coq_L1gTerm -> nat -> __ -> 'a1) -> (coq_L1gTerm -> __ -> 'a1) ->
    (coq_L1gTerm -> name -> Compile0.coq_Term -> __ -> coq_Term ->
    coq_R_strip -> 'a1 -> 'a1) -> (coq_L1gTerm -> name -> Compile0.coq_Term
    -> Compile0.coq_Term -> __ -> coq_Term -> coq_R_strip -> 'a1 -> coq_Term
    -> coq_R_strip -> 'a1 -> 'a1) -> (coq_L1gTerm -> Compile0.coq_Term ->
    Compile0.coq_Term -> __ -> coq_Term -> coq_R_strip -> 'a1 -> __ ->
    coq_Term -> coq_R_strip -> 'a1 -> 'a1) -> (coq_L1gTerm ->
    Compile0.coq_Term -> Compile0.coq_Term -> __ -> coq_Term -> coq_R_strip
    -> 'a1 -> (coq_Terms -> coq_Term) -> coq_Terms -> nat -> nat -> __ ->
    'a1) -> (coq_L1gTerm -> char list -> __ -> 'a1) -> (coq_L1gTerm ->
    inductive -> nat -> nat -> nat -> __ -> 'a1) -> (coq_L1gTerm ->
    (inductive * nat) -> Compile0.coq_Term -> Compile0.coq_Brs -> __ ->
    coq_Term -> coq_R_strip -> 'a1 -> coq_Brs -> coq_R_stripBs -> 'a1) ->
    (coq_L1gTerm -> Compile0.coq_Defs -> nat -> __ -> coq_Defs ->
    coq_R_stripDs -> 'a1) -> (coq_L1gTerm -> inductive -> nat -> nat ->
    Compile0.coq_Term -> __ -> coq_Term -> coq_R_strip -> 'a1 -> 'a1) ->
    (coq_L1gTerm -> char list -> __ -> 'a1) -> coq_L1gTerm -> coq_Term ->
    coq_R_strip -> 'a1 **)

let rec coq_R_strip_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 _ _ = function
| R_strip_0 (t, n) -> f t n __
| R_strip_1 t -> f0 t __
| R_strip_2 (t, nm, bod, _res, r0) ->
  f1 t nm bod __ _res r0
    (coq_R_strip_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 bod _res r0)
| R_strip_3 (t, nm, dfn, bod, _res0, r0, _res, r1) ->
  f2 t nm dfn bod __ _res0 r0
    (coq_R_strip_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 dfn _res0 r0) _res
    r1 (coq_R_strip_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 bod _res r1)
| R_strip_4 (t, fn, arg, _res, r0, x, x0) ->
  f3 t fn arg __ _res r0
    (coq_R_strip_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 arg _res r0) __ x
    x0 (coq_R_strip_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 fn x x0)
| R_strip_5 (t, fn, arg, _res, r0, x, x0, x1, x2) ->
  f4 t fn arg __ _res r0
    (coq_R_strip_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 arg _res r0) x x0
    x1 x2 __
| R_strip_6 (t, nm) -> f5 t nm __
| R_strip_7 (t, i, m, npars, nargs) -> f6 t i m npars nargs __
| R_strip_8 (t, i, mch, brs, _res0, r0, _res, r1) ->
  f7 t i mch brs __ _res0 r0
    (coq_R_strip_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 mch _res0 r0) _res
    r1
| R_strip_9 (t, ds, n, _res, r0) -> f8 t ds n __ _res r0
| R_strip_10 (t, ind, _x, nargs, bod, _res, r0) ->
  f9 t ind _x nargs bod __ _res r0
    (coq_R_strip_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 bod _res r0)
| R_strip_11 (t, str) -> f10 t str __

(** val coq_R_strip_rec :
    (coq_L1gTerm -> nat -> __ -> 'a1) -> (coq_L1gTerm -> __ -> 'a1) ->
    (coq_L1gTerm -> name -> Compile0.coq_Term -> __ -> coq_Term ->
    coq_R_strip -> 'a1 -> 'a1) -> (coq_L1gTerm -> name -> Compile0.coq_Term
    -> Compile0.coq_Term -> __ -> coq_Term -> coq_R_strip -> 'a1 -> coq_Term
    -> coq_R_strip -> 'a1 -> 'a1) -> (coq_L1gTerm -> Compile0.coq_Term ->
    Compile0.coq_Term -> __ -> coq_Term -> coq_R_strip -> 'a1 -> __ ->
    coq_Term -> coq_R_strip -> 'a1 -> 'a1) -> (coq_L1gTerm ->
    Compile0.coq_Term -> Compile0.coq_Term -> __ -> coq_Term -> coq_R_strip
    -> 'a1 -> (coq_Terms -> coq_Term) -> coq_Terms -> nat -> nat -> __ ->
    'a1) -> (coq_L1gTerm -> char list -> __ -> 'a1) -> (coq_L1gTerm ->
    inductive -> nat -> nat -> nat -> __ -> 'a1) -> (coq_L1gTerm ->
    (inductive * nat) -> Compile0.coq_Term -> Compile0.coq_Brs -> __ ->
    coq_Term -> coq_R_strip -> 'a1 -> coq_Brs -> coq_R_stripBs -> 'a1) ->
    (coq_L1gTerm -> Compile0.coq_Defs -> nat -> __ -> coq_Defs ->
    coq_R_stripDs -> 'a1) -> (coq_L1gTerm -> inductive -> nat -> nat ->
    Compile0.coq_Term -> __ -> coq_Term -> coq_R_strip -> 'a1 -> 'a1) ->
    (coq_L1gTerm -> char list -> __ -> 'a1) -> coq_L1gTerm -> coq_Term ->
    coq_R_strip -> 'a1 **)

let rec coq_R_strip_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 _ _ = function
| R_strip_0 (t, n) -> f t n __
| R_strip_1 t -> f0 t __
| R_strip_2 (t, nm, bod, _res, r0) ->
  f1 t nm bod __ _res r0
    (coq_R_strip_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 bod _res r0)
| R_strip_3 (t, nm, dfn, bod, _res0, r0, _res, r1) ->
  f2 t nm dfn bod __ _res0 r0
    (coq_R_strip_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 dfn _res0 r0) _res
    r1 (coq_R_strip_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 bod _res r1)
| R_strip_4 (t, fn, arg, _res, r0, x, x0) ->
  f3 t fn arg __ _res r0
    (coq_R_strip_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 arg _res r0) __ x x0
    (coq_R_strip_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 fn x x0)
| R_strip_5 (t, fn, arg, _res, r0, x, x0, x1, x2) ->
  f4 t fn arg __ _res r0
    (coq_R_strip_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 arg _res r0) x x0 x1
    x2 __
| R_strip_6 (t, nm) -> f5 t nm __
| R_strip_7 (t, i, m, npars, nargs) -> f6 t i m npars nargs __
| R_strip_8 (t, i, mch, brs, _res0, r0, _res, r1) ->
  f7 t i mch brs __ _res0 r0
    (coq_R_strip_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 mch _res0 r0) _res r1
| R_strip_9 (t, ds, n, _res, r0) -> f8 t ds n __ _res r0
| R_strip_10 (t, ind, _x, nargs, bod, _res, r0) ->
  f9 t ind _x nargs bod __ _res r0
    (coq_R_strip_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 bod _res r0)
| R_strip_11 (t, str) -> f10 t str __

(** val coq_R_stripBs_rect :
    (coq_L1gBrs -> __ -> 'a1) -> (coq_L1gBrs -> nat -> Compile0.coq_Term ->
    Compile0.coq_Brs -> __ -> coq_Term -> coq_R_strip -> coq_Brs ->
    coq_R_stripBs -> 'a1 -> 'a1) -> coq_L1gBrs -> coq_Brs -> coq_R_stripBs ->
    'a1 **)

let rec coq_R_stripBs_rect f f0 _ _ = function
| R_stripBs_0 bs -> f bs __
| R_stripBs_1 (bs, n, t, ts, _res0, r0, _res, r1) ->
  f0 bs n t ts __ _res0 r0 _res r1 (coq_R_stripBs_rect f f0 ts _res r1)

(** val coq_R_stripBs_rec :
    (coq_L1gBrs -> __ -> 'a1) -> (coq_L1gBrs -> nat -> Compile0.coq_Term ->
    Compile0.coq_Brs -> __ -> coq_Term -> coq_R_strip -> coq_Brs ->
    coq_R_stripBs -> 'a1 -> 'a1) -> coq_L1gBrs -> coq_Brs -> coq_R_stripBs ->
    'a1 **)

let rec coq_R_stripBs_rec f f0 _ _ = function
| R_stripBs_0 bs -> f bs __
| R_stripBs_1 (bs, n, t, ts, _res0, r0, _res, r1) ->
  f0 bs n t ts __ _res0 r0 _res r1 (coq_R_stripBs_rec f f0 ts _res r1)

(** val coq_R_stripDs_rect :
    (coq_L1gDefs -> __ -> 'a1) -> (coq_L1gDefs -> name -> Compile0.coq_Term
    -> nat -> Compile0.coq_Defs -> __ -> coq_Term -> coq_R_strip -> coq_Defs
    -> coq_R_stripDs -> 'a1 -> 'a1) -> coq_L1gDefs -> coq_Defs ->
    coq_R_stripDs -> 'a1 **)

let rec coq_R_stripDs_rect f f0 _ _ = function
| R_stripDs_0 ts -> f ts __
| R_stripDs_1 (ts, nm, t, m, ds, _res0, r0, _res, r1) ->
  f0 ts nm t m ds __ _res0 r0 _res r1 (coq_R_stripDs_rect f f0 ds _res r1)

(** val coq_R_stripDs_rec :
    (coq_L1gDefs -> __ -> 'a1) -> (coq_L1gDefs -> name -> Compile0.coq_Term
    -> nat -> Compile0.coq_Defs -> __ -> coq_Term -> coq_R_strip -> coq_Defs
    -> coq_R_stripDs -> 'a1 -> 'a1) -> coq_L1gDefs -> coq_Defs ->
    coq_R_stripDs -> 'a1 **)

let rec coq_R_stripDs_rec f f0 _ _ = function
| R_stripDs_0 ts -> f ts __
| R_stripDs_1 (ts, nm, t, m, ds, _res0, r0, _res, r1) ->
  f0 ts nm t m ds __ _res0 r0 _res r1 (coq_R_stripDs_rec f f0 ds _res r1)

(** val strip_rect :
    (coq_L1gTerm -> nat -> __ -> 'a1) -> (coq_L1gTerm -> __ -> 'a1) ->
    (coq_L1gTerm -> name -> Compile0.coq_Term -> __ -> 'a1 -> 'a1) ->
    (coq_L1gTerm -> name -> Compile0.coq_Term -> Compile0.coq_Term -> __ ->
    'a1 -> 'a1 -> 'a1) -> (coq_L1gTerm -> Compile0.coq_Term ->
    Compile0.coq_Term -> __ -> 'a1 -> __ -> 'a1 -> 'a1) -> (coq_L1gTerm ->
    Compile0.coq_Term -> Compile0.coq_Term -> __ -> 'a1 -> (coq_Terms ->
    coq_Term) -> coq_Terms -> nat -> nat -> __ -> 'a1) -> (coq_L1gTerm ->
    char list -> __ -> 'a1) -> (coq_L1gTerm -> inductive -> nat -> nat -> nat
    -> __ -> 'a1) -> (coq_L1gTerm -> (inductive * nat) -> Compile0.coq_Term
    -> Compile0.coq_Brs -> __ -> 'a1 -> 'a1) -> (coq_L1gTerm ->
    Compile0.coq_Defs -> nat -> __ -> 'a1) -> (coq_L1gTerm -> inductive ->
    nat -> nat -> Compile0.coq_Term -> __ -> 'a1 -> 'a1) -> (coq_L1gTerm ->
    char list -> __ -> 'a1) -> coq_L1gTerm -> 'a1 **)

let rec strip_rect f10 f9 f8 f7 f6 f5 f4 f3 f2 f1 f0 f t =
  let f11 = f10 t in
  let f12 = f9 t in
  let f13 = f8 t in
  let f14 = f7 t in
  let f15 = f6 t in
  let f16 = f5 t in
  let f17 = f4 t in
  let f18 = f3 t in
  let f19 = f2 t in
  let f20 = f1 t in
  let f21 = f0 t in
  let f22 = f t in
  (match t with
   | Compile0.TRel n -> f11 n __
   | Compile0.TProof -> f12 __
   | Compile0.TLambda (n, t0) ->
     let f23 = f13 n t0 __ in
     let hrec = strip_rect f10 f9 f8 f7 f6 f5 f4 f3 f2 f1 f0 f t0 in f23 hrec
   | Compile0.TLetIn (n, t0, t1) ->
     let f23 = f14 n t0 t1 __ in
     let f24 =
       let hrec = strip_rect f10 f9 f8 f7 f6 f5 f4 f3 f2 f1 f0 f t0 in
       f23 hrec
     in
     let hrec = strip_rect f10 f9 f8 f7 f6 f5 f4 f3 f2 f1 f0 f t1 in f24 hrec
   | Compile0.TApp (t0, t1) ->
     let f23 = f15 t0 t1 __ in
     let f24 =
       let hrec = strip_rect f10 f9 f8 f7 f6 f5 f4 f3 f2 f1 f0 f t1 in
       f23 hrec
     in
     let f25 = fun _ ->
       let hrec = strip_rect f10 f9 f8 f7 f6 f5 f4 f3 f2 f1 f0 f t0 in
       f24 __ hrec
     in
     let f26 = f16 t0 t1 __ in
     let f27 =
       let hrec = strip_rect f10 f9 f8 f7 f6 f5 f4 f3 f2 f1 f0 f t1 in
       f26 hrec
     in
     (match coq_CanonicalP strip t0 (strip t1) with
      | Some p ->
        let (p0, n) = p in
        let (p1, n0) = p0 in let (t2, t3) = p1 in f27 t2 t3 n0 n __
      | None -> f25 __)
   | Compile0.TConst s -> f17 s __
   | Compile0.TConstruct (i, n, n0, n1) -> f18 i n n0 n1 __
   | Compile0.TCase (p, t0, b) ->
     let f23 = f19 p t0 b __ in
     let hrec = strip_rect f10 f9 f8 f7 f6 f5 f4 f3 f2 f1 f0 f t0 in f23 hrec
   | Compile0.TFix (d, n) -> f20 d n __
   | Compile0.TProj (p, t0) ->
     let (p0, n) = p in
     let (i, n0) = p0 in
     let f23 = f21 i n0 n t0 __ in
     let hrec = strip_rect f10 f9 f8 f7 f6 f5 f4 f3 f2 f1 f0 f t0 in f23 hrec
   | Compile0.TWrong s -> f22 s __)

(** val strip_rec :
    (coq_L1gTerm -> nat -> __ -> 'a1) -> (coq_L1gTerm -> __ -> 'a1) ->
    (coq_L1gTerm -> name -> Compile0.coq_Term -> __ -> 'a1 -> 'a1) ->
    (coq_L1gTerm -> name -> Compile0.coq_Term -> Compile0.coq_Term -> __ ->
    'a1 -> 'a1 -> 'a1) -> (coq_L1gTerm -> Compile0.coq_Term ->
    Compile0.coq_Term -> __ -> 'a1 -> __ -> 'a1 -> 'a1) -> (coq_L1gTerm ->
    Compile0.coq_Term -> Compile0.coq_Term -> __ -> 'a1 -> (coq_Terms ->
    coq_Term) -> coq_Terms -> nat -> nat -> __ -> 'a1) -> (coq_L1gTerm ->
    char list -> __ -> 'a1) -> (coq_L1gTerm -> inductive -> nat -> nat -> nat
    -> __ -> 'a1) -> (coq_L1gTerm -> (inductive * nat) -> Compile0.coq_Term
    -> Compile0.coq_Brs -> __ -> 'a1 -> 'a1) -> (coq_L1gTerm ->
    Compile0.coq_Defs -> nat -> __ -> 'a1) -> (coq_L1gTerm -> inductive ->
    nat -> nat -> Compile0.coq_Term -> __ -> 'a1 -> 'a1) -> (coq_L1gTerm ->
    char list -> __ -> 'a1) -> coq_L1gTerm -> 'a1 **)

let strip_rec =
  strip_rect

(** val stripBs_rect :
    (coq_L1gBrs -> __ -> 'a1) -> (coq_L1gBrs -> nat -> Compile0.coq_Term ->
    Compile0.coq_Brs -> __ -> 'a1 -> 'a1) -> coq_L1gBrs -> 'a1 **)

let rec stripBs_rect f0 f bs =
  let f1 = f0 bs in
  let f2 = f bs in
  (match bs with
   | Compile0.Coq_bnil -> f1 __
   | Compile0.Coq_bcons (n, t, b) ->
     let f3 = f2 n t b __ in let hrec = stripBs_rect f0 f b in f3 hrec)

(** val stripBs_rec :
    (coq_L1gBrs -> __ -> 'a1) -> (coq_L1gBrs -> nat -> Compile0.coq_Term ->
    Compile0.coq_Brs -> __ -> 'a1 -> 'a1) -> coq_L1gBrs -> 'a1 **)

let stripBs_rec =
  stripBs_rect

(** val stripDs_rect :
    (coq_L1gDefs -> __ -> 'a1) -> (coq_L1gDefs -> name -> Compile0.coq_Term
    -> nat -> Compile0.coq_Defs -> __ -> 'a1 -> 'a1) -> coq_L1gDefs -> 'a1 **)

let rec stripDs_rect f0 f ts =
  let f1 = f0 ts in
  let f2 = f ts in
  (match ts with
   | Compile0.Coq_dnil -> f1 __
   | Compile0.Coq_dcons (n, t, n0, d) ->
     let f3 = f2 n t n0 d __ in let hrec = stripDs_rect f0 f d in f3 hrec)

(** val stripDs_rec :
    (coq_L1gDefs -> __ -> 'a1) -> (coq_L1gDefs -> name -> Compile0.coq_Term
    -> nat -> Compile0.coq_Defs -> __ -> 'a1 -> 'a1) -> coq_L1gDefs -> 'a1 **)

let stripDs_rec =
  stripDs_rect

(** val coq_R_strip_correct : coq_L1gTerm -> coq_Term -> coq_R_strip **)

let coq_R_strip_correct t _res =
  let f14 = fun y y0 _ -> R_strip_0 (y, y0) in
  let f13 = fun y _ -> R_strip_1 y in
  let f12 = fun y y0 y1 y3 _ -> R_strip_2 (y, y0, y1, (strip y1),
    (y3 (strip y1) __))
  in
  let f11 = fun y y0 y1 y2 y4 y5 _ -> R_strip_3 (y, y0, y1, y2, (strip y1),
    (y4 (strip y1) __), (strip y2), (y5 (strip y2) __))
  in
  let f10 = fun y y0 y1 y3 y5 _ -> R_strip_4 (y, y0, y1, (strip y1),
    (y3 (strip y1) __), (strip y0), (y5 (strip y0) __))
  in
  let f9 = fun y y0 y1 y3 y4 y5 y6 y7 _ -> R_strip_5 (y, y0, y1, (strip y1),
    (y3 (strip y1) __), y4, y5, y6, y7)
  in
  let f8 = fun y y0 _ -> R_strip_6 (y, y0) in
  let f7 = fun y y0 y1 y2 y3 _ -> R_strip_7 (y, y0, y1, y2, y3) in
  let f6 = fun y y0 y1 y2 y4 y5 _ -> R_strip_8 (y, y0, y1, y2, (strip y1),
    (y4 (strip y1) __), (stripBs y2), (y5 (stripBs y2) __))
  in
  let f5 = fun y y0 y1 y3 _ -> R_strip_9 (y, y0, y1, (stripDs y0),
    (y3 (stripDs y0) __))
  in
  let f4 = fun y y0 y1 y2 y3 y5 _ -> R_strip_10 (y, y0, y1, y2, y3,
    (strip y3), (y5 (strip y3) __))
  in
  let f3 = fun y y0 _ -> R_strip_11 (y, y0) in
  let f2 = fun y _ -> R_stripBs_0 y in
  let f1 = fun y y0 y1 y2 y4 y5 _ -> R_stripBs_1 (y, y0, y1, y2, (strip y1),
    (y4 (strip y1) __), (stripBs y2), (y5 (stripBs y2) __))
  in
  let f0 = fun y _ -> R_stripDs_0 y in
  let f = fun y y0 y1 y2 y3 y5 y6 _ -> R_stripDs_1 (y, y0, y1, y2, y3,
    (strip y1), (y5 (strip y1) __), (stripDs y3), (y6 (stripDs y3) __))
  in
  let rec strip0 t0 =
    let f15 = fun y0 z -> f14 t0 y0 z in
    let f16 = fun z -> f13 t0 z in
    let f17 = fun y0 y1 y3 z -> f12 t0 y0 y1 y3 z in
    let f18 = fun y0 y1 y2 y4 y5 z -> f11 t0 y0 y1 y2 y4 y5 z in
    let f19 = fun y0 y1 y3 y5 z -> f10 t0 y0 y1 y3 y5 z in
    let f20 = fun y0 y1 y3 y4 y5 y6 y7 z -> f9 t0 y0 y1 y3 y4 y5 y6 y7 z in
    let f21 = fun y0 z -> f8 t0 y0 z in
    let f22 = fun y0 y1 y2 y3 z -> f7 t0 y0 y1 y2 y3 z in
    let f23 = fun y0 y1 y2 y4 y5 z -> f6 t0 y0 y1 y2 y4 y5 z in
    let f24 = fun y0 y1 y3 z -> f5 t0 y0 y1 y3 z in
    let f25 = fun y0 y1 y2 y3 y5 z -> f4 t0 y0 y1 y2 y3 y5 z in
    let f26 = fun y0 z -> f3 t0 y0 z in
    (match t0 with
     | Compile0.TRel n -> (fun z _ -> f15 n z)
     | Compile0.TProof -> (fun z _ -> f16 z)
     | Compile0.TLambda (n, t1) ->
       let f27 = fun y3 z -> f17 n t1 y3 z in
       let hrec = strip0 t1 in (fun z _ -> f27 hrec z)
     | Compile0.TLetIn (n, t1, t2) ->
       let f27 = fun y4 y5 z -> f18 n t1 t2 y4 y5 z in
       let f28 = let hrec = strip0 t1 in (fun y5 z _ -> f27 hrec y5 z) in
       let hrec = strip0 t2 in f28 hrec
     | Compile0.TApp (t1, t2) ->
       let f27 = fun y3 y5 z -> f19 t1 t2 y3 y5 z in
       let f28 = let hrec = strip0 t2 in (fun _ y5 z _ -> f27 hrec y5 z) in
       let f29 = fun _ -> let hrec = strip0 t1 in f28 __ hrec in
       let f30 = fun y3 y4 y5 y6 y7 z -> f20 t1 t2 y3 y4 y5 y6 y7 z in
       let f31 =
         let hrec = strip0 t2 in
         (fun y4 y5 y6 y7 _ z _ -> f30 hrec y4 y5 y6 y7 z)
       in
       (match coq_CanonicalP strip t1 (strip t2) with
        | Some p ->
          let (p0, n) = p in
          let (p1, n0) = p0 in let (t3, t4) = p1 in f31 t3 t4 n0 n __
        | None -> f29 __)
     | Compile0.TConst s -> (fun z _ -> f21 s z)
     | Compile0.TConstruct (i, n, n0, n1) -> (fun z _ -> f22 i n n0 n1 z)
     | Compile0.TCase (p, t1, b) ->
       let f27 = fun y4 y5 z -> f23 p t1 b y4 y5 z in
       let f28 = let hrec = strip0 t1 in (fun y5 z _ -> f27 hrec y5 z) in
       let hrec = stripBs0 b in f28 hrec
     | Compile0.TFix (d, n) ->
       let f27 = fun y3 z -> f24 d n y3 z in
       let hrec = stripDs0 d in (fun z _ -> f27 hrec z)
     | Compile0.TProj (p, t1) ->
       let (p0, n) = p in
       let (i, n0) = p0 in
       let f27 = fun y5 z -> f25 i n0 n t1 y5 z in
       let hrec = strip0 t1 in (fun z _ -> f27 hrec z)
     | Compile0.TWrong s -> (fun z _ -> f26 s z))
  and stripBs0 bs =
    let f15 = fun z -> f2 bs z in
    let f16 = fun y0 y1 y2 y4 y5 z -> f1 bs y0 y1 y2 y4 y5 z in
    (match bs with
     | Compile0.Coq_bnil -> (fun z _ -> f15 z)
     | Compile0.Coq_bcons (n, t0, b) ->
       let f17 = fun y4 y5 z -> f16 n t0 b y4 y5 z in
       let f18 = let hrec = strip0 t0 in (fun y5 z _ -> f17 hrec y5 z) in
       let hrec = stripBs0 b in f18 hrec)
  and stripDs0 ts =
    let f15 = fun z -> f0 ts z in
    let f16 = fun y0 y1 y2 y3 y5 y6 z -> f ts y0 y1 y2 y3 y5 y6 z in
    (match ts with
     | Compile0.Coq_dnil -> (fun z _ -> f15 z)
     | Compile0.Coq_dcons (n, t0, n0, d) ->
       let f17 = fun y5 y6 z -> f16 n t0 n0 d y5 y6 z in
       let f18 = let hrec = strip0 t0 in (fun y6 z _ -> f17 hrec y6 z) in
       let hrec = stripDs0 d in f18 hrec)
  in strip0 t _res __

(** val coq_R_stripBs_correct : coq_L1gBrs -> coq_Brs -> coq_R_stripBs **)

let coq_R_stripBs_correct bs _res =
  let f14 = fun y y0 _ -> R_strip_0 (y, y0) in
  let f13 = fun y _ -> R_strip_1 y in
  let f12 = fun y y0 y1 y3 _ -> R_strip_2 (y, y0, y1, (strip y1),
    (y3 (strip y1) __))
  in
  let f11 = fun y y0 y1 y2 y4 y5 _ -> R_strip_3 (y, y0, y1, y2, (strip y1),
    (y4 (strip y1) __), (strip y2), (y5 (strip y2) __))
  in
  let f10 = fun y y0 y1 y3 y5 _ -> R_strip_4 (y, y0, y1, (strip y1),
    (y3 (strip y1) __), (strip y0), (y5 (strip y0) __))
  in
  let f9 = fun y y0 y1 y3 y4 y5 y6 y7 _ -> R_strip_5 (y, y0, y1, (strip y1),
    (y3 (strip y1) __), y4, y5, y6, y7)
  in
  let f8 = fun y y0 _ -> R_strip_6 (y, y0) in
  let f7 = fun y y0 y1 y2 y3 _ -> R_strip_7 (y, y0, y1, y2, y3) in
  let f6 = fun y y0 y1 y2 y4 y5 _ -> R_strip_8 (y, y0, y1, y2, (strip y1),
    (y4 (strip y1) __), (stripBs y2), (y5 (stripBs y2) __))
  in
  let f5 = fun y y0 y1 y3 _ -> R_strip_9 (y, y0, y1, (stripDs y0),
    (y3 (stripDs y0) __))
  in
  let f4 = fun y y0 y1 y2 y3 y5 _ -> R_strip_10 (y, y0, y1, y2, y3,
    (strip y3), (y5 (strip y3) __))
  in
  let f3 = fun y y0 _ -> R_strip_11 (y, y0) in
  let f2 = fun y _ -> R_stripBs_0 y in
  let f1 = fun y y0 y1 y2 y4 y5 _ -> R_stripBs_1 (y, y0, y1, y2, (strip y1),
    (y4 (strip y1) __), (stripBs y2), (y5 (stripBs y2) __))
  in
  let f0 = fun y _ -> R_stripDs_0 y in
  let f = fun y y0 y1 y2 y3 y5 y6 _ -> R_stripDs_1 (y, y0, y1, y2, y3,
    (strip y1), (y5 (strip y1) __), (stripDs y3), (y6 (stripDs y3) __))
  in
  let rec strip0 t =
    let f15 = fun y0 z -> f14 t y0 z in
    let f16 = fun z -> f13 t z in
    let f17 = fun y0 y1 y3 z -> f12 t y0 y1 y3 z in
    let f18 = fun y0 y1 y2 y4 y5 z -> f11 t y0 y1 y2 y4 y5 z in
    let f19 = fun y0 y1 y3 y5 z -> f10 t y0 y1 y3 y5 z in
    let f20 = fun y0 y1 y3 y4 y5 y6 y7 z -> f9 t y0 y1 y3 y4 y5 y6 y7 z in
    let f21 = fun y0 z -> f8 t y0 z in
    let f22 = fun y0 y1 y2 y3 z -> f7 t y0 y1 y2 y3 z in
    let f23 = fun y0 y1 y2 y4 y5 z -> f6 t y0 y1 y2 y4 y5 z in
    let f24 = fun y0 y1 y3 z -> f5 t y0 y1 y3 z in
    let f25 = fun y0 y1 y2 y3 y5 z -> f4 t y0 y1 y2 y3 y5 z in
    let f26 = fun y0 z -> f3 t y0 z in
    (match t with
     | Compile0.TRel n -> (fun z _ -> f15 n z)
     | Compile0.TProof -> (fun z _ -> f16 z)
     | Compile0.TLambda (n, t0) ->
       let f27 = fun y3 z -> f17 n t0 y3 z in
       let hrec = strip0 t0 in (fun z _ -> f27 hrec z)
     | Compile0.TLetIn (n, t0, t1) ->
       let f27 = fun y4 y5 z -> f18 n t0 t1 y4 y5 z in
       let f28 = let hrec = strip0 t0 in (fun y5 z _ -> f27 hrec y5 z) in
       let hrec = strip0 t1 in f28 hrec
     | Compile0.TApp (t0, t1) ->
       let f27 = fun y3 y5 z -> f19 t0 t1 y3 y5 z in
       let f28 = let hrec = strip0 t1 in (fun _ y5 z _ -> f27 hrec y5 z) in
       let f29 = fun _ -> let hrec = strip0 t0 in f28 __ hrec in
       let f30 = fun y3 y4 y5 y6 y7 z -> f20 t0 t1 y3 y4 y5 y6 y7 z in
       let f31 =
         let hrec = strip0 t1 in
         (fun y4 y5 y6 y7 _ z _ -> f30 hrec y4 y5 y6 y7 z)
       in
       (match coq_CanonicalP strip t0 (strip t1) with
        | Some p ->
          let (p0, n) = p in
          let (p1, n0) = p0 in let (t2, t3) = p1 in f31 t2 t3 n0 n __
        | None -> f29 __)
     | Compile0.TConst s -> (fun z _ -> f21 s z)
     | Compile0.TConstruct (i, n, n0, n1) -> (fun z _ -> f22 i n n0 n1 z)
     | Compile0.TCase (p, t0, b) ->
       let f27 = fun y4 y5 z -> f23 p t0 b y4 y5 z in
       let f28 = let hrec = strip0 t0 in (fun y5 z _ -> f27 hrec y5 z) in
       let hrec = stripBs0 b in f28 hrec
     | Compile0.TFix (d, n) ->
       let f27 = fun y3 z -> f24 d n y3 z in
       let hrec = stripDs0 d in (fun z _ -> f27 hrec z)
     | Compile0.TProj (p, t0) ->
       let (p0, n) = p in
       let (i, n0) = p0 in
       let f27 = fun y5 z -> f25 i n0 n t0 y5 z in
       let hrec = strip0 t0 in (fun z _ -> f27 hrec z)
     | Compile0.TWrong s -> (fun z _ -> f26 s z))
  and stripBs0 bs0 =
    let f15 = fun z -> f2 bs0 z in
    let f16 = fun y0 y1 y2 y4 y5 z -> f1 bs0 y0 y1 y2 y4 y5 z in
    (match bs0 with
     | Compile0.Coq_bnil -> (fun z _ -> f15 z)
     | Compile0.Coq_bcons (n, t, b) ->
       let f17 = fun y4 y5 z -> f16 n t b y4 y5 z in
       let f18 = let hrec = strip0 t in (fun y5 z _ -> f17 hrec y5 z) in
       let hrec = stripBs0 b in f18 hrec)
  and stripDs0 ts =
    let f15 = fun z -> f0 ts z in
    let f16 = fun y0 y1 y2 y3 y5 y6 z -> f ts y0 y1 y2 y3 y5 y6 z in
    (match ts with
     | Compile0.Coq_dnil -> (fun z _ -> f15 z)
     | Compile0.Coq_dcons (n, t, n0, d) ->
       let f17 = fun y5 y6 z -> f16 n t n0 d y5 y6 z in
       let f18 = let hrec = strip0 t in (fun y6 z _ -> f17 hrec y6 z) in
       let hrec = stripDs0 d in f18 hrec)
  in stripBs0 bs _res __

(** val coq_R_stripDs_correct : coq_L1gDefs -> coq_Defs -> coq_R_stripDs **)

let coq_R_stripDs_correct ts _res =
  let f14 = fun y y0 _ -> R_strip_0 (y, y0) in
  let f13 = fun y _ -> R_strip_1 y in
  let f12 = fun y y0 y1 y3 _ -> R_strip_2 (y, y0, y1, (strip y1),
    (y3 (strip y1) __))
  in
  let f11 = fun y y0 y1 y2 y4 y5 _ -> R_strip_3 (y, y0, y1, y2, (strip y1),
    (y4 (strip y1) __), (strip y2), (y5 (strip y2) __))
  in
  let f10 = fun y y0 y1 y3 y5 _ -> R_strip_4 (y, y0, y1, (strip y1),
    (y3 (strip y1) __), (strip y0), (y5 (strip y0) __))
  in
  let f9 = fun y y0 y1 y3 y4 y5 y6 y7 _ -> R_strip_5 (y, y0, y1, (strip y1),
    (y3 (strip y1) __), y4, y5, y6, y7)
  in
  let f8 = fun y y0 _ -> R_strip_6 (y, y0) in
  let f7 = fun y y0 y1 y2 y3 _ -> R_strip_7 (y, y0, y1, y2, y3) in
  let f6 = fun y y0 y1 y2 y4 y5 _ -> R_strip_8 (y, y0, y1, y2, (strip y1),
    (y4 (strip y1) __), (stripBs y2), (y5 (stripBs y2) __))
  in
  let f5 = fun y y0 y1 y3 _ -> R_strip_9 (y, y0, y1, (stripDs y0),
    (y3 (stripDs y0) __))
  in
  let f4 = fun y y0 y1 y2 y3 y5 _ -> R_strip_10 (y, y0, y1, y2, y3,
    (strip y3), (y5 (strip y3) __))
  in
  let f3 = fun y y0 _ -> R_strip_11 (y, y0) in
  let f2 = fun y _ -> R_stripBs_0 y in
  let f1 = fun y y0 y1 y2 y4 y5 _ -> R_stripBs_1 (y, y0, y1, y2, (strip y1),
    (y4 (strip y1) __), (stripBs y2), (y5 (stripBs y2) __))
  in
  let f0 = fun y _ -> R_stripDs_0 y in
  let f = fun y y0 y1 y2 y3 y5 y6 _ -> R_stripDs_1 (y, y0, y1, y2, y3,
    (strip y1), (y5 (strip y1) __), (stripDs y3), (y6 (stripDs y3) __))
  in
  let rec strip0 t =
    let f15 = fun y0 z -> f14 t y0 z in
    let f16 = fun z -> f13 t z in
    let f17 = fun y0 y1 y3 z -> f12 t y0 y1 y3 z in
    let f18 = fun y0 y1 y2 y4 y5 z -> f11 t y0 y1 y2 y4 y5 z in
    let f19 = fun y0 y1 y3 y5 z -> f10 t y0 y1 y3 y5 z in
    let f20 = fun y0 y1 y3 y4 y5 y6 y7 z -> f9 t y0 y1 y3 y4 y5 y6 y7 z in
    let f21 = fun y0 z -> f8 t y0 z in
    let f22 = fun y0 y1 y2 y3 z -> f7 t y0 y1 y2 y3 z in
    let f23 = fun y0 y1 y2 y4 y5 z -> f6 t y0 y1 y2 y4 y5 z in
    let f24 = fun y0 y1 y3 z -> f5 t y0 y1 y3 z in
    let f25 = fun y0 y1 y2 y3 y5 z -> f4 t y0 y1 y2 y3 y5 z in
    let f26 = fun y0 z -> f3 t y0 z in
    (match t with
     | Compile0.TRel n -> (fun z _ -> f15 n z)
     | Compile0.TProof -> (fun z _ -> f16 z)
     | Compile0.TLambda (n, t0) ->
       let f27 = fun y3 z -> f17 n t0 y3 z in
       let hrec = strip0 t0 in (fun z _ -> f27 hrec z)
     | Compile0.TLetIn (n, t0, t1) ->
       let f27 = fun y4 y5 z -> f18 n t0 t1 y4 y5 z in
       let f28 = let hrec = strip0 t0 in (fun y5 z _ -> f27 hrec y5 z) in
       let hrec = strip0 t1 in f28 hrec
     | Compile0.TApp (t0, t1) ->
       let f27 = fun y3 y5 z -> f19 t0 t1 y3 y5 z in
       let f28 = let hrec = strip0 t1 in (fun _ y5 z _ -> f27 hrec y5 z) in
       let f29 = fun _ -> let hrec = strip0 t0 in f28 __ hrec in
       let f30 = fun y3 y4 y5 y6 y7 z -> f20 t0 t1 y3 y4 y5 y6 y7 z in
       let f31 =
         let hrec = strip0 t1 in
         (fun y4 y5 y6 y7 _ z _ -> f30 hrec y4 y5 y6 y7 z)
       in
       (match coq_CanonicalP strip t0 (strip t1) with
        | Some p ->
          let (p0, n) = p in
          let (p1, n0) = p0 in let (t2, t3) = p1 in f31 t2 t3 n0 n __
        | None -> f29 __)
     | Compile0.TConst s -> (fun z _ -> f21 s z)
     | Compile0.TConstruct (i, n, n0, n1) -> (fun z _ -> f22 i n n0 n1 z)
     | Compile0.TCase (p, t0, b) ->
       let f27 = fun y4 y5 z -> f23 p t0 b y4 y5 z in
       let f28 = let hrec = strip0 t0 in (fun y5 z _ -> f27 hrec y5 z) in
       let hrec = stripBs0 b in f28 hrec
     | Compile0.TFix (d, n) ->
       let f27 = fun y3 z -> f24 d n y3 z in
       let hrec = stripDs0 d in (fun z _ -> f27 hrec z)
     | Compile0.TProj (p, t0) ->
       let (p0, n) = p in
       let (i, n0) = p0 in
       let f27 = fun y5 z -> f25 i n0 n t0 y5 z in
       let hrec = strip0 t0 in (fun z _ -> f27 hrec z)
     | Compile0.TWrong s -> (fun z _ -> f26 s z))
  and stripBs0 bs =
    let f15 = fun z -> f2 bs z in
    let f16 = fun y0 y1 y2 y4 y5 z -> f1 bs y0 y1 y2 y4 y5 z in
    (match bs with
     | Compile0.Coq_bnil -> (fun z _ -> f15 z)
     | Compile0.Coq_bcons (n, t, b) ->
       let f17 = fun y4 y5 z -> f16 n t b y4 y5 z in
       let f18 = let hrec = strip0 t in (fun y5 z _ -> f17 hrec y5 z) in
       let hrec = stripBs0 b in f18 hrec)
  and stripDs0 ts0 =
    let f15 = fun z -> f0 ts0 z in
    let f16 = fun y0 y1 y2 y3 y5 y6 z -> f ts0 y0 y1 y2 y3 y5 y6 z in
    (match ts0 with
     | Compile0.Coq_dnil -> (fun z _ -> f15 z)
     | Compile0.Coq_dcons (n, t, n0, d) ->
       let f17 = fun y5 y6 z -> f16 n t n0 d y5 y6 z in
       let f18 = let hrec = strip0 t in (fun y6 z _ -> f17 hrec y6 z) in
       let hrec = stripDs0 d in f18 hrec)
  in stripDs0 ts _res __

(** val stripEC : coq_L1gEC -> coq_Term envClass **)

let stripEC = function
| Coq_ecTrm t -> Coq_ecTrm (strip t)
| Coq_ecTyp (_, itp) -> Coq_ecTyp (O, itp)

type coq_R_stripEC =
| R_stripEC_0 of coq_L1gEC * coq_L1gTerm
| R_stripEC_1 of coq_L1gEC * nat * itypPack

(** val coq_R_stripEC_rect :
    (coq_L1gEC -> coq_L1gTerm -> __ -> 'a1) -> (coq_L1gEC -> nat -> itypPack
    -> __ -> 'a1) -> coq_L1gEC -> coq_Term envClass -> coq_R_stripEC -> 'a1 **)

let coq_R_stripEC_rect f f0 _ _ = function
| R_stripEC_0 (x, x0) -> f x x0 __
| R_stripEC_1 (x, x0, x1) -> f0 x x0 x1 __

(** val coq_R_stripEC_rec :
    (coq_L1gEC -> coq_L1gTerm -> __ -> 'a1) -> (coq_L1gEC -> nat -> itypPack
    -> __ -> 'a1) -> coq_L1gEC -> coq_Term envClass -> coq_R_stripEC -> 'a1 **)

let coq_R_stripEC_rec f f0 _ _ = function
| R_stripEC_0 (x, x0) -> f x x0 __
| R_stripEC_1 (x, x0, x1) -> f0 x x0 x1 __

(** val stripEC_rect :
    (coq_L1gEC -> coq_L1gTerm -> __ -> 'a1) -> (coq_L1gEC -> nat -> itypPack
    -> __ -> 'a1) -> coq_L1gEC -> 'a1 **)

let stripEC_rect f0 f ec =
  let f1 = f0 ec in
  let f2 = f ec in
  (match ec with
   | Coq_ecTrm l -> f1 l __
   | Coq_ecTyp (n, i) -> f2 n i __)

(** val stripEC_rec :
    (coq_L1gEC -> coq_L1gTerm -> __ -> 'a1) -> (coq_L1gEC -> nat -> itypPack
    -> __ -> 'a1) -> coq_L1gEC -> 'a1 **)

let stripEC_rec =
  stripEC_rect

(** val coq_R_stripEC_correct :
    coq_L1gEC -> coq_Term envClass -> coq_R_stripEC **)

let coq_R_stripEC_correct ec _res =
  stripEC_rect (fun y y0 _ _ _ -> R_stripEC_0 (y, y0)) (fun y y0 y1 _ _ _ ->
    R_stripEC_1 (y, y0, y1)) ec _res __

(** val stripEnv : coq_L1gEnv -> coq_Term environ **)

let stripEnv =
  map (fun nmec -> ((fst nmec), (stripEC (snd nmec))))

(** val stripProgram : coq_L1gPgm -> coq_Term coq_Program **)

let stripProgram p =
  { main = (strip p.main); env = (stripEnv p.env) }

(** val program_Program : coq_Fuel -> program -> coq_Term coq_Program **)

let program_Program f p =
  stripProgram (program_Program f p)

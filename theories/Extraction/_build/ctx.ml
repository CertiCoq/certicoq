open Datatypes
open Cps

type exp_ctx =
| Hole_c
| Econstr_c of var * cTag * var list * exp_ctx
| Eproj_c of var * cTag * int * var * exp_ctx
| Eprim_c of var * prim * var list * exp_ctx
| Ecase_c of var * (cTag * exp) list * cTag * exp_ctx * (cTag * exp) list
| Efun1_c of fundefs * exp_ctx
| Efun2_c of fundefs_ctx * exp
and fundefs_ctx =
| Fcons1_c of var * cTag * var list * exp_ctx * fundefs
| Fcons2_c of var * cTag * var list * exp * fundefs_ctx

(** val app_ctx_f : exp_ctx -> exp -> exp **)

let rec app_ctx_f c e =
  match c with
  | Hole_c -> e
  | Econstr_c (x, t, ys, c0) -> Econstr (x, t, ys, (app_ctx_f c0 e))
  | Eproj_c (x, t, n, y, c0) -> Eproj (x, t, n, y, (app_ctx_f c0 e))
  | Eprim_c (x, f, ys, c0) -> Eprim (x, f, ys, (app_ctx_f c0 e))
  | Ecase_c (x, te, t, c0, te') ->
    Ecase (x, (app te ((t, (app_ctx_f c0 e)) :: te')))
  | Efun1_c (fds, c0) -> Efun (fds, (app_ctx_f c0 e))
  | Efun2_c (cfds, e') -> Efun ((app_f_ctx_f cfds e), e')

(** val app_f_ctx_f : fundefs_ctx -> exp -> fundefs **)

and app_f_ctx_f c e =
  match c with
  | Fcons1_c (f, t, ys, c0, fds) -> Fcons (f, t, ys, (app_ctx_f c0 e), fds)
  | Fcons2_c (f, t, ys, e', cfds) ->
    Fcons (f, t, ys, e', (app_f_ctx_f cfds e))

(** val comp_ctx_f : exp_ctx -> exp_ctx -> exp_ctx **)

let rec comp_ctx_f c1 c2 =
  match c1 with
  | Hole_c -> c2
  | Econstr_c (x, t, ys, c) -> Econstr_c (x, t, ys, (comp_ctx_f c c2))
  | Eproj_c (x, t, n, y, c) -> Eproj_c (x, t, n, y, (comp_ctx_f c c2))
  | Eprim_c (x, f, ys, c) -> Eprim_c (x, f, ys, (comp_ctx_f c c2))
  | Ecase_c (x, te, t, c, te') -> Ecase_c (x, te, t, (comp_ctx_f c c2), te')
  | Efun1_c (fds, c) -> Efun1_c (fds, (comp_ctx_f c c2))
  | Efun2_c (cfds, e') -> Efun2_c ((comp_f_ctx_f cfds c2), e')

(** val comp_f_ctx_f : fundefs_ctx -> exp_ctx -> fundefs_ctx **)

and comp_f_ctx_f c c2 =
  match c with
  | Fcons1_c (f, t, ys, c0, fds) ->
    Fcons1_c (f, t, ys, (comp_ctx_f c0 c2), fds)
  | Fcons2_c (f, t, ys, e', cfds) ->
    Fcons2_c (f, t, ys, e', (comp_f_ctx_f cfds c2))

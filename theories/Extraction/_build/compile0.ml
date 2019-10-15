open Ast0
open AstCommon
open BasicAst
open Datatypes
open EAst
open ETyping
open Extract
open List0
open PCUICChecker
open RandyPrelude
open String0
open TemplateToPCUIC
open ExceptionMonad
open UGraph0
open Utils

type coq_Term =
| TRel of nat
| TProof
| TLambda of name * coq_Term
| TLetIn of name * coq_Term * coq_Term
| TApp of coq_Term * coq_Term
| TConst of char list
| TConstruct of inductive * nat * nat * nat
| TCase of (inductive * nat) * coq_Term * coq_Brs
| TFix of coq_Defs * nat
| TProj of projection * coq_Term
| TWrong of char list
and coq_Brs =
| Coq_bnil
| Coq_bcons of nat * coq_Term * coq_Brs
and coq_Defs =
| Coq_dnil
| Coq_dcons of name * coq_Term * nat * coq_Defs

(** val defs_Defs : (term -> coq_Term) -> term def list -> coq_Defs **)

let rec defs_Defs term_Term0 = function
| [] -> Coq_dnil
| d :: ds0 ->
  Coq_dcons (d.dname, (term_Term0 d.dbody), d.rarg,
    (defs_Defs term_Term0 ds0))

(** val natterms_Brs : (term -> coq_Term) -> (nat * term) list -> coq_Brs **)

let rec natterms_Brs term_Term0 = function
| [] -> Coq_bnil
| p :: ds ->
  let (n, t) = p in
  Coq_bcons (n, (term_Term0 t), (natterms_Brs term_Term0 ds))

(** val print_global_declarations : global_declarations -> char list **)

let rec print_global_declarations = function
| [] -> '!'::[]
| g0 :: p ->
  (match g0 with
   | ConstantDecl (knm, _) -> append knm (print_global_declarations p)
   | InductiveDecl (knm, _) -> append knm (print_global_declarations p))

(** val coq_Cstr_npars_nargs :
    global_declarations -> inductive -> nat -> (nat * nat) coq_exception **)

let coq_Cstr_npars_nargs g ind ncst =
  let { inductive_mind = knm; inductive_ind = nbod } = ind in
  (match ETyping.lookup_env g knm with
   | Some g0 ->
     (match g0 with
      | ConstantDecl (_, _) ->
        raise
          ('C'::('s'::('t'::('r'::('_'::('n'::('p'::('a'::('r'::('s'::('_'::('n'::('a'::('r'::('g'::('s'::(':'::('l'::('o'::('o'::('k'::('u'::('p'::('_'::('e'::('n'::('v'::(' '::('C'::('o'::('n'::('s'::('t'::('a'::('n'::('t'::('D'::('e'::('c'::('l'::[]))))))))))))))))))))))))))))))))))))))))
      | InductiveDecl (_, m) ->
        let { ind_npars = npars; ind_bodies = bodies } = m in
        (match nth_error bodies nbod with
         | Some o ->
           let { ind_name = _; ind_type = _; ind_kelim = _; ind_ctors =
             ctors; ind_projs = _ } = o
           in
           (match nth_error ctors ncst with
            | Some p -> let (_, nargs) = p in ret (npars, nargs)
            | None ->
              raise
                ('C'::('s'::('t'::('r'::('_'::('n'::('p'::('a'::('r'::('s'::('_'::('n'::('a'::('r'::('g'::('s'::(':'::('n'::('t'::('h'::('_'::('e'::('r'::('r'::('o'::('r'::(' '::('c'::('t'::('o'::('r'::('s'::[])))))))))))))))))))))))))))))))))
         | None ->
           raise
             ('C'::('s'::('t'::('r'::('_'::('n'::('p'::('a'::('r'::('s'::('_'::('n'::('a'::('r'::('g'::('s'::(':'::('n'::('t'::('h'::('_'::('e'::('r'::('r'::('o'::('r'::(' '::('b'::('o'::('d'::('i'::('e'::('s'::[])))))))))))))))))))))))))))))))))))
   | None ->
     raise
       (append
         ('C'::('s'::('t'::('r'::('_'::('n'::('p'::('a'::('r'::('s'::('_'::('n'::('a'::('r'::('g'::('s'::(':'::('l'::('o'::('o'::('k'::('u'::('p'::('_'::('e'::('n'::('v'::(';'::(' '::[])))))))))))))))))))))))))))))
         (append knm
           (append (','::[])
             (append (nat_to_string nbod)
               (append (','::[])
                 (append (nat_to_string ncst)
                   (append ('/'::[]) (print_global_declarations g)))))))))

(** val term_Term : global_declarations -> term -> coq_Term **)

let rec term_Term g = function
| Coq_tBox -> TProof
| Coq_tRel n -> TRel n
| Coq_tLambda (nm, bod) -> TLambda (nm, (term_Term g bod))
| Coq_tLetIn (nm, dfn, bod) ->
  TLetIn (nm, (term_Term g dfn), (term_Term g bod))
| Coq_tApp (fn, arg) -> TApp ((term_Term g fn), (term_Term g arg))
| Coq_tConst pth ->
  (match ETyping.lookup_env g pth with
   | Some g0 ->
     (match g0 with
      | ConstantDecl (_, _) -> TConst pth
      | InductiveDecl (_, _) ->
        TWrong
          (append
            ('t'::('e'::('r'::('m'::('_'::('T'::('e'::('r'::('m'::(':'::('C'::('o'::('n'::('s'::('t'::(' '::('i'::('n'::('d'::('u'::('c'::('t'::('i'::('v'::('e'::(' '::('o'::('r'::(' '::('a'::('x'::('i'::('o'::('m'::(':'::(' '::[]))))))))))))))))))))))))))))))))))))
            pth))
   | None ->
     TWrong
       (append
         ('t'::('e'::('r'::('m'::('_'::('T'::('e'::('r'::('m'::(':'::('C'::('o'::('n'::('s'::('t'::(' '::('i'::('n'::('d'::('u'::('c'::('t'::('i'::('v'::('e'::(' '::('o'::('r'::(' '::('a'::('x'::('i'::('o'::('m'::(':'::(' '::[]))))))))))))))))))))))))))))))))))))
         pth))
| Coq_tConstruct (ind, ncst) ->
  (match coq_Cstr_npars_nargs g ind ncst with
   | Exc s ->
     TWrong
       (append
         ('t'::('e'::('r'::('m'::('_'::('T'::('e'::('r'::('m'::(';'::('t'::('C'::('o'::('n'::('s'::('t'::('r'::('u'::('c'::('t'::(':'::[])))))))))))))))))))))
         s)
   | Ret p -> let (npars, nargs) = p in TConstruct (ind, ncst, npars, nargs))
| Coq_tCase (npars, mch, brs) ->
  TCase (npars, (term_Term g mch), (natterms_Brs (term_Term g) brs))
| Coq_tProj (prj, bod) -> TProj (prj, (term_Term g bod))
| Coq_tFix (defs, m) -> TFix ((defs_Defs (term_Term g) defs), m)
| _ ->
  TWrong
    ('('::('t'::('e'::('r'::('m'::('_'::('T'::('e'::('r'::('m'::(':'::('U'::('n'::('k'::('n'::('o'::('w'::('n'::(')'::[])))))))))))))))))))

(** val trans_global_decl :
    global_declarations -> global_decl -> char list * coq_Term envClass **)

let trans_global_decl g = function
| ConstantDecl (nm, cb) ->
  (match cb.cst_body with
   | Some t -> (nm, (Coq_ecTrm (term_Term g t)))
   | None -> (nm, ecAx))
| InductiveDecl (nm, mib) ->
  let ibs = ibodies_itypPack mib.ind_bodies in
  (nm, (Coq_ecTyp (mib.ind_npars, ibs)))

(** val program_Pgm_aux : global_declarations -> coq_Term environ **)

let rec program_Pgm_aux = function
| [] -> []
| gd :: g0 -> (trans_global_decl g0 gd) :: (program_Pgm_aux g0)

(** val program_Program : coq_Fuel -> Ast0.program -> coq_Term coq_Program **)

let program_Program f = function
| (genv, t) ->
  let gc = (genv, init_graph) in
  let genv' = trans_global gc in
  let genv'' = extract_global f genv' in
  let t' = extract f genv' [] (trans t) in
  (match genv'' with
   | Checked genv''' ->
     (match t' with
      | Checked t''' ->
        { main = (term_Term genv''' t'''); env =
          (program_Pgm_aux (rev genv''')) }
      | TypeError _ ->
        { main = (TWrong
          ('p'::('r'::('o'::('g'::('r'::('a'::('m'::('_'::('P'::('r'::('o'::('g'::('r'::('a'::('m'::[]))))))))))))))));
          env = [] })
   | TypeError _ ->
     { main = (TWrong
       ('p'::('r'::('o'::('g'::('r'::('a'::('m'::('_'::('P'::('r'::('o'::('g'::('r'::('a'::('m'::[]))))))))))))))));
       env = [] })

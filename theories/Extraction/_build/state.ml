open BasicAst
open BinNat
open BinPos
open Datatypes
open List_util
open Monad0
open MonadState
open StateMonad
open Cps
open Cps_show
open Cps_util

let __ = let rec f _ = Obj.repr f in Obj.repr f

type comp_data = { next_var : var; nect_cTag : cTag; next_iTag : iTag;
                   next_fTag : fTag; cenv : cEnv; fenv : fEnv;
                   name_env : Cps_show.nEnv; log : char list list }

(** val cenv : comp_data -> cEnv **)

let cenv x = x.cenv

(** val fenv : comp_data -> fEnv **)

let fenv x = x.fenv

(** val name_env : comp_data -> Cps_show.nEnv **)

let name_env x = x.name_env

type ('s, 't) compM = (comp_data * 's, 't) state

(** val get_name_env : unit -> ('a1, Cps_show.nEnv) compM **)

let get_name_env _ =
  pbind (coq_PMonad_Monad (Obj.magic coq_Monad_state)) (Obj.magic __)
    (Obj.magic coq_MonadState_state).get (fun s ->
    ret (Obj.magic coq_Monad_state) (fst s).name_env)

(** val get_name : var -> char list -> ('a1, var) compM **)

let get_name old_var suff =
  pbind (coq_PMonad_Monad (Obj.magic coq_Monad_state)) (Obj.magic __)
    (Obj.magic coq_MonadState_state).get (fun p ->
    let (y, st) = p in
    let { next_var = n; nect_cTag = c; next_iTag = i; next_fTag = f; cenv =
      e; fenv = fenv0; name_env = names; log = log0 } = y
    in
    let names' = add_entry names n old_var suff in
    pbind (coq_PMonad_Monad (Obj.magic coq_Monad_state)) (Obj.magic __)
      ((Obj.magic coq_MonadState_state).put ({ next_var = (Pos.add n 1);
        nect_cTag = c; next_iTag = i; next_fTag = f; cenv = e; fenv = fenv0;
        name_env = names'; log = log0 }, st)) (fun _ ->
      ret (Obj.magic coq_Monad_state) n))

(** val get_names_lst : var list -> char list -> ('a1, var list) compM **)

let rec get_names_lst old suff =
  match old with
  | [] -> ret (Obj.magic coq_Monad_state) []
  | o :: os ->
    pbind (coq_PMonad_Monad (Obj.magic coq_Monad_state)) (Obj.magic __)
      (Obj.magic get_name o suff) (fun x ->
      pbind (coq_PMonad_Monad (Obj.magic coq_Monad_state)) (Obj.magic __)
        (get_names_lst os suff) (fun xs ->
        ret (Obj.magic coq_Monad_state) (x :: xs)))

(** val get_name_no_suff : char list -> ('a1, var) compM **)

let get_name_no_suff name =
  pbind (coq_PMonad_Monad (Obj.magic coq_Monad_state)) (Obj.magic __)
    (Obj.magic coq_MonadState_state).get (fun p ->
    let (y, st) = p in
    let { next_var = n; nect_cTag = c; next_iTag = i; next_fTag = f; cenv =
      e; fenv = fenv0; name_env = names; log = log0 } = y
    in
    let names' = add_entry_str names n name in
    pbind (coq_PMonad_Monad (Obj.magic coq_Monad_state)) (Obj.magic __)
      ((Obj.magic coq_MonadState_state).put ({ next_var = (Pos.add n 1);
        nect_cTag = c; next_iTag = i; next_fTag = f; cenv = e; fenv = fenv0;
        name_env = names'; log = log0 }, st)) (fun _ ->
      ret (Obj.magic coq_Monad_state) n))

(** val make_record_cTag : int -> ('a1, cTag) compM **)

let make_record_cTag n =
  pbind (coq_PMonad_Monad (Obj.magic coq_Monad_state)) (Obj.magic __)
    (Obj.magic coq_MonadState_state).get (fun p ->
    let (y, st) = p in
    let { next_var = x; nect_cTag = c; next_iTag = i; next_fTag = f; cenv =
      e; fenv = fenv0; name_env = names; log = log0 } = y
    in
    let inf = ((((Coq_nAnon, Coq_nAnon), i), n), 0) in
    let e' = M.set c inf e in
    pbind (coq_PMonad_Monad (Obj.magic coq_Monad_state)) (Obj.magic __)
      ((Obj.magic coq_MonadState_state).put ({ next_var = x; nect_cTag =
        (Pos.add c 1); next_iTag = (Pos.add i 1); next_fTag = f; cenv = e';
        fenv = fenv0; name_env = names; log = log0 }, st)) (fun _ ->
      ret (Obj.magic coq_Monad_state) c))

(** val register_record_cTag : cTag -> iTag -> int -> ('a1, unit) compM **)

let register_record_cTag _ _ n =
  pbind (coq_PMonad_Monad (Obj.magic coq_Monad_state)) (Obj.magic __)
    (Obj.magic coq_MonadState_state).get (fun p ->
    let (y, st) = p in
    let { next_var = x; nect_cTag = c; next_iTag = i; next_fTag = f; cenv =
      e; fenv = fenv0; name_env = names; log = log0 } = y
    in
    let inf = ((((Coq_nAnon, Coq_nAnon), i), n), 0) in
    let e' = M.set c inf e in
    (Obj.magic coq_MonadState_state).put ({ next_var = x; nect_cTag = c;
      next_iTag = i; next_fTag = f; cenv = e'; fenv = fenv0; name_env =
      names; log = log0 }, st))

(** val get_pp_name : var -> ('a1, char list) compM **)

let get_pp_name x =
  pbind (coq_PMonad_Monad (Obj.magic coq_Monad_state)) (Obj.magic __)
    (Obj.magic get_name_env ()) (fun nenv ->
    ret (Obj.magic coq_Monad_state) (show_tree (show_var nenv x)))

(** val get_pp_names_list : var list -> ('a1, char list list) compM **)

let rec get_pp_names_list = function
| [] -> ret (Obj.magic coq_Monad_state) []
| x :: xs0 ->
  pbind (coq_PMonad_Monad (Obj.magic coq_Monad_state)) (Obj.magic __)
    (Obj.magic get_pp_name x) (fun x' ->
    pbind (coq_PMonad_Monad (Obj.magic coq_Monad_state)) (Obj.magic __)
      (get_pp_names_list xs0) (fun xs' ->
      ret (Obj.magic coq_Monad_state) (x' :: xs')))

(** val log_msg : char list -> ('a1, unit) compM **)

let log_msg msg =
  pbind (coq_PMonad_Monad (Obj.magic coq_Monad_state)) (Obj.magic __)
    (Obj.magic coq_MonadState_state).get (fun s ->
    let (y, st) = s in
    let { next_var = x; nect_cTag = c; next_iTag = i; next_fTag = f; cenv =
      e; fenv = fenv0; name_env = names; log = log0 } = y
    in
    (Obj.magic coq_MonadState_state).put ({ next_var = x; nect_cTag = c;
      next_iTag = i; next_fTag = f; cenv = e; fenv = fenv0; name_env = names;
      log = (msg :: log0) }, st))

(** val chr_newline : char **)

let chr_newline =
  '\n'

(** val newline : char list **)

let newline =
  chr_newline::[]

(** val get_state : unit -> ('a1, 'a1) compM **)

let get_state _ =
  pbind (coq_PMonad_Monad (Obj.magic coq_Monad_state)) (Obj.magic __)
    (Obj.magic coq_MonadState_state).get (fun s ->
    ret (Obj.magic coq_Monad_state) (snd s))

(** val put_state : 'a1 -> ('a1, unit) compM **)

let put_state st =
  pbind (coq_PMonad_Monad (Obj.magic coq_Monad_state)) (Obj.magic __)
    (Obj.magic coq_MonadState_state).get (fun s ->
    (Obj.magic coq_MonadState_state).put ((fst s), st))

(** val get_ftag : int -> ('a1, fTag) compM **)

let get_ftag arity =
  pbind (coq_PMonad_Monad (Obj.magic coq_Monad_state)) (Obj.magic __)
    (Obj.magic coq_MonadState_state).get (fun p ->
    let (y, st) = p in
    let { next_var = x; nect_cTag = c; next_iTag = i; next_fTag = f; cenv =
      e; fenv = fenv0; name_env = names; log = log0 } = y
    in
    pbind (coq_PMonad_Monad (Obj.magic coq_Monad_state)) (Obj.magic __)
      ((Obj.magic coq_MonadState_state).put ({ next_var = x; nect_cTag = c;
        next_iTag = i; next_fTag = (Pos.add f 1); cenv = e; fenv =
        (M.set f (arity, (fromN 0 (N.to_nat arity))) fenv0); name_env =
        names; log = log0 }, st)) (fun _ -> ret (Obj.magic coq_Monad_state) f))

(** val run_compM :
    ('a1, 'a2) compM -> comp_data -> 'a1 -> 'a2 * (comp_data * 'a1) **)

let run_compM m st s =
  runState m (st, s)

(** val pack_data :
    var -> cTag -> iTag -> fTag -> cEnv -> fEnv -> Cps_show.nEnv -> char list
    list -> comp_data **)

let pack_data x x0 x1 x2 x3 x4 x5 x6 =
  { next_var = x; nect_cTag = x0; next_iTag = x1; next_fTag = x2; cenv = x3;
    fenv = x4; name_env = x5; log = x6 }

Require Import L6.cps L6.cps_util L6.set_util L6.identifiers L6.ctx
        L6.List_util L6.functions L6.cps_show.
Require Import Coq.ZArith.Znumtheory.
Require Import Coq.Lists.List Coq.MSets.MSets Coq.MSets.MSetRBT Coq.Numbers.BinNums
        Coq.NArith.BinNat Coq.PArith.BinPos Coq.Strings.String Coq.Strings.Ascii.
Require Import Common.AstCommon.
Require Import ExtLib.Structures.Monads ExtLib.Data.Monads.StateMonad.

Import ListNotations Nnat MonadNotation.

Require Import compcert.lib.Maps.

Open Scope monad_scope.
Open Scope string.

(** *  Unified state for L6 transformations *)
(* Takes care of fresh names for binders, types and constructors, the original name environment,
   and debugging utils *)

Section CompM.
  Context {S : Type}. (* Transformation-specific state *) 
  
  Record comp_data : Type :=  mkCompData { next_var : var;
                                           nect_cTag : cTag;
                                           next_iTag : iTag;
                                           next_fTag : fTag;
                                           cenv : cEnv;
                                           fenv : fEnv; (* Maps fTag's to (number of args,  list (arg no)) *)
                                           name_env : nEnv;
                                           log : list string }.

  Definition compM := state (comp_data * S).

  (* Get the environment name *)
  Definition get_name_env (_ : unit) : compM nEnv :=
    s <- get ;;
    ret (name_env (fst s)).

  (** Get a fresh name, and register a pretty name by appending a suffix to the pretty name of the old var *)
  Definition get_name (old_var : var) (suff : string) : compM var :=
    p <- get ;;
    let '(mkCompData n c i f e fenv names log, st) := p in  
    let names' := add_entry names n old_var suff in  
    put (mkCompData ((n+1)%positive) c i f e fenv names' log, st) ;;
        ret n.

  Fixpoint get_names_lst (old : list var) (suff : string) : compM (list var) :=
    match old with
    | [] => ret []
    | o :: os =>
      x <- get_name o suff ;;
      xs <- get_names_lst os suff ;;
      ret (x :: xs)
    end.

  (** Get a fresh name, and create a new pretty name *)
  Definition get_name_no_suff (name : string) : compM var :=
    p <- get ;;
    let '(mkCompData n c i f e fenv names log, st) := p in
    let names' := add_entry_str names n name in
    put (mkCompData ((n+1)%positive) c i f e fenv names' log, st) ;;
    ret n.

  (* Get the next fresh record tag of a fresh type *)
  Definition make_record_cTag (n : N) : compM cTag :=
    p <- get ;; 
    let '(mkCompData x c i f e fenv names log, st) := p  in
    let inf := (nAnon, nAnon,  i, n, 0%N) : cTyInfo in
    let e' := ((M.set c inf e) : cEnv) in
    put (mkCompData x (c+1)%positive (i+1)%positive f e' fenv names log, st) ;;
    ret c.

  (* Register a constructor tag of some type i *)
  Definition register_record_cTag (c : cTag) (i : iTag) (n : N) : compM unit :=
    p <- get ;; 
    let '(mkCompData x c i f e fenv names log, st) := p  in
    let inf := (nAnon, nAnon,  i, n, 0%N) : cTyInfo in
    let e' := ((M.set c inf e) : cEnv) in
    put (mkCompData x c i f e' fenv names log, st).

  (* Get the pretty name of a binder *)
  Definition get_pp_name (x : var) : compM string :=
    nenv <- get_name_env tt ;;
    ret (show_tree (show_var nenv x)).

  (* Get the pretty name of a list of binders *)
  Fixpoint get_pp_names_list (xs : list var) : compM (list string) :=
    match xs with
    | [] => ret []
    | x :: xs => 
      x' <- get_pp_name x ;;
      xs' <- get_pp_names_list xs ;;
      ret (x' :: xs')
    end.

  (* Log a new message *)
  Definition log_msg (msg : string) : compM unit :=
    s <- get ;;
    let '(mkCompData x c i f e fenv names log, st) := s in
    put (mkCompData x c i f e fenv names (msg :: log)%string, st).

  Definition chr_newline : ascii := Eval compute in ascii_of_nat 10.
  Definition newline : string := (String chr_newline EmptyString).

  Definition log_to_string (log : list string) : string :=
    (concat newline ("Debug messages" :: (List.rev log)))%string.

  (* Access the transformation specific state *)
  Definition get_state (_ : unit) : compM S :=
    s <- get ;;
    ret (snd s).

  (* Access the transformation specific state *)
  Definition put_state (st : S) : compM unit :=
    s <- get ;;
    put (fst s, st).

  (** Get a fresh function tag and register it in fEnv *)
  Definition get_ftag (arity : N) : compM fTag :=
    p <- get ;;
    let '(mkCompData x c i f e fenv names log, st) := p in
    put (mkCompData x c i (f + 1)%positive e (M.set f (arity, (fromN (0%N) (BinNat.N.to_nat arity))) fenv) names log, st) ;;
    ret f.

  
  Definition run_compM {A} (m: compM A) (st : comp_data) (s : S) : A * (comp_data * S) :=
    let '(a, st) := runState m (st, s) in
    (a, st).

  Definition pack_data := mkCompData.

  (* Returns the name environment and the log *)
  Definition get_result (d : comp_data) : nEnv * string := (name_env d, log_to_string (log d)).  

End CompM.

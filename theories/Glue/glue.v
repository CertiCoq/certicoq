Require Import Common.Pipeline_utils.

Require Import Coq.ZArith.ZArith
               Coq.Program.Basics
               Coq.Strings.String
               Coq.Lists.List List_util.

Require Import ExtLib.Structures.Monads
               ExtLib.Data.Monads.OptionMonad
               ExtLib.Data.Monads.StateMonad
               ExtLib.Data.String.

From MetaCoq.Template Require Import BasicAst.
Require MetaCoq.Template.All.

Require Import compcert.common.AST
               compcert.common.Errors
               compcert.lib.Integers
               compcert.cfrontend.Cop
               compcert.cfrontend.Ctypes
               compcert.cfrontend.Clight
               compcert.common.Values.

Require Import L6.cps
               L6.identifiers.

Require Import Clightdefs.
Require Import L6.cps_show.
Require Import L6_to_Clight.


Import MonadNotation.
Open Scope monad_scope.

Definition main_ident : positive := 1.

Notation "'var' x" := (Etempvar x val) (at level 20).

Notation " p ';;;' q " := (Ssequence p q)
                          (at level 100, format " p ';;;' '//' q ").

Notation "'*' p " := (Ederef p val) (at level 40).

Notation "'[' t ']' e " := (Ecast e t) (at level 34).

Notation "'Field(' t ',' n ')'" :=
  ( *(add ([valPtr] t) (c_int n%Z val))) (at level 36). (* what is the type of int being added? *)


(* aliases for Clight AST types *)
Definition def : Type := ident * globdef fundef type.
Definition defs : Type := list def.

(* A record that holds L1 information about Coq types. *)
Record ty_info : Type :=
  Build_ty_info
    { ty_name   : kername
    ; ty_body   : Ast.one_inductive_body
    ; ty_params : list string
    }.

(* A record that holds information about Coq constructors.
   This may be redesigned in the future to hold info about
   the [dissected_type] etc, like a one-stop shop for constructors? *)
Record ctor_info : Type :=
  Build_ctor_info
    { ctor_name    : BasicAst.ident
    ; ctor_arity   : nat
    ; ctor_ordinal : nat
    }.

(* An enumeration of L1 types.
   This is separate from the [ind_tag] values generated in L6.
   These are generated only for gluing purposes.
   There is no good reason for this, except for easier plumbing. *)
Definition ind_L1_tag : Type := positive.
Definition ind_L1_env : Type := M.t ty_info.

(* Matches [ind_L1_tag]s to a [ident] (i.e. [positive]) that holds
   the name of the get_tag_... function in C. *)
Definition get_tag_env : Type := M.t ident.

(* Matches [ind_L1_tag]s to a [ident] (i.e. [positive]) that holds
   the name and type of the names array in C. *)
Definition ctor_names_env : Type := M.t (ident * type).

(* An enumeration of constructors in a type starting from 1.
   Should preserve the ordering of the ctors in the original Coq definition.
   Should coincide with the index the glue functions return.
   But that index should start from 0, while this one starts from 1. *)
Definition ctor_L1_index : Type := positive.

(* Matches [ind_L1_tag]s to another map matching [ctor_L1_index]
   to the [Struct] type and the accessor function name (like "get_S_args")
   associated with that constructor.
   In practice, this is like a 2D dictionary. *)
Definition ctor_arg_accessor_env : Type := M.t (M.t (type * ident)).

(* Matches [ind_L1_tag]s to a [ident] (i.e. [positive]) that holds
   the name of the print function in C. *)
Definition print_env : Type := M.t ident.

(* A Clight ident and a Clight type packed together *)
Definition def_info : Type := positive * type.

Section Helpers.

  (* printf, is_ptr and these literals will be used by multiple functions
     so we want to reuse them, not redefine every time.
     Hence we keep references to them in this "toolbox".
   *)

  Record toolbox_info : Type :=
    Build_toolbox_info
      { printf_info : def_info
      ; is_ptr_info : def_info
      ; lparen_info : def_info
      ; rparen_info : def_info
      ; space_info  : def_info
      ; fun'_info   : def_info
      ; type'_info  : def_info
      ; unk_info    : def_info
      ; prop_info   : def_info
      ; get_unboxed_ordinal_info : def_info
      ; get_boxed_ordinal_info   : def_info
      }.

  (* Enumerate items starting from 0. *)
  Definition enumerate_nat {a : Type} (xs : list a) : list (nat * a) :=
    let fix aux (n : nat) (xs : list a) :=
          match xs with
          | nil => nil
          | x :: xs => (n, x) :: aux (S n) xs
          end
    in aux O xs.

  (* Enumerate items starting from 1, because that's the smallest [positive]. *)
  Definition enumerate_pos {a : Type} (xs : list a) : list (positive * a) :=
    let fix aux (n : positive) (xs : list a) :=
          match xs with
          | nil => nil
          | x :: xs => (n, x) :: aux (Pos.succ n) xs
          end
    in aux 1%positive xs.

  (* Lookup in a 2D dictionary. *)
  Definition get_2d {A : Type} (k1 k2 : positive) (m : M.t (M.t A)) : option A :=
    match M.get k1 m with
    | None => None
    | Some m2 => M.get k2 m2
    end.

  (* Insertion in a 2D dictionary. *)
  Definition set_2d {A : Type}
             (k1 k2 : positive) (v : A) (m : M.t (M.t A)) : M.t (M.t A) :=
    let sub_map := match M.get k1 m with
                   | None => M.empty A
                   | Some m2 => m2
                   end
    in M.set k1 (M.set k2 v sub_map) m.

End Helpers.

Section Ctor_Info.

Variant ctor_box : Type := unboxed | boxed.

(* Can be used [if unbox_check c then ... else ...] *)
Definition unbox_check (ctor : BasicAst.ident * Ast.term * nat) : ctor_box :=
  let '(_, _, arity) := ctor in
  match arity with
  | O => unboxed
  | S _ => boxed
  end.

(* A function to calculate the ordinals of a type's constructors. *)
Definition process_ctors
           (ctors : list (BasicAst.ident * Ast.term * nat)) : list ctor_info :=
  let fix aux
          (unboxed_count : nat)
          (boxed_count : nat)
          (ctors : list (BasicAst.ident * Ast.term * nat)) : list ctor_info :=
    match ctors with
    | nil => nil
    | (name, _, ar) :: ctors' =>
      let '(ord, rest) :=
          match ar with
          | O   => (unboxed_count, aux (S unboxed_count) boxed_count ctors')
          | S _ => (boxed_count, aux unboxed_count (S boxed_count) ctors')
          end
      in
        {| ctor_name := name
         ; ctor_arity := ar
         ; ctor_ordinal := ord
         |} :: rest
    end
  in aux O O ctors.

End Ctor_Info.

(* A state monad for the glue code generation *)
Section GState.

  Record gstate_data : Type :=
    Build_gstate_data
      { gstate_gensym : ident
      ; gstate_ienv   : ind_L1_env
      ; gstate_nenv   : name_env
      ; gstate_gtenv  : get_tag_env
      ; gstate_cnenv  : ctor_names_env
      ; gstate_caaenv : ctor_arg_accessor_env
      ; gstate_penv   : print_env
      ; gstate_log    : list string
      }.

  Definition gState : Type -> Type := StateMonad.state gstate_data.

  (* generate fresh [ident] and record it to the [name_env]
     with the given [string] *)
  Definition gensym (s : string) : gState ident :=
    '(Build_gstate_data n ienv nenv gtenv cnenv caaenv penv log) <- get ;;
    let nenv := M.set n (nNamed s) nenv in
    put (Build_gstate_data ((n+1)%positive) ienv nenv gtenv cnenv caaenv penv log) ;;
    ret n.

  Definition set_print_env (k : ind_L1_tag) (v : ident) : gState unit :=
    '(Build_gstate_data n ienv nenv gtenv cnenv caaenv penv log) <- get ;;
    let penv := M.set k v penv in
    put (Build_gstate_data n ienv nenv gtenv cnenv caaenv penv log).

  Definition get_print_env (k : ind_L1_tag) : gState (option ident) :=
    penv <- gets gstate_penv ;;
    ret (M.get k penv).

  Definition set_get_tag_env (k : ind_L1_tag) (v : ident) : gState unit :=
    '(Build_gstate_data n ienv nenv gtenv cnenv caaenv penv log) <- get ;;
    let gtenv := M.set k v gtenv in
    put (Build_gstate_data n ienv nenv gtenv cnenv caaenv penv log).

  Definition get_get_tag_env (k : ind_L1_tag) : gState (option ident) :=
    gtenv <- gets gstate_gtenv ;;
    ret (M.get k gtenv).

  Definition get_ctor_names_env (k : ind_L1_tag) : gState (option (ident * type)) :=
    cnenv <- gets gstate_cnenv ;;
    ret (M.get k cnenv).

  Definition set_ctor_names_env (k : ind_L1_tag) (v : ident * type) : gState unit :=
    '(Build_gstate_data n ienv nenv gtenv cnenv caaenv penv log) <- get ;;
    let cnenv := M.set k v cnenv in
    put (Build_gstate_data n ienv nenv gtenv cnenv caaenv penv log).

  Definition get_ctor_arg_accessor_env
             (k1 : ind_L1_tag) (k2: ctor_L1_index)
             : gState (option (type * ident)) :=
    caaenv <- gets gstate_caaenv ;;
    ret (get_2d k1 k2 caaenv).

  Definition set_ctor_arg_accessor_env
             (k1 : ind_L1_tag) (k2 : ctor_L1_index) (v : type * ident) : gState unit :=
    '(Build_gstate_data n ienv nenv gtenv cnenv caaenv penv log) <- get ;;
    let caaenv := set_2d k1 k2 v caaenv in
    put (Build_gstate_data n ienv nenv gtenv cnenv caaenv penv log).

  Definition get_ind_L1_env (k : ind_L1_tag) : gState (option ty_info) :=
    ienv <- gets gstate_ienv ;;
    ret (M.get k ienv).

  (* A hacky way to get the [ind_L1_tag] of a type from its name.
     This is necessary because of a shortcoming of Template Coq.
     (mutually recursive type names aren't fully qualified) *)
  Definition get_tag_from_type_name (s : kername) : gState (option ind_L1_tag) :=
    let find (prev : option ind_L1_tag)
             (tag : ind_L1_tag)
             (info : ty_info) : option ind_L1_tag :=
      match prev with
      | None => if string_dec s (ty_name info) then Some tag else None
      | _ => prev
      end in
    ienv <- gets gstate_ienv ;;
    ret (M.fold find ienv None).

  Definition put_ind_L1_env (ienv : ind_L1_env) : gState unit :=
    '(Build_gstate_data n _ nenv gtenv cnenv caaenv penv log) <- get ;;
    put (Build_gstate_data n ienv nenv gtenv cnenv caaenv penv log).

  (* logs are appended to the list and the list is reversed
     at the end to keep them in chronological order *)
  Definition log (s : string) : gState unit :=
    '(Build_gstate_data n ienv nenv gtenv cnenv caaenv penv log) <- get ;;
    put (Build_gstate_data n ienv nenv gtenv cnenv caaenv penv (s :: log)).

End GState.

Section Externs.

  (* Converts Coq string to Clight array *)
  Fixpoint string_as_array (s : string) : list init_data :=
    match s with
    | EmptyString => Init_int8 Int.zero :: nil
    | String c s' =>
        Init_int8 (Int.repr (Z.of_N (N_of_ascii c))) :: string_as_array s'
    end.

  (* Creates a global variable with a string literal constant *)
  Definition string_literal (name : string) (literal : string)
            : gState (ident * type * globdef fundef type) :=
    ident <- gensym name ;;
    let len := String.length literal in
    let init := string_as_array literal in
    let ty := tarray tschar (Z.of_nat (S len)) in
    let gv := Gvar (mkglobvar ty init true false) in
    ret (ident, ty, gv).

  Definition ty_printf : type :=
    Tfunction (Tcons (tptr tschar) Tnil) tint cc_default.

  Definition get_unboxed_ordinal : gState def :=
    gname <- gensym "get_unboxed_ordinal" ;;
    _v <- gensym "v" ;;
    ret (gname,
         Gfun (Internal
                 {| fn_return := tuint
                  ; fn_callconv := cc_default
                  ; fn_params := (_v, val) :: nil
                  ; fn_vars := nil
                  ; fn_temps := nil
                  ; fn_body := (Sreturn (Some (Ebinop Oshr (var _v) (make_cint 1 val) val)))
                  |})).

  Definition get_boxed_ordinal : gState def :=
    gname <- gensym "get_boxed_ordinal" ;;
    _v <- gensym "v" ;;
    ret (gname,
         Gfun (Internal
                 {| fn_return := tuint
                  ; fn_callconv := cc_default
                  ; fn_params := (_v, val) :: nil
                  ; fn_vars := nil
                  ; fn_temps := nil
                  ; fn_body :=
                      (Sreturn (Some (Ebinop Oand (Field(var _v, -1)) (make_cint 255 val) val)))
                  |})).

  Definition make_externs : gState (defs * toolbox_info) :=
    '(_lparen, ty_lparen, def_lparen) <- string_literal "lparen_lit" "(" ;;
    '(_rparen, ty_rparen, def_rparen) <- string_literal "rparen_lit" ")" ;;
    '(_space,  ty_space,  def_space)  <- string_literal "space_lit"  " " ;;
    '(_fun',   ty_fun',   def_fun')   <- string_literal "fun_lit"    "<fun>" ;;
    '(_type',  ty_type',  def_type')  <- string_literal "type_lit"   "<type>" ;;
    '(_unk,    ty_unk,    def_unk)    <- string_literal "unk_lit"    "<unk>" ;;
    '(_prop,   ty_prop,   def_prop)   <- string_literal "prop_lit"   "<prop>" ;;
    _printf <- gensym "printf" ;;
    _is_ptr <- gensym "is_ptr" ;;
    '(_guo, def_guo) <- get_unboxed_ordinal ;;
    '(_gbo, def_gbo) <- get_boxed_ordinal ;;

    let toolbox :=
        {| printf_info :=
              (_printf, Tfunction (Tcons (tptr tschar) Tnil) tint cc_default)
         ; is_ptr_info :=
              (_is_ptr, Tfunction (Tcons val Tnil) tbool cc_default)
         ; lparen_info := (_lparen, ty_lparen)
         ; rparen_info := (_rparen, ty_rparen)
         ; space_info  := (_space,  ty_space)
         ; fun'_info   := (_fun',   ty_fun')
         ; type'_info  := (_type',  ty_type')
         ; unk_info    := (_unk,    ty_unk)
         ; prop_info   := (_prop,   ty_prop)
         ; get_unboxed_ordinal_info :=
              (_guo, Tfunction (Tcons val Tnil) tuint cc_default)
         ; get_boxed_ordinal_info :=
              (_gbo, Tfunction (Tcons val Tnil) tuint cc_default)
         |} in
    let dfs :=
      ((_lparen, def_lparen) ::
       (_rparen, def_rparen) ::
       (_space, def_space) ::
       (_fun', def_fun') ::
       (_type', def_type') ::
       (_unk, def_unk) ::
       (_prop, def_prop) ::
       (_printf,
        Gfun (External (EF_external "printf"
                          (mksignature (AST.Tint :: nil)
                                       (Some AST.Tint)
                                       cc_default))
                        (Tcons (tptr tschar) Tnil) tint cc_default)) ::
       (_is_ptr,
         Gfun (External (EF_external "is_ptr"
                          (mksignature (val_typ :: nil) None cc_default))
                        (Tcons val Tnil)
                        (Tint IBool Unsigned noattr) cc_default)) ::
       (_guo, def_guo) ::
       (_gbo, def_gbo) ::
       nil) in
    ret (dfs, toolbox).

End Externs.

Section L1Types.

  Fixpoint get_max_ctor_arity
          (ctors : list (BasicAst.ident * Ast.term * nat)) : nat :=
    match ctors with
    | nil => 0
    | (_, _, arity) :: ctors' =>
        max arity (get_max_ctor_arity ctors')
    end.

  Fixpoint split_aux (acc : string) (sep : ascii) (s : string) : list string :=
    match s with
    | EmptyString => acc :: nil
    | String c s' =>
        if Char.ascii_dec sep c
          then acc :: split_aux EmptyString sep s'
          else split_aux (acc ++ String c EmptyString) sep s'
    end.

  Definition split (c : ascii) (s : string) : list string :=
    split_aux EmptyString c s.

 Definition qualifying_prefix := string.
 Definition base_name := string.
 Definition sanitized_name := string.

 (* takes a fully qualified name and removes the base name,
    leaving behind the qualifying prefix.
    e.g. "Coq.Init.Datatypes.bool" becomes "Coq.Init.Datatypes." *)
  Definition find_qualifying_prefix (n : kername) : qualifying_prefix :=
    match rev (split "." n) with
    | nil => (* not possible *) ""%string
    | base :: rest => String.concat "." (rev (""%string :: rest))
    end.

 (* takes a fully qualified name and gives the base name *)
  Definition find_base_name (n : kername) : base_name :=
    match rev (split "." n) with
    | nil => (* not possible *) ""%string
    | base :: rest => base
    end.

  (* Takes in "M1.M2.tau" and returns "M1_M2_tau". *)
  Definition sanitize_qualified (n : kername) : sanitized_name :=
    String.concat "_" (split "." n).

  (* takes an inductive type declaration and returns
     the qualifying prefix for the name and the type definition *)
  Definition extract_mut_ind
            (name : kername)
            (g : Ast.global_decl)
            : option (qualifying_prefix * Ast.mutual_inductive_body) :=
    match g with
    | Ast.InductiveDecl body => Some (find_qualifying_prefix name, body)
    | _ => None
    end.

  Definition context_names (ctx : Ast.context) : list string :=
    map (fun d => match Ast.decl_name d with
                  | nNamed x => x
                  | _ => ""%string (* TODO error handling *)
                  end) ctx.

  Fixpoint get_single_types
           (gs : Ast.global_env)
           : list ty_info :=
    match gs with
    | nil => nil
    | (name, g) :: gs' =>
      match extract_mut_ind name g with
      | Some (qual_pre, b) =>
          (* This relies on the assumption that mutually recursive types
             must exist in the same namespace. So if we only have one of them
             fully qualified, then we can apply the same qualification to
             the other types in the mut rec type declaration.
             Type names in one_inductive_body are NOT qualified,
             which makes them globally nonunique. *)
        let tys := map (fun o =>
                          {| ty_name := (qual_pre ++ Ast.ind_name o)%string
                           ; ty_body := o
                           ; ty_params := context_names (rev (Ast.ind_params b))
                           |}) (Ast.ind_bodies b) in
          tys ++ get_single_types gs'
      | None => get_single_types gs'
      end
    end.

  (* Generates the initial ind_L1_env *)
  Definition propagate_types
             (gs : Ast.global_env)
             : gState (list (ind_L1_tag * ty_info)) :=
    let singles := get_single_types gs in
    let res := enumerate_pos singles in
    let ienv : ind_L1_env := set_list res (M.empty _) in
    put_ind_L1_env ienv ;;
    ret res.

  (* Checks is the type in question is of sort [Prop]. *)
  Definition is_prop_type (info : ty_info) : bool :=
    let fix check_last (e : Ast.term) : bool :=
        match e with
          | Ast.tProd _ _ e' => check_last e'
          (* | Ast.tSort (utils.NEL.sing (Universes.Level.lProp, _)) => true *)
          | Ast.tSort u =>
              (String.eqb (AstUtils.string_of_sort u) ("[Prop]"%string))
               (* hacky but there's a module issue if you try to do it right *)
          | _ => false
        end
    in let check_elims (l : list Universes.sort_family) : bool :=
        match l with
        | _ :: nil => true (* hacky but the only case with 1 elt is Prop *)
        | _ => false
        end
   in orb (check_last (Ast.ind_type (ty_body info)))
          (check_elims (Ast.ind_kelim (ty_body info))).

  (* Takes in a list of types and removes the ones that are of sort [Prop].
     [Set] and [Type] are fine. CertiCoq erases [Prop]s early on,
     so no glue code is needed for those types. *)
  Fixpoint filter_prop_types
           (l : list (ind_L1_tag * ty_info)) : gState (list (ind_L1_tag * ty_info)) :=
    match l with
    | nil => ret nil
    | (itag, info) :: xs =>
      if is_prop_type info
      then
        log ("Skipping type of sort Prop: " ++ ty_name info) ;;
        filter_prop_types xs
      else
        log ("Including type: " ++ ty_name info) ;;
        rest <- filter_prop_types xs ;;
        ret ((itag, info) :: rest)
    end.

End L1Types.

Section L1Constructors.

  Inductive dissected_type :=
  | dInd : string -> dissected_type
  | dApp : dissected_type -> list dissected_type -> dissected_type
  | dFun : dissected_type (* for higher-order arguments to constructor *)
  | dParam : string -> dissected_type (* for argument of the parametrized types *)
  | dSort : dissected_type (* for type arguments to the ctor *)
  | dInvalid : dissected_type (* used for variables that could not be found *).

  (* Get nth type from the [dissected_type] context.
     Used for when n is a De Bruijn index. *)
  Definition get_from_ctx (ctx : list dissected_type) (n : nat) : dissected_type :=
    nth_default dInvalid ctx n.

  Fixpoint dissect_type
         (* type context, required to be able to resolve De Bruijn indices *)
           (ctx : list dissected_type)
         (* a simple component of constructor type *)
           (ty : Ast.term)
         (* the dissected type component (not the full type) *)
           : dissected_type :=
    match ty with
    | Ast.tRel n => get_from_ctx ctx n
    | Ast.tInd kn _ => dInd (inductive_mind kn)
    | Ast.tProd _ e1 e2 => dFun
    | Ast.tSort _ => dSort
    | Ast.tApp hd args =>
        dApp (dissect_type ctx hd) (map (dissect_type ctx) args)
    | _ => dInvalid
    end.

  Definition for_ctx (d : dissected_type) : dissected_type :=
    match d with
    | dSort => dInvalid
    | _ => d
    end.

  Fixpoint dissect_types
         (* number of parameters in the type *)
           (params : list string)
         (* context of types for De Bruijn indices in the type *)
           (ctx : list dissected_type)
         (* the type of the constructor that will be dissected *)
           (ty : Ast.term)
         (* a list of arguments and the return type *)
           : list dissected_type * dissected_type :=
    match ty, params with
    (* Parameters have to be named!
       Ideally we'd print an error message otherwise. *)
    | Ast.tProd (nNamed x) e1 e2, _ :: p' =>
        dissect_types p' (dParam x :: ctx) e2
    | Ast.tProd _ e1 e2, nil =>
        let e1' := dissect_type ctx e1 in
        let (args, rt) := dissect_types params (for_ctx e1' :: ctx) e2 in
        (e1' :: args, rt)
    | _, _ => (nil, dissect_type ctx ty)
    end.

  (*
  Import Template.Ast.

  Definition change := tProd nAnon
                          (tProd nAnon
                            (tInd
                                {|
                                inductive_mind := "Coq.Init.Datatypes.nat";
                                inductive_ind := 0 |} nil)
                            (tRel 1))
                          (tRel 1).
  Eval compute in (dissect_types 0 (dInd "Top.color" :: nil) change).

  Definition c := tProd (nNamed "a"%string)
                    (tSort ((Level.Level "Top.43", false) :: nil))
                    (tProd nAnon (tRel 0) (tRel 2)).
  Eval compute in (dissect_types 0 (dInd "Top.test" :: nil) c).

  Definition s := tProd nAnon (tRel 0) (tRel 1).
  Eval compute in (dissect_types 0 (dInd "Coq.Init.Datatypes.nat" :: nil) s).

  Definition no := tProd (nNamed "a"%string)
                     (tSort ((Level.Level "Top.40", false) :: nil))
                     (tProd nAnon (tRel 0)
                         (tProd nAnon (tApp (tRel 2) (tRel 1 :: nil))
                           (tProd nAnon (tApp (tRel 3) (tRel 2 :: nil))
                               (tApp (tRel 4) (tRel 3 :: nil))))).
  Eval compute in (dissect_types 1 (dInd "Top.tree" :: nil) no).
  *)

End L1Constructors.

Section Printers.
  (* We need a preliminary pass to generate the names for all
    printer functions for each type because they can be mutually recursive. *)
  Fixpoint make_printer_names
          (tys : list (ind_L1_tag * ty_info))
          : gState unit :=
    match tys with
    | nil => ret tt
    | (tag, {| ty_name := kn ; ty_body := ty |}) :: tys' =>
        pname <- gensym ("print_" ++ sanitize_qualified kn) ;;
        set_print_env tag pname ;;
        make_printer_names tys'
    end.

  Fixpoint gen_param_fun_names (params : list string) : gState (list (string * ident)) :=
    match params with
    | nil => ret nil
    | x :: xs =>
        x' <- gensym ("print_param_" ++ x) ;;
        xs' <- gen_param_fun_names xs ;;
        ret ((x, x') :: xs')
    end.

  Fixpoint find_param_fun_name
           (param : string) (params : list (string * ident)) : option ident :=
    match params with
    | nil => None
    | (s, i) :: xs =>
        if string_dec param s
          then Some i
          else find_param_fun_name param xs
    end.

  (* FIXME currently we assume all print functions have the same type,
     but that's not correct.
     Print functions for parametrized types take > 1 arguments. *)
  Definition ty_printer : type := Tfunction (Tcons val Tnil) tvoid cc_default.

  (* Takes a spine of the type that is about to be printed,
     and returns the correct list of printer functions for it,
     some of which may be the parameters of the type *)
  Fixpoint spine_to_args
           (spine : list dissected_type)
           (params : list (string * ident)) : gState (option (list expr)) :=
    match spine with
    | nil => ret (Some nil)
    | dParam p :: spine' =>
        match find_param_fun_name p params with
        | None => ret None
        | Some i =>
            rest <- spine_to_args spine' params ;;
            match rest with
            | None => ret None
            | Some rest' => ret (Some ((Evar i ty_printer) :: rest'))
            end
        end
    | dInd arg_type_name :: spine' =>
        (* We check [arg_type_name] against fully qualified [kername]s
           like "Coq.Init.Datatypes.nat". We should only use [kername]s
           since they're globally unique. *)
        tagM <- get_tag_from_type_name arg_type_name ;;
        match tagM with
        | None => ret None
        | Some tag =>
            printerM <- get_print_env tag ;;
            match printerM with
            | None =>
                log ("Can't find printer for the spine type " ++ arg_type_name) ;;
                ret None
            | Some printer => (* success! *)
                rest <- spine_to_args spine' params ;;
                match rest with
                | None => ret None
                | Some rest' => ret (Some ((Evar printer ty_printer) :: rest'))
                end
            end
        end
    | _ :: _ => ret None
    end.

  Variable toolbox : toolbox_info.

  Definition generate_printer
             (info : ind_L1_tag * ty_info)
            : gState (option def) :=
    let '(itag, {| ty_name := name ; ty_body := b ; ty_params := params |}) := info in
    let basename := Ast.ind_name b in
    let ctors := Ast.ind_ctors b in
    pnameM <- get_print_env itag ;;
    gtnameM <- get_get_tag_env itag ;;
    cnnameM <- get_ctor_names_env itag ;;
    iM <- get_ind_L1_env itag ;;
    match pnameM, gtnameM, cnnameM, iM with
    | Some pname (* name of the current print function *),
      Some gtname (* name of the elim function this will use *),
      Some (cnname, ty_names) (* name of the names array this will use *),
      Some iinfo (* L1 info about the inductive type *) =>
        _v <- gensym "v" ;;
        _tag <- gensym "tag" ;;
        _args <- gensym "args" ;;
        param_table <- gen_param_fun_names params ;;

        (* We need the maximum arity of all the ctors because
          we will declare an array for the arguments of the constructor
          of the resulting value from the eliminator *)
        let max_ctor_arity : nat := get_max_ctor_arity (Ast.ind_ctors b) in

        (* if none of the constructors take any args *)
        let won't_take_args : bool := Nat.eqb max_ctor_arity 0 in

        (* names and Clight types of printf and string literals *)
        let (_printf, ty_printf) := printf_info toolbox in
        let (_space, ty_space) := space_info toolbox in
        let (_lparen, ty_lparen) := lparen_info toolbox in
        let (_rparen, ty_rparen) := rparen_info toolbox in
        let (_fun, ty_fun) := fun'_info toolbox in
        let (_type, ty_type) := type'_info toolbox in
        let (_unk, ty_unk) := unk_info toolbox in
        let (_prop, ty_prop) := prop_info toolbox in

        (* function calls to printf *)
        let print_ctor_name : statement :=
          Scall None
            (Evar _printf ty_printf)
            ((Ederef
                (Ebinop Oadd
                  (Evar cnname ty_names)
                  (Evar _tag tint) ty_names)
                ty_names) :: nil) in
        let print_lparen : statement :=
            Scall None (Evar _printf ty_printf)
                       (Evar _lparen ty_lparen :: nil) in
        let print_rparen : statement :=
            Scall None (Evar _printf ty_printf)
                       (Evar _rparen ty_rparen :: nil) in
        let print_space : statement :=
            Scall None (Evar _printf ty_printf)
                       (Evar _space ty_space :: nil) in
        let print_unk : statement :=
            Scall None (Evar _printf ty_printf)
                       (Evar _unk ty_unk :: nil) in
        let print_prop : statement :=
            Scall None (Evar _printf ty_printf)
                       (Evar _prop ty_prop :: nil) in

        (* Generates a single function call to a printer with the right argument type *)
        let rec_print_call
            (arg : nat * dissected_type) : gState statement :=
          match arg with
          | (_, dFun) =>
              ret (Scall None (Evar _printf ty_printf)
                              (Evar _fun ty_fun :: nil))
          | (_, dInvalid) =>
              ret print_unk
          | (_, dSort) =>
              ret (Scall None (Evar _printf ty_printf)
                              (Evar _type ty_type :: nil))
          | (i, dParam p) =>
              match find_param_fun_name p param_table with
              | None =>
                  log ("Found an unexpected param " ++ p ++ " for type " ++ name) ;;
                  ret print_unk
              | Some fn_name =>
                  ret (Scall None (Evar fn_name ty_printer)
                          (Ederef
                              (Ebinop Oadd
                                      (Ecast
                                        (Evar _args (tptr tvoid))
                                        (tptr val))
                                      (Econst_int (Int.repr (Z.of_nat i)) val)
                                      (tptr val)) val :: nil))
              end
          | (i, dApp (dInd arg_type_name) _ as dt) (* for indexed/polymorphic types *)
          | (i, dInd arg_type_name as dt) (* for monomorphic types *) =>
              (* in order to get the disjunctive pattern work
                 we need a separate match to get the spine *)
              let spine := match dt with dApp _ s => s | _ => nil end in
              (* We check [arg_type_name] against fully qualified [kername]s
                 like "Coq.Init.Datatypes.nat". We should only use [kername]s
                 since they're globally unique. *)
              tagM <- get_tag_from_type_name arg_type_name ;;
              match tagM with
              | None =>
                  log ("No L1 tag for the type " ++ name ++
                       " for the #" ++ show_nat i ++
                       " constructor that takes " ++ arg_type_name) ;;
                  ret Sskip (* ideally shouldn't happen *)
              | Some tag =>
                  infoM <- get_ind_L1_env tag ;;
                  match infoM with
                  | None =>
                      log ("Can't find info for the type " ++ name ++
                           " in recursive call") ;;
                      ret Sskip
                  | Some info =>
                      if is_prop_type info
                      then ret print_prop
                      else
                        spineM <- spine_to_args spine param_table ;;
                        printerM <- get_print_env tag ;;
                        match spineM, printerM with
                        | None , _ =>
                            log ("Couldn't create spine application for the type " ++ name ++
                                " for the #" ++ show_nat i ++
                                " constructor that takes " ++ arg_type_name) ;;
                            ret Sskip (* ideally shouldn't happen *)
                        | _ , None =>
                            log ("Can't find printer for the type " ++ name) ;;
                            ret Sskip
                        | Some spine_args , Some printer =>
                            let spine_args := (* taking in only the parameters *)
                                firstn (length (ty_params info)) spine_args in
                            ret (Scall None (Evar printer ty_printer) (* FIXME wrong type *)
                                  (Ederef
                                      (Ebinop Oadd
                                              (Ecast
                                                (Evar _args (tptr tvoid))
                                                (tptr val))
                                              (Econst_int (Int.repr (Z.of_nat i)) val)
                                              (tptr val)) val :: spine_args))
                        end
                  end
             end
          | _ => (* TODO expand this for other cases *)
              log ("Found a non-inductive constructor argument for " ++ name) ;;
              ret print_unk
          end in

        (* Generates function calls to printers with the right argument types *)
        let fix rec_print_calls
                (args : list (nat * dissected_type))
                : gState statement :=
          match args with
          | nil => ret Sskip
          | arg :: nil => (* to handle the separator *)
              rec_print_call arg
          | arg :: args' =>
              rest <- rec_print_calls args' ;;
              call <- rec_print_call arg ;;
              ret (call ;;; print_space ;;; rest)
          end in

        (* Generates cases for the switch statement in the print function *)
        let fix switch_cases
                (ctors : list (ctor_L1_index * (BasicAst.ident * Ast.term * nat)))
                : gState labeled_statements :=
          match ctors with
          | nil => ret LSnil
          | (ctag, (_, ty, arity)) :: ctors' =>
            let (args, rt) := dissect_types params (dInd name :: nil) ty in
            calls <- rec_print_calls (enumerate_nat args) ;;
            rest <- switch_cases ctors' ;;
            accM <- get_ctor_arg_accessor_env itag ctag ;;
            match accM with
            | Some (ty_acc, _acc) =>
                ret (LScons (Some (Zpos ctag - 1)%Z)
                      (if Nat.eqb arity 0
                        then print_ctor_name ;;; Sbreak
                        else
                          Scall (Some _args) (Evar _acc ty_acc)
                                (Evar _v val :: nil) ;;;
                          print_lparen ;;;
                          print_ctor_name ;;;
                          print_space ;;;
                          calls ;;;
                          print_rparen ;;;
                          Sbreak)
                      rest)
            | None =>
                log ("Cannot find ctor arg accessor function for ctor #" ++ show_nat (Pos.to_nat ctag)) ;;
                ret LSnil (* TODO handle this better *)
            end
          end in

        entire_switch <- switch_cases (enumerate_pos ctors) ;;
        let body :=
          Scall (Some _tag)
             (Evar gtname (Tfunction (Tcons val Tnil) tuint cc_default))
             ((Etempvar _v val) :: nil) ;;;
          (if won't_take_args
            then print_ctor_name
            else Sswitch (Evar _tag val) entire_switch) in


        (* declare an args array if any of the constructors take args,
          if not then prodArr will not be declared at all *)
        let vars : list (ident * type) :=
            if won't_take_args then nil
            else (_args, tptr tvoid) :: nil in

        (* to handle polymorphic data types *)
        let param_pairs : list (ident * type) :=
            map (fun p => let '(_, i) := p in (i, ty_printer)) param_table in

        let f := {| fn_return := tvoid
                  ; fn_callconv := cc_default
                  ; fn_params := (_v, val) :: param_pairs
                  ; fn_vars := (_tag, tuint) :: vars
                  ; fn_temps := nil
                  ; fn_body := body
                |} in
        ret (Some (pname, Gfun (Internal f)))

    (* pnameM, gtnameM, cnnameM, iM *)
    | None, _, _, _ =>
        log ("No print function name for " ++ name ++ ".") ;; ret None
    | _, None, _, _ =>
        log ("No get_tag_... function name for " ++ name ++ ".") ;; ret None
    | _, _, None, _ =>
        log ("No constructor names array name for " ++ name ++ ".") ;; ret None
    | _, _, _, None =>
        log ("No L1 info for the inductive type  " ++ name ++ ".") ;; ret None
    end.

  Fixpoint generate_printers
          (tys : list (ind_L1_tag * ty_info))
          : gState defs :=
    match tys with
    | nil => ret nil
    | ty :: tys' =>
        rest <- generate_printers tys' ;;
        def <- generate_printer ty ;;
        match def with
        | Some def => ret (def :: rest)
        | None => ret rest
        end
    end.

End Printers.

Section CtorArrays.

  (* Pad a list by adding zeros to the end, to reach a list length of n. *)
  Definition pad_char_init (l : list init_data) (n : nat) : list init_data :=
    l ++ List.repeat (Init_int8 Int.zero) (n - (length l)).

  Fixpoint normalized_names_array
           (ctors : list (BasicAst.ident * Ast.term * nat))
           (n : nat) : nat * list init_data :=
    match ctors with
    | nil => (n, Init_space 0 :: nil)
             (* This may cause a warning in some C compilers.
                This is a hacky solution for that for now. *)
    | (s, _, _) :: ctors' =>
        let (max_len, init_l) :=
          normalized_names_array ctors' (max n (String.length s + 1)) in
        let i := pad_char_init (string_as_array s) max_len in
        (max_len, i ++ init_l)
    end.

  Fixpoint make_name_array
           (tag : ind_L1_tag)
           (kn : kername)
           (ctors : list (BasicAst.ident * Ast.term * nat))
           : gState def :=
    let (max_len, init_l) := normalized_names_array ctors 1 in
    let ty := tarray (tarray tschar (Z.of_nat max_len))
                     (Z.of_nat (length ctors)) in
    nname <- gensym ("names_of_" ++ sanitize_qualified kn) ;;
    set_ctor_names_env tag (nname, ty) ;;
    ret (nname, Gvar (mkglobvar ty init_l true false)).

  Fixpoint make_name_arrays
           (tys : list (ind_L1_tag * ty_info))
           : gState defs :=
    match tys with
    | nil => ret nil
    | (tag, {| ty_name := kn; ty_body := b |}) :: tys' =>
        rest <- make_name_arrays tys' ;;
        def <- make_name_array tag kn (Ast.ind_ctors b) ;;
        ret (def :: rest)
    end.

End CtorArrays.

Section ArgsStructs.

  Fixpoint members_from_ctor
           (qp : qualifying_prefix)
           (name : BasicAst.ident)
           (i : nat) (* initially 0 *)
           (j : nat) (* initially the arity *)
           : gState members :=
    match j with
    | O => ret nil
    | S j' =>
        arg_name <- gensym (sanitize_qualified (qp ++ name)%string ++ "_args_" ++ show_nat i) ;;
        rest <- members_from_ctor qp name (i + 1) j' ;;
        ret ((arg_name, val) :: rest)
    end.

  Fixpoint args_structs_from_ctors
          (itag : ind_L1_tag)
          (qp : qualifying_prefix)
          (ctors : list (ctor_L1_index * (BasicAst.ident * Ast.term * nat)))
          : gState (list (composite_definition * def)) :=
    match ctors with
    | nil => ret nil
    | (ctag, ctor) :: ctors' =>
        let '(name, ty, arity) := ctor in
        let sn := sanitize_qualified (qp ++ name)%string in
        _struct <- gensym (sn ++ "_args") ;;
        mems <- members_from_ctor qp name 0 arity ;;
        let comp := Composite _struct Struct mems noattr in


        aname <- gensym ("get_" ++ sn ++ "_args") ;;
        _v <- gensym "v" ;;
        let tstruct := Tpointer (Tstruct _struct noattr) noattr in
        let null := Ecast (Econst_int (Int.repr 0) val) tstruct in
        let e :=
            if unbox_check ctor
            then Econst_int (Int.repr 0) val (* null pointer for unboxed *)
            else Evar _v val in
        let body := Sreturn (Some (Ecast e tstruct)) in
        let f := (aname,
                  Gfun (Internal
                          {| fn_return := tstruct
                           ; fn_callconv := cc_default
                           ; fn_params := (_v, val) :: nil
                           ; fn_vars := nil
                           ; fn_temps := nil
                           ; fn_body := body
                           |})) in

        set_ctor_arg_accessor_env itag ctag (tstruct, aname) ;;
        rest <- args_structs_from_ctors itag qp ctors' ;;
        ret ((comp, f) :: rest)
    end.

  Fixpoint args_structs_from_types
          (tys : list (ind_L1_tag * ty_info))
          : gState (list (composite_definition * def)) :=
    match tys with
    | nil => ret nil
    | (itag, {| ty_body := ty ; ty_name := kn |}) :: tys' =>
        let qp := find_qualifying_prefix kn in
        s' <- args_structs_from_ctors itag qp (enumerate_pos (Ast.ind_ctors ty)) ;;
        rest <- args_structs_from_types tys' ;;
        ret (app s' rest)
    end.

End ArgsStructs.

Section CtorEnumTag.
  Variable toolbox : toolbox_info.

  Fixpoint match_ordinals_with_tag
           (ctors : list (BasicAst.ident * Ast.TemplateTerm.term * nat))
           (boxed unboxed total : nat)
           : list (nat * nat) * list (nat * nat) :=
    match ctors with
    | nil => (nil, nil)
    | ctor :: ctors' =>
        if unbox_check ctor
        then
          let (bs, us) := match_ordinals_with_tag ctors' boxed (S unboxed) (S total) in
          (bs, (unboxed, total) :: us)
        else
          let (bs, us) := match_ordinals_with_tag ctors' (S boxed) unboxed (S total) in
          ((boxed, total) :: bs, us)
    end.

  Fixpoint matches_to_LS
           (pairs : list (nat * nat)) : labeled_statements :=
    match pairs with
    | nil => LSnil
    | (ordinal, tag) :: pairs' =>
      LScons (Some (Z.of_nat ordinal))
             (Sreturn (Some (Econst_int (Int.repr (Z.of_nat tag)) tuint)))
             (matches_to_LS pairs')
    end.

  Fixpoint get_enum_tag_from_types
          (tys : list (ind_L1_tag * ty_info))
          : gState defs :=
    match tys with
    | nil => ret nil
    | (itag, {| ty_name := kn ; ty_body := one |}) :: tys' =>
        _b <- gensym "b" ;;
        _t <- gensym "t" ;;
        _v <- gensym "v" ;;
        let (_is_ptr, ty_is_ptr) := is_ptr_info toolbox in
        let (_guo, ty_guo) := get_unboxed_ordinal_info toolbox in
        let (_gbo, ty_gbo) := get_boxed_ordinal_info toolbox in
        let (boxed, unboxed) := match_ordinals_with_tag (Ast.ind_ctors one) 0 0 0 in
        let (vars, body) := match boxed, unboxed with
          | nil, nil => (* if there are no constructors, just return 0 *)
             (nil, Sreturn (Some (Econst_int (Int.repr 0) tuint)))
          | nil, _ => (* if all ctors are unboxed, then just call get_unboxed_ordinal *)
             ((_t, tuint) :: nil,
              Scall (Some _t) (Evar _guo ty_guo) (Evar _v val :: nil) ;;;
              Sreturn (Some (Evar _t tuint)))
          | _, nil => (* if all ctors are unboxed, then just call get_boxed_ordinal *)
             ((_t, tuint) :: nil,
              Scall (Some _t) (Evar _gbo ty_gbo) (Evar _v val :: nil) ;;;
              Sreturn (Some (Evar _t tuint)))
          | _, _ => (* if there are boxed and unboxed constructors, then if and switch *)
            let body :=
              Scall (Some _b) (Evar _is_ptr ty_is_ptr) (Evar _v val :: nil) ;;;
              Sifthenelse
                (Evar _b tbool)
                (Scall (Some _t) (Evar _gbo ty_gbo) (Evar _v val :: nil) ;;;
                Sswitch (Evar _t tuint) (matches_to_LS boxed))
                (Scall (Some _t) (Evar _guo ty_guo) (Evar _v val :: nil) ;;;
                Sswitch (Evar _t tuint) (matches_to_LS unboxed))
            in ((_b, tbool) :: (_t, tuint) :: nil, body)
          end in
        gname <- gensym ("get_" ++ sanitize_qualified kn ++ "_tag") ;;
        let f := (gname,
                  Gfun (Internal
                          {| fn_return := tuint
                          ; fn_callconv := cc_default
                          ; fn_params := (_v, val) :: nil
                          ; fn_vars := vars
                          ; fn_temps := nil
                          ; fn_body := body
                          |})) in
        set_get_tag_env itag gname ;;
        rest <- get_enum_tag_from_types tys' ;;
        ret (f :: rest)
    end.

End CtorEnumTag.

Section CConstructors.

  Fixpoint make_arg_list'
           (n : nat) : gState (list (ident * type)) :=
    match n with
    | O => ret nil
    | S n' =>
        new_id <- gensym ("arg" ++ nat2string10 n')%string ;;
        rest_id <- make_arg_list' n' ;;
        ret ((new_id, val) :: rest_id)
    end.

  Definition make_arg_list
             (n : nat) : gState (list (ident * type)) :=
    rest <- make_arg_list' n ;;
    ret (rev rest).

  Fixpoint constructors_from_ctors
          (name_ty : kername) (* like bool or nat *)
          (ctors : list ctor_info) (* name, arity, ordinal *)
          : gState defs :=
    let make_name (cname : string) : string :=
      ("make_" ++ sanitize_qualified name_ty ++ "_" ++ cname)%string in
    match ctors with
    | nil => ret nil
    | (* Unboxed *) {| ctor_name := cname ; ctor_arity := O ; ctor_ordinal := ord |} :: ctors =>
        constr_fun_id <- gensym (make_name cname) ;;
        let body :=
          Sreturn (Some (Econst_int (Int.repr (Z.add (Z.shiftl (Z.of_nat ord) 1) 1)) val)) in
        let f := (constr_fun_id,
                  Gfun (Internal
                          {| fn_return := val
                           ; fn_callconv := cc_default
                           ; fn_params := nil
                           ; fn_vars := nil
                           ; fn_temps := nil
                           ; fn_body := body
                           |})) in
        rest <- constructors_from_ctors name_ty ctors ;;
        ret (f :: rest)
    | (* Boxed *) {| ctor_name := cname ; ctor_arity := ar ; ctor_ordinal := ord |} :: ctors =>
        constr_fun_id <- gensym (make_name cname) ;;
        argv_ident <- gensym "argv" ;;
        arg_list <- make_arg_list ar ;;
        let asgn_s := make_constrAsgn argv_ident arg_list in (* TODO move this fn from L6_to_Clight to here*)
        let header := c_int ((Z.shiftl (Z.of_nat ar) 10) + (Z.of_nat ord)) val in
        let body :=
            Sassign (Field(var argv_ident, 0%Z)) header ;;;
            asgn_s ;;;
            Sreturn (Some (add (Evar argv_ident argvTy) (c_int 1%Z val))) in

        let f := (constr_fun_id,
                  Gfun (Internal
                          {| fn_return := val
                           ; fn_callconv := cc_default
                           ; fn_params := arg_list ++ ((argv_ident, argvTy) :: nil)
                           ; fn_vars := nil
                           ; fn_temps := nil
                           ; fn_body := body
                           |})) in
        rest <- constructors_from_ctors name_ty ctors ;;
        ret (f :: rest)
    end.

  Fixpoint constructors_for_tys
          (tys : list (ind_L1_tag * ty_info))
          : gState defs :=
    match tys with
      | nil => ret nil
      | (itag, {| ty_name := kn ; ty_body := ty |}) :: tys' =>
          nameM <- get_ind_L1_env itag ;;
          match nameM with
          | None => constructors_for_tys tys'
          | Some info =>
              s' <- constructors_from_ctors
                      (ty_name info)
                      (process_ctors (Ast.ind_ctors ty)) ;;
              rest <- constructors_for_tys tys' ;;
              ret (app s' rest)
          end
    end.

End CConstructors.

(* A helper function needed to satisfy a condition about composites *)
Definition mk_prog_opt
           (composites : list composite_definition)
           (ds : defs)
           (main : ident)
           (add_comp : bool)
           : option Clight.program :=
  let composites := if add_comp then composites else nil in
  let res := Ctypes.make_program composites ds nil main in
  match res with
  | Error e => None
  | OK p => Some p
  end.


Section FunctionCalls.
(* Glue code for function calls, adapted from OB to work with different number of parameters *)

(* Necessary variables. TODO: Export them into the toolbox once updated. *)
Variable (threadInfIdent : ident).
Variable (argsIdent : ident).
Variable (make_tinfoIdent : ident).
Variable (haltIdent : ident).
Variable (halt_cloIdent: ident).
Variable (callIdent: ident).


(* TODO: This belongs somewhere else. *)
Fixpoint hd_n {X: Type} (xs: list X) (n : nat) :  list X :=
  match n, xs with
  | 0, xs => nil
  | _ , nil => nil
  | S n, cons x xs => cons x (hd_n xs n)
  end.

(* Notations, from OB *)
Notation " a '::=' b " := (Sset a b) (at level 50).
Notation "'funVar' x" := (Evar x (funTy threadInfIdent)) (at level 20).

(* From OB. TODO: It is impossible to use the L7 version because of make_tinfoIdent.
 *)
Definition make_tinfo_rec : positive * globdef Clight.fundef type :=
  (make_tinfoIdent,
   Gfun (External (EF_external "make_tinfo"
                               (mksignature (nil) (Some val_typ) cc_default))
                  Tnil
                  (threadInf threadInfIdent)
                  cc_default)).


(* Definition of halt and halt_clo.

Generate a function equivalent to halt, receives a tinfo and
 - for c_args = 1 the environment,
 - for c_args >= 2 the environment and the result.

Hence, if c_args>=2 we additionally have to put the result into *tinfo.args[1].
 *)

Definition make_halt
           (c_args : nat)
           : gState ((ident * globdef Clight.fundef type)
                      * (ident * globdef Clight.fundef type)) :=
  envIdent <- gensym "env";;
  argIdent <- gensym "arg";;
  tinfIdent <- gensym "tinfo";;
  let argsExpr :=  (Efield (tinfd threadInfIdent tinfIdent) argsIdent valPtr) in (* TODO: Duplication? *)
  let args_halt := (tinfIdent, (threadInf threadInfIdent)) :: (envIdent, val) :: (argIdent, val) ::  nil in
  let halt_stm := if 2 <=? c_args
                  then Sassign (Field(argsExpr, Z.of_nat 1)) (Etempvar argIdent val);;; Sreturn None
                  else (Sreturn None) in
  ret ((* halt *)
       (haltIdent, Gfun (Internal (mkfunction Tvoid cc_default
                                              (hd_n args_halt (S c_args))
                                              nil nil halt_stm))),
       (* halt_clo *)
       (halt_cloIdent,
        Gvar (mkglobvar (tarray uval 2)
                        ((Init_addrof haltIdent Ptrofs.zero) :: Init_int 1 :: nil)
                        true false))).


Definition condif (b: bool) s1 s2 :=
  if b then s1;;;s2 else s2.

(* Function calls.

What to push in the argument array depends on c_args:
   If c_args = 0, then environment, the halting closure, and the (single) argument have to be put into arg[0], arg[1], and arg[2] respectively.
  If c_args = 1, as before but omit the environment and hand it over directly.
  If c_args = 2, as before but omit the environment and the halting closure.
  If c_args >= 3, no elements have to be put into the argument array.

Call function with respective arguments.
 *)

Definition make_call
           (c_args : nat)
           (closIdent : ident)
           (fIdent : ident)
           (envIdent : ident)
           (argsExpr : expr)
           (argIdent : ident)
           (tinfIdent : ident) : statement :=
  let closExpr := Etempvar closIdent valPtr in
  let fargs := tinf threadInfIdent tinfIdent :: Etempvar envIdent val :: Evar haltIdent val :: Etempvar argIdent val :: nil in
  let forcelist := if c_args <=? 0 then Tnil else if c_args <=? 1 then Tcons val Tnil else if c_args <=? 2 then Tcons val (Tcons val Tnil) else Tcons val (Tcons val (Tcons val Tnil)) in (* TODO: Make this better. *)
  let retty :=  Tpointer (Tfunction (Tcons (threadInf threadInfIdent) forcelist) Tvoid cc_default) noattr in
  (fIdent ::=  (Field(closExpr , Z.of_nat 0)) ;;;
  envIdent ::= (Field(closExpr, Z.of_nat 1)) ;;;
  condif (c_args <=? 0) (Sassign (Field(argsExpr, Z.of_nat 0)) (Etempvar envIdent val))
  (condif (c_args <=? 1) (Sassign (Field(argsExpr, Z.of_nat 1)) (Evar haltIdent val))
  (condif (c_args <=? 2) (Sassign (Field(argsExpr, Z.of_nat 2)) (Etempvar argIdent val))
  ((Scall None ([retty] (funVar fIdent)) (hd_n fargs (S c_args))))))).

Definition make_call_wrapper
           (c_args : nat)
           : gState (ident * globdef Clight.fundef type) :=
    closIdent <- gensym "clo" ;;
    fIdent <- gensym "f" ;;
    envIdent <- gensym "envi" ;;
    retIdent <- gensym "ret" ;;
    argIdent <- gensym "arg" ;;
    tinfIdent <- gensym "tinfo";;

    let argsExpr :=  (Efield (tinfd threadInfIdent tinfIdent) argsIdent valPtr) in
    let left_args := make_proj argsExpr 2 1 in
    let asgn_s := make_call c_args closIdent fIdent envIdent argsExpr argIdent tinfIdent in
    let return_s := (retIdent ::= (Field(argsExpr, Z.of_nat 1))) in
    let body_s := Ssequence
                    (asgn_s)
                    (return_s ;;; Sreturn  (Some (Etempvar retIdent valPtr))) in

    let params := (tinfIdent, (threadInf threadInfIdent)) :: (closIdent, val) :: (argIdent,val) :: nil in
    let vars := (fIdent, valPtr) :: (envIdent, valPtr) :: (retIdent, valPtr) :: nil in
    ret (callIdent, Gfun (Internal (mkfunction (Tpointer Tvoid noattr)
                                              cc_default params nil vars body_s))).


End FunctionCalls.


(* Generates the header and the source programs *)
Definition make_glue_program
        (opts : Options) (gs : Ast.global_env)
  : gState (option Clight.program * option Clight.program) :=
  '(externs, toolbox) <- make_externs ;;
  singles <- (propagate_types >=> filter_prop_types) gs ;;
  name_defs <- make_name_arrays singles ;;
  ctor_defs <- constructors_for_tys singles ;;
  structs <- args_structs_from_types singles ;;
  get_tag_defs <- get_enum_tag_from_types toolbox singles ;;
  make_printer_names singles;;
  printer_defs <- generate_printers toolbox singles ;;

  (* TODO: These should be in the toolbox, when it's updated. *)
  make_tinfoIdent <- gensym "make_tinfo";;
  threadInfIdent <- gensym "thread_info" ;;
  haltIdent <- gensym "halt";;
  halt_cloIdent <- gensym "halt_clo";;
  allocIdent <- gensym "alloc";;
  limitIdent <- gensym "limit";;
  heapInfIdent <- gensym "heap";;
  argsIdent <- gensym "args";;
  callIdent <- gensym "call";;

  nenv <- gets gstate_nenv ;;
  halt_code <- make_halt threadInfIdent argsIdent haltIdent halt_cloIdent (c_args opts) ;;
  call_code <- make_call_wrapper threadInfIdent argsIdent halt_cloIdent callIdent (c_args opts);;
  let (compstructs, struct_defs) := List.split structs in
  let composites := composites argsIdent allocIdent limitIdent threadInfIdent heapInfIdent ++ compstructs in
  let (halt_code, haltclo_code) := halt_code in
  let glob_defs := externs ++ name_defs ++ ctor_defs ++
                   get_tag_defs ++ struct_defs ++
                   printer_defs ++ make_tinfo_rec threadInfIdent make_tinfoIdent ::  halt_code :: haltclo_code :: call_code :: nil in
  let pi := map fst glob_defs in
  ret (mk_prog_opt composites (make_extern_decls nenv glob_defs true)
                   main_ident true,
       mk_prog_opt composites glob_defs
                   main_ident true).


(* The entry point glue code generation *)
Definition generate_glue
           (opts : Options)
           (p : Ast.program) (* an L1 program *)
           : name_env * option Clight.program * option Clight.program * list string :=
  let (globs, _) := p in
  let init : gstate_data :=
      {| gstate_gensym := 2%positive
       ; gstate_ienv   := M.empty _
       ; gstate_nenv   := M.empty _
       ; gstate_gtenv  := M.empty _
       ; gstate_cnenv  := M.empty _
       ; gstate_caaenv := M.empty _
       ; gstate_penv   := M.empty _
       ; gstate_log    := nil
       |} in
  let '((header, source), st) := runState (make_glue_program opts globs) init in
  let nenv := gstate_nenv st in
  (nenv (* the name environment to be passed to C generation *) ,
   header (* the header content *),
   source (* the source content *),
   (rev (gstate_log st)) (* logged messages *)).

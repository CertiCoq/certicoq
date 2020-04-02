Require Import Common.Pipeline_utils.

Require Import Coq.ZArith.ZArith
               Coq.Program.Basics
               Coq.Strings.String
               Coq.Lists.List List_util.

Require Import ExtLib.Structures.Monads
               ExtLib.Data.Monads.OptionMonad
               ExtLib.Data.String.

From MetaCoq.Template Require Import BasicAst.
Require MetaCoq.Template.All.

Require Import compcert.common.AST
               compcert.common.Errors
               compcert.lib.Integers
               compcert.cfrontend.Cop
               compcert.cfrontend.Ctypes
               compcert.cfrontend.Clight
               compcert.common.Values
               compcert.exportclight.Clightdefs.

Require Import L6.cps
               L6.identifiers
               L6.cps_show
               L6_to_Clight
               compM.

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

Definition multiple (xs : list statement) : statement :=
  fold_right Ssequence Sskip xs.

Definition max_args : Z := 1024.

(* aliases for Clight AST types *)
Definition def : Type := ident * globdef fundef type.
Definition defs : Type := list def.
Definition composite_definitions : Type := list composite_definition.

Section Helpers.

  Fixpoint last_error {A : Type} (l : list A) : option A :=
    match l with
    | nil => None
    | a :: nil => Some a
    | a :: xs => last_error xs
    end.

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

Section Names.

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

End Names.

Section Clight_Helpers.

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

End Clight_Helpers.
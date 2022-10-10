(** Naive conversion to a deBruijn-only expression language for a core
    calculus including mutually recursive functions, data constructors,
    and pattern matching.
 *)

Require Import Coq.Arith.Arith Coq.NArith.BinNat Coq.Strings.String
        Coq.Lists.List Coq.micromega.Lia Coq.Program.Program Coq.micromega.Psatz.
Require Export Common.Common.  (* shared namespace *)
Open Scope N_scope.
Opaque N.add.
Opaque N.sub.
Require Import LambdaBoxMut.compile.
Module LambdaBoxMutt := LambdaBoxMut.compile.
Require Import LambdaBoxLocal.expression.

(** Tactics *)
Ltac forward H :=
  match type of H with
  | ?T -> _ => let H' := fresh in cut T;[intros H'; specialize (H H') | ]
  end.

Definition dcon_of_con (i : inductive) (n : nat) := (i, N.of_nat n).

(** Definition environment *)
Definition env := list (kername * exp).

Fixpoint cst_offset (e : env) (s : kername) : N :=
  match e with
  | [] => 0%N
  | (c, e) :: tl => if eq_kername s c then 0 else 1 + cst_offset tl s
  end.

Fixpoint find_prim (prims : list (kername * string * bool * nat * positive)) (n : kername) : option positive :=
  match prims with
  | [] => None
  | (c, s, b, ar, pos) :: prims => if eq_kername n c then Some pos else find_prim prims n
  end.

(** Inductive environment, kept to record arities of constructors.
    No more parameters by this stage. *)
Definition ienv := list (kername * itypPack).

Definition map_terms (f : LambdaBoxMutt.Term -> exp) :=
  fix map_terms (l : LambdaBoxMutt.Terms) : exps :=
  match l with
  | LambdaBoxMutt.tnil => enil
  | LambdaBoxMutt.tcons t ts => econs (f t) (map_terms ts)
  end.

Definition map_exps (f : exp -> exp) :=
  fix map_exps (l : exps) : exps :=
  match l with
  | enil => enil
  | econs t ts => econs (f t) (map_exps ts)
  end.

Section TermTranslation.

  Variable e : env.

  Variable prims : list (kername * string * bool * nat * positive).
           
  Section fixes.
    Variable trans : N -> LambdaBoxMutt.Term -> exp.
    Definition trans_args (k : N) (t : LambdaBoxMutt.Terms) : exps :=
      map_terms (trans k) t.
    Fixpoint trans_brs ind k n l :=
      match l with
      | LambdaBoxMutt.bnil => brnil_e
      | LambdaBoxMutt.bcons nargs t ts =>
        brcons_e (ind,n) (N.of_nat (List.length nargs), nargs) (trans (k + N.of_nat (List.length nargs)) t)
                 (trans_brs ind k (n + 1)%N ts)
      end.
    Fixpoint trans_fixes k l :=
      match l with
      | LambdaBoxMutt.dnil => eflnil
      | LambdaBoxMutt.dcons na t _ l' =>
        eflcons na (trans k t) (trans_fixes k l')
      end.

  End fixes.

  Fixpoint trans (k : N) (t : LambdaBoxMutt.Term) : exp :=
    match t with
    | LambdaBoxMutt.TWrong _ => Prf_e
    | LambdaBoxMutt.TProof => Prf_e
    | LambdaBoxMutt.TRel n => Var_e (N.of_nat n)
    | LambdaBoxMutt.TLambda n t => Lam_e n (trans (1+k) t)
    | LambdaBoxMutt.TLetIn n t u => Let_e n (trans k t) (trans (1+k) u)
    | LambdaBoxMutt.TApp t u => App_e (trans k t) (trans k u)
    | LambdaBoxMutt.TConst s =>
      match find_prim prims s with 
      | Some p => Prim_e p
      | None => 
        (* Transform to let-binding *)
        Var_e (cst_offset e s + k)
      end
    | LambdaBoxMutt.TConstruct ind c args =>
      let args' := trans_args trans k args in
      Con_e (dcon_of_con ind c) args'
    | LambdaBoxMutt.TCase ind t brs =>
      let brs' := trans_brs trans ind k 0%N brs in
      Match_e (trans k t) 0 brs'
    | LambdaBoxMutt.TFix d n =>
      let len := LambdaBoxMutt.dlength d in
      let defs' := trans_fixes trans (N.of_nat len + k) d in
      Fix_e defs' (N.of_nat n)
    | LambdaBoxMutt.TPrim p => Prim_val_e p
    end.

  Definition translate t :=
    trans 0 t.

End TermTranslation.

Section EnvTranslation.
  
  Variable prims : list (kername * string * bool * nat * positive).
  
  Definition translate_entry x acc :=
    match x with
    | (s, ecTrm t) =>
      let t' := translate acc prims t in
      (s, t') :: acc
    | (s, ecTyp _ _) => acc
    end.

  Definition translate_entry_aux x acc : option (string * exp) :=
    match x with
    | (s, ecTrm t) =>
      let t' := translate acc prims t in
      Some (s, t')
    | (s, ecTyp _ _) => None
    end.

  Definition translate_env_aux (e : environ LambdaBoxMut.compile.Term) (k : env) : env :=
    fold_right translate_entry k e.

  Definition translate_env (e : environ LambdaBoxMut.compile.Term) : env :=
    translate_env_aux e [].

End EnvTranslation.

Definition inductive_entry_aux {A} (x : kername * envClass A) acc : ienv :=
  match x with
  | (s, ecTrm t) => acc
  | (s, ecTyp pars pack) =>
    (* pars is always 0 in the output of LambdaBoxMut_noCstrParams *)
    (s, pack) :: acc
  end.

Definition inductive_env (e : environ LambdaBoxMut.compile.Term) : ienv :=
  fold_right inductive_entry_aux [] e.

Definition mkLets (e : env) (t : exp) :=
  fold_left (fun acc (x : _ * exp) => Let_e (string_of_kername (fst x)) (snd x) acc) e t.

(* TODO, pass ienv too *)
Definition translate_program
           (prims : list (kername * string * bool * nat * positive))
           (e: environ LambdaBoxMut.compile.Term) (t: LambdaBoxMutt.Term) : exp :=
  let e' := translate_env prims e in
  mkLets e' (translate e' prims t).

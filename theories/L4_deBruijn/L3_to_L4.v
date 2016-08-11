(** Naive conversion to a deBruijn-only expression language for a core calculus including
    mutually recursive functions, data constructors, and pattern matching.
 *)

(******)
Add LoadPath "../common" as Common.
Add LoadPath "../L1g" as L1g.
Add LoadPath "../L2_typeStripped" as L2.
Add LoadPath "../L3_flattenedApp" as L3.
Add LoadPath "../L4_deBruijn" as L4.
(******)

Require Import Coq.Arith.Arith Coq.NArith.BinNat Coq.Strings.String Coq.Lists.List Coq.omega.Omega Coq.Program.Program Coq.micromega.Psatz.
Require Export Common.Common.  (* shared namespace *)
Open Scope N_scope.
Opaque N.add.
Opaque N.sub.

(***
Require L3.term.
Require L3.wcbvEval.
Require L3.wNorm.
Require L3.unaryApplications.
***)
Require Import L3.compile.

(***
Module L3eval := L3.wcbvEval.
Module L3U := L3.unaryApplications.
Module L3N := L3.wNorm.
***)
Module L3t := L3.compile.

Require Import L4.expression.

Ltac forward H :=
  match type of H with
  | ?T -> _ => let H' := fresh in cut T;[intros H'; specialize (H H') | ]
  end.

Definition dcon_of_con (i : inductive) (n : nat) := (i, N.of_nat n).

(** Erased terms are turned into axioms *)
Definition erased_exp := Ax_e "erased".

(** Definition environment *)
Definition env := list (string * exp).

Fixpoint cst_offset (e : env) (s : string) : N :=
  match e with
  | [] => 0%N
  | (c, e) :: tl => if string_eq_bool s c then 0 else 1 + cst_offset tl s
  end.

(** Inductive environment: disappears at this stage *)
Definition ienv := list (string * itypPack).

Definition map_terms (f : L3t.Term -> exp) :=
  fix map_terms (l : L3t.Terms) : exps :=
  match l with
  | L3t.tnil => enil
  | L3t.tcons t ts => econs (f t) (map_terms ts)
  end.

Definition map_exps (f : exp -> exp) :=
  fix map_exps (l : exps) : exps :=
  match l with
  | enil => enil
  | econs t ts => econs (f t) (map_exps ts)
  end.

Section TermTranslation.
  Variable ie : ienv.
  Variable e : env.
    
  Fixpoint strip_lam (k : nat) (e : exp) : exp :=
    match k, e with
    | 0%nat, _ => e
    | S n, Lam_e e => strip_lam n e
    | S n, _ => e
    end.

  Section fixes.
    Variable trans : N -> L3t.Term -> exp.
    Definition trans_args (k : N) (t : L3t.Terms) : exps :=
      map_terms (trans k) t.
    Fixpoint trans_brs ind pars ann k n l :=
      match l with
      | L3t.tnil => brnil_e
      | L3t.tcons t ts =>
        let nargs := (List.nth (N.to_nat n) ann 0%nat - pars)%nat in
        brcons_e (ind,n) (N.of_nat nargs)
                 (strip_lam nargs (trans k t))
                 (trans_brs ind pars ann k (n + 1)%N ts)
      end.
    Fixpoint trans_fixes k l :=
      match l with
      | L3t.dnil => eflnil
      | L3t.dcons na t _ l' =>
        eflcons (trans k t) (trans_fixes k l')
      end.

  End fixes.
  
  Fixpoint trans (k : N) (t : L3t.Term) : exp :=
    match t with
    | L3t.TAx => Ax_e ""
    | L3t.TProof => (* TODO: Ax_e for now *) Ax_e "proof"
    | L3t.TRel n => Var_e (N.of_nat n)
    | L3t.TSort s => (* Erase *) erased_exp
    | L3t.TProd n t => (* Erase *) erased_exp
    | L3t.TLambda n t => Lam_e (trans (1+k) t)
    | L3t.TLetIn n t u => Let_e (trans k t) (trans (1+k) u)
    | L3t.TApp t u => App_e (trans k t) (trans k u)
    | L3t.TConst s => (* Transform to let-binding *)
      Var_e (cst_offset e s + k)
    | L3t.TInd i => (* Erase *) erased_exp
    | L3t.TConstruct ind c args =>
      let args' := trans_args trans k args in
        Con_e (dcon_of_con ind c) args'
    | L3t.TCase ann t brs =>
      let '(ind, pars, args) := ann in
      let brs' := trans_brs trans ind pars args k 0%N brs in
      Match_e (trans k t) (N.of_nat pars) brs'
    | L3t.TFix d n =>
      let len := L3t.dlength d in
      let defs' := trans_fixes trans (N.of_nat len + k) d in
      Fix_e defs' (N.of_nat n)
    end.

End TermTranslation.

Definition translate (e : env) t :=
  trans e 0 t.

Definition translate_entry x acc :=
  match x with
  | (s, ecTrm t) =>
    let t' := translate acc t in
    (s, t') :: acc
  | (s, ecTyp _ _ _) => acc
  end.

Definition translate_entry_aux x acc : option (string * exp) :=
  match x with
  | (s, ecTrm t) =>
    let t' := translate acc t in
    Some (s, t')
  | (s, ecTyp _ _ _) => None
  end.

Definition translate_env_aux (e : environ L3.compile.Term) (k : env) : env :=
  fold_right translate_entry k e.

Definition translate_env (e : environ L3.compile.Term) : env :=
  translate_env_aux e [].

Definition mkLets (e : env) (t : exp) :=
  fold_left (fun acc (x : string * exp) => Let_e (snd x) acc) e t.

(** start-to-L4 translations **)
Definition myprogram_Program : program -> exception (Program Term) :=
  L3t.program_Program.
(*************
  do pgm0 <- malecha_L1.program_Program pgm (Ret nil);
    let e' := stripEvalCommute.stripEnv (program.env pgm0) in
    match L3U.stripEnv e' with
    | Ret senv => 
      match L3U.strip e' (stripEvalCommute.strip (program.main pgm0)) with
      | Ret smain => Ret {| main := smain; L3.program.env := senv |}
      | Exc s => Exc ("Error in stripping: " ++ s)
      end
    | Exc s => Exc ("Error while stripping environ L3.compile.Termment: " ++ s)
    end.
 *************)

Definition translate_program (e : environ L3.compile.Term) (t : L3t.Term) : exp :=
  let e' := translate_env e in
    mkLets e' (translate e' t).

Definition program_exp (pgm:program) : exception exp :=
  do prg <- myprogram_Program pgm;
      let (main, env) := prg in
      Ret (translate_program env main).

(**************  never used ???  *******************
Definition term_exp (e:L3t.environ L3.compile.Term) (t:term) : exception exp :=
  let e' := stripEvalCommute.stripEnv e in
  match L3U.term_Term e' t with
  | Exc s => Exc ("Error while translating term to L3: " ++ s)
  | Ret trm =>
    match L3U.stripEnv e' with
    | Exc s => Exc ("Error while stripping environ L3.compile.Termment: " ++ s)
    | Ret e => Ret (translate_program e trm)
    end
  end.
***************************************************)
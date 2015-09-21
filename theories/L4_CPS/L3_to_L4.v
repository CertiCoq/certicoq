
(** Naive conversion to continuation-passing style for a core language including
    mutually recursive functions, data constructors, and pattern matching.
*)
Require Import Arith BinNat String List Omega Program Psatz.
Require Export Common.Common.  (* shared namespace *)
Open Scope N_scope.
Opaque N.add.
Opaque N.sub.

Require Import L3.program.

Require L3.
Module L3eval := L3.wndEval.
Module L3 := L3.term.
Require Import  simpleCPS.

Definition dcon_of_con (i : inductive) (n : nat) := N.of_nat n.

Fixpoint translate (t : L3.Term) : simpleCPS.exp :=
  match t with
  | L3.TRel n => Var_e (N.of_nat n)
  | L3.TSort s => Var_e 0 (* encode with TConst ? *)
  | L3.TProd n t => Var_e 0  (* same ? *)
  | L3.TLambda n t => Lam_e (translate t)
  | L3.TLetIn n t u => Let_e (translate t) (translate u)
  | L3.TApp t u => App_e (translate t) (translate u)
  | L3.TConst s => Var_e 0 (* FIXME *)
  | L3.TInd i => Var_e 0 (* FIXME *)
  | L3.TConstruct ind c args =>
    let fix args' l :=
        match l with
        | L3.tnil => nil
        | L3.tcons t ts => cons (translate t) (args' ts)
        end
    in Con_e (dcon_of_con ind c) (args' args)
  | L3.TCase n t brs =>
    let fix brs' n l :=
      match l with
      | L3.tnil => nil
      | L3.tcons t ts => cons (n, 0 (* FIXME *), translate t) (brs' (n + 1)%N ts)
      end
    in Match_e (translate t) (brs' (0%N) brs)
  | L3.TFix d n =>
    let fix defs' l :=
        match l with
        | L3.dnil => nil
        | L3.dcons na t k l' => cons (translate t) (defs' l')
        end
    in Proj_e (Fix_e (defs' d)) (N.of_nat n)
  end.

Theorem translate_correct (e : environ) (t t' : L3.Term) :
  L3eval.wndEval e t t' -> (* small step non-deterministic *)
  eval (translate t) (translate t') (* big-step deterministic *).
Proof.
  induction 1. simpl. red in H. 



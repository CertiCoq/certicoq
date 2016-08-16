Require Import L4.expression.
Require Import L4.L4a_to_L5.

Require Import SquiggleEq.export.
Require Import SquiggleEq.UsefulTypes.
(*
Require Import SquiggleEq.list.
Require Import SquiggleEq.LibTactics.
Require Import SquiggleEq.tactics.
Require Import SquiggleEq.lmap.
*)

Require Import Coq.Arith.Arith Coq.NArith.BinNat Coq.Strings.String Coq.Lists.List Coq.omega.Omega Coq.Program.Program Coq.micromega.Psatz.

Section VarsOf2Class.

(* see the file SquiggleEq.varImplPeano for an instantiation of NVar *)
Context {NVar} {deqnvar : Deq NVar} 
  {vartype: @VarType NVar bool (* 2 species of vars*) _}.


Notation BTerm := (@BTerm NVar CoqL4GenericTermSig).
Notation NTerm := (@NTerm NVar CoqL4GenericTermSig).
Notation oterm := (@oterm NVar CoqL4GenericTermSig).

Notation push := cons (only parsing).

Definition freshVar (lv : list NVar) : NVar :=
hd nvarx (freshVars 1 (Some true) lv []).

Definition dummyind := Ast.mkInd "" 0%nat.

(* N.to_nat efficiency? *)
Fixpoint translate (fvars : list NVar)(e:exp) : NTerm :=
match e with
| Var_e n => vterm (nth (N.to_nat n) fvars nvarx) (* efficiency? *)

| expression.Lam_e e => 
    let vn := freshVar fvars in
    Lam_e vn (translate (vn::fvars) e)

| expression.App_e f a => 
    App_e (translate fvars f) (translate fvars a)

| expression.Let_e e1 e2 => 
    let vn := freshVar fvars in
    Let_e vn (translate fvars e1) (translate (vn::fvars) e2)

| expression.Con_e d el => 
    Con_e d (translatel fvars el)

| expression.Fix_e el pn => 
    let xf := freshVar fvars in
    Proj_e (Fix_e xf (translatef (xf::fvars) el)) (N.to_nat pn)

| expression.Match_e d _ brl => 
    Match_e (translate fvars d) (translateb fvars brl)

| Ax_e _ => Con_e (dummyind, N.zero) nil (* FIX! *) 
end
with translatel (fvars : list NVar)(e:exps) : list NTerm :=
match e with
| enil => []
| econs h tl => (translate fvars h)::(translatel fvars tl)
end
with translatef (fvars : list NVar)(e:efnlst) : list NTerm :=
match e with
| eflnil => []
| eflcons h tl => (translate fvars h)::(translatef fvars tl)
end
with translateb (fvars : list NVar)(lb:branches_e) 
  : list (@branch NVar CoqL4GenericTermSig):=
match lb with
| brnil_e => []
| brcons_e d n e tl => 
    let bvars := freshVars (N.to_nat n) (Some true) fvars [] in 
    let h := (d, bterm bvars (translate (bvars++fvars) e)) in
    h::(translateb fvars tl)
end.


End VarsOf2Class.

Require Import SquiggleEq.varImplZ.

Require Import cps.

Definition L4_to_L4a (e:expression.exp) : (@NTerm cps.var CoqL4GenericTermSig) :=
  translate nil e.

(* faster than [L4_to_L4a]. This one exploits the fact that variables are numbers 
Fixpoint L4_to_L4a_fast (depth : positive (*1 => outside any binder *))
(e:expression.exp) : NTerm :=
match e with
| Var_e n => vterm ((Npos depth) - (n+1))%N
| _ => vterm xH
end.
*)



Require Import L4.expression.
Require Import L4.L4a_to_L5.

Require Import SquiggleEq.export.
Require Import SquiggleEq.UsefulTypes.
Require Import SquiggleEq.varImplZ.
(*
Require Import SquiggleEq.list.
Require Import SquiggleEq.LibTactics.
Require Import SquiggleEq.tactics.
Require Import SquiggleEq.lmap.
*)

Require Import Coq.Arith.Arith Coq.NArith.BinNat Coq.Strings.String Coq.Lists.List Coq.omega.Omega Coq.Program.Program Coq.micromega.Psatz.

(*replace in to SquiggleEq and delete here *)
Fixpoint seq {T:Type} (next: T->T) (start : T) (len : nat) {struct len} : list T :=
match len with
| 0 => []
| S len0 => start :: seq next (next start) len0
end.


(* make a section so that the notations get cleared *)
Section Dummy.
Variable NVar:Type.
Variable mkVar : N -> NVar.

Notation BTerm := (@BTerm NVar L4Opid).
Notation NTerm := (@NTerm NVar L4Opid).
Notation oterm := (@oterm NVar L4Opid).

Notation push := cons (only parsing).


Definition dummyind := Ast.mkInd "" 0%nat.



(* N.to_nat efficiency? *)
Fixpoint translate (max : N)(e:exp) : NTerm :=
match e with
| Var_e n => vterm (mkVar (max-n-1))

| expression.Lam_e e => 
    let vn := mkVar max in
    Lam_e vn (translate (N.succ max) e)

| expression.App_e f a => 
    App_e (translate max f) (translate max a)

| expression.Let_e e1 e2 => 
    let vn := mkVar max in
    Let_e vn (translate max e1) (translate (N.succ max) e2)

| expression.Con_e d el => 
    Con_e d (translatel max el)

| expression.Fix_e el pn => 
    let xf := mkVar max in
    Proj_e (Fix_e xf (translatef (N.succ max) el)) (N.to_nat pn)

| expression.Match_e d _ brl => 
    Match_e (translate max d) (translateb max brl)

| Ax_e _ => Con_e (dummyind, N.zero) nil (* FIX! *) 
end
with translatel (max : N)(e:exps) : list NTerm :=
match e with
| enil => []
| econs h tl => (translate max h)::(translatel max tl)
end
with translatef (max:N)(e:efnlst) : list NTerm :=
match e with
| eflnil => []
| eflcons h tl => (translate max h)::(translatef max tl)
end
with translateb (max:N)(lb:branches_e) 
  : list (@branch NVar L4Opid):=
match lb with
| brnil_e => []
| brcons_e d n e tl => 
    let bvars := map mkVar (seq N.succ max (N.to_nat n)) in 
    let h := (d, bterm bvars (translate (max+n) e)) in
    h::(translateb max tl)
end.


End Dummy.

Require Import L6.cps.

(* uservars are supposed to be even, so multiply by 2 x0*)
Definition L4_to_L4a (e:expression.exp) : (@NTerm cps.var L4Opid) :=
  translate cps.var (fun n => xO (N.succ_pos n)) (0%N) e.

(*
(* Delete this module and everything inside it *)
Module Old.
Notation NVar := cps.var.

Require Import SquiggleEq.export.
Require Import L4.expression.
Require Import L4.L4a_to_L5.

Definition freshVar (lv : list NVar) : NVar :=
hd nvarx (freshVars 1 (Some true) lv []).

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
  : list (@branch NVar L4Opid):=
match lb with
| brnil_e => []
| brcons_e d n e tl => 
    let bvars := freshVars (N.to_nat n) (Some true) fvars [] in 
    let h := (d, bterm bvars (translate (bvars++fvars) e)) in
    h::(translateb fvars tl)
end.
End Old.

Require Import Common.certiClasses.
Require Export L2.instances.
Require Export L3.compile.
Require Export L3.instances.
Require Import Common.Common.
Require Import Template.Template.

Quote Recursively Definition p := (3 + 4).
Quote Recursively Definition id := @id.

Quote Recursively Definition swap := 
(fun {A B:Type} (p: A  *B) =>
match p with
(x,y) => (y,x)
end).



Section Test.
Local Instance certiL3_to_L4: 
  CerticoqTranslation (Program L3.compile.Term) L4.expression.exp  :=
fun p => Ret (L3_to_L4.translate_program (AstCommon.env p) (main p)).

Require Import Template.Template.


Open Scope Z_scope.
Require Import ZArith.

Definition pl4 : L4.expression.exp.
(let t:= eval compute in (translateTo L4.expression.exp p) in 
match t with
|Ret ?xx => exact xx
end).
Defined.

Definition id4 : L4.expression.exp.
(let t:= eval compute in (translateTo L4.expression.exp id) in 
match t with
|Ret ?xx => exact xx
end).
Defined.

Definition swap4 : L4.expression.exp.
(let t:= eval compute in (translateTo L4.expression.exp swap) in 
match t with
|Ret ?xx => exact xx
end).
Defined.

Print swap4.
Time Eval vm_compute in (L4_to_L4a pl4).
Time Eval compute in (L4_to_L4a pl4).
(*0.003 secs*)

Time Eval vm_compute in (Old.translate nil pl4).
(*0.004 secs*)

Local Opaque Match_e.
Local Opaque Fix_e.
Local Opaque Proj_e.
Local Opaque Con_e.
Local Opaque Lam_e.
Local Opaque Let_e.
Local Opaque App_e.

(*
Compute runs much slower.
These Opacity directives cut down the time from 40s to 13.929s
*)
Definition pl4a := ltac:(let t:= eval compute in (L4_to_L4a swap4) in exact t).
Definition pl4aOld := ltac:(let t:= eval compute in (Old.translate nil swap4) in exact t).

Print swap4. (* Why are branches lambdas? *)
Print pl4a.
Print pl4aOld.

Local Transparent Match_e.
Local Transparent Fix_e.
Local Transparent Proj_e.
Local Transparent Con_e.
Local Transparent Lam_e.
Local Transparent Let_e.
Local Transparent App_e.

(* fix opacity in squiggleEq *)
Local Instance deqpos : Deq positive.
Proof.
  apply @deqAsSumbool.
  intros ? ?. unfold DecidableSumbool.
  decide equality.
Defined.

Print pl4a.
Print pl4aOld.

Eval vm_compute in (free_vars pl4aOld).
Eval vm_compute in (free_vars pl4a).

Print deqpos.


End Test.
*)


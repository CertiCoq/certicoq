Require Import L4.expression.
Require Import L4.variables.
Require Import polyEval.

Require Import SquiggleEq.export.
Require Import SquiggleEq.UsefulTypes.
Require Import SquiggleEq.varImplZ.
(*
Require Import SquiggleEq.list.
Require Import SquiggleEq.LibTactics.
Require Import SquiggleEq.tactics.
Require Import SquiggleEq.lmap.
*)

Require Import Coq.Arith.Arith 
Coq.NArith.BinNat Coq.Strings.String Coq.Lists.List Coq.omega.Omega Coq.Program.Program 
Coq.micromega.Psatz.

Definition dummyind := Ast.mkInd "" 0%nat.

Require Import Common.RandyPrelude.
Open Scope N_scope.

Require Import ExtLib.Data.Map.FMapPositive.
Require Import Common.TermAbs.
Require Import SquiggleEq.termsDB.


Fixpoint tL4_to_L4_1 (e:exp) {struct e}: (@DTerm Ast.name L4Opid):=
match e with
| Var_e n => vterm n

| Lam_e name e => 
    oterm NLambda [bterm [name] (tL4_to_L4_1 e)]

| App_e f a => 
    oterm NApply 
      (map ((bterm [])∘tL4_to_L4_1) [f;a])

| Let_e name e1 e2 =>
    oterm NLet [bterm [] (tL4_to_L4_1 e1); bterm [name] (tL4_to_L4_1 e2)]

| Con_e d el => let el := (ltL4_to_L4_1 el) in 
    oterm (NDCon d (length el)) (map ((bterm [])) el)

| Fix_e el i => 
    let names := fnames el in
    let lbt := ftL4_to_L4_1 el in
     oterm (NFix (length lbt) (N.to_nat i)) (map (bterm names) lbt)

| Match_e d _ brl => 
  let brs := btL4_to_L4_1 brl in
   oterm (NMatch (List.map (fun b => (fst b, num_bvars (snd b))) brs))
        ((bterm [] (tL4_to_L4_1 d))::(List.map snd brs))


| Ax_e s => oterm (NBox s) []
end
with ltL4_to_L4_1  (e:exps) {struct e}: list (@DTerm Ast.name L4Opid) :=
match e with
| enil => []
| econs h tl => 
    (tL4_to_L4_1 h)
     ::(ltL4_to_L4_1 tl)
end
with ftL4_to_L4_1  (e:efnlst) {struct e}: list (@DTerm Ast.name L4Opid) :=
match e with
| eflnil => []
| eflcons f h tl => 
    (tL4_to_L4_1 h)
    ::(ftL4_to_L4_1 tl)
end
with btL4_to_L4_1 (lb:branches_e) {struct lb}
  : list (@polyEval.branch L4Opid (@TermAbsDB _ _)):=
match lb with
| brnil_e => []
| brcons_e d n e tl => 
    let (n,vnames) := n in
    let vnames := firstn  (N.to_nat n) vnames in
    let vnames := list.listPad Ast.nAnon vnames  (N.to_nat n) in
    (d, bterm vnames (tL4_to_L4_1 e))
    ::(btL4_to_L4_1 tl)
end.


Definition mkVar (n:N) : positive :=  (xO (N.succ_pos n)).

Definition mkNVar (p: N*Ast.name) : NVar := 
  let (n, name) := p in (mkVar n, name).

Definition getId (i:positive): N := (N.pred (N.pos (Pos.div2 i))).

Definition getNId :NVar -> N := getId ∘ fst.

Lemma getIdMkVar : forall i,
  getId (mkVar i) = i.
Proof using Type.
  intros.
  unfold getId. simpl.
  rewrite N.pos_pred_succ.
  refl.
Qed.

Lemma getIdMkNVar : forall n s,
  getNId (mkNVar (n,s)) = n.
Proof using Type.
  intros. unfold getNId. simpl.
  unfold compose. simpl.
  apply getIdMkVar.
Qed.


Require Import L6.cps.



Definition L4_1_Term :Type := (@DTerm Ast.name L4Opid).
Definition L4_2_Term :Type := (@NTerm NVar L4Opid).

(* may be useful in some proofs *)
Definition tL4_1_to_L4_2_aux (n:N) (e:L4_1_Term) : L4_2_Term :=
  fromDB Ast.nAnon mkNVar n Empty e.

Definition tL4_1_to_L4_2 (e:L4_1_Term) : L4_2_Term :=
  fromDB Ast.nAnon mkNVar 0 Empty e.

(* L4_1 is not intended to be visible to the rest of certicoq *)
Definition tL4_to_L4_2 : L4.expression.exp -> L4_2_Term :=
  tL4_1_to_L4_2 ∘ tL4_to_L4_1.



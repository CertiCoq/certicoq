Require Import BinNat.
Require Import BinPos.
Require Import Omega.
Require Import Psatz.
Require Import Arith.
Require Import PArith.
Require Import NArith.
Require Import L4.expression.
Require Import Basics.


Require Import L4.polyEval.
Require Import SquiggleEq.export.
Require Import SquiggleEq.UsefulTypes.
Require Import SquiggleEq.varImplZ.
Require Import SquiggleEq.list.
Require Import SquiggleEq.LibTactics.
Require Import Coq.Classes.DecidableClass.
Require Import Coq.Classes.Morphisms.

Require Import SquiggleEq.tactics.
Require Import Coq.Unicode.Utf8.
Require Import List.
Require Import SquiggleEq.list.

Open Scope program_scope.


Open Scope N_scope.

Section L4Inst.


(**
The proof in SquiggleEq of substitution commuting with DB to named
only works when substituting with closed terms, and to produce closed terms.
Thus, we need to either carry enough proofs to ensure the applicability of that
proof or have the instantiation of [absApplyBTerm] check those decidable conditions
and return None if they are not met.
Although the former choice avoids checks, it may end up paying large performance
penalties for carrying around proofs. Also, carrying around proofs make 
it hard to write down programs without using tactics.
In the latter choice, if the checks are indeed too costly,
we can later prove that on closed inputs, the eval function
produces the same answer as another one that doesn't do the checks.

Some day, there should be an unconditional proof of substitution commuting with
DB to named conversion.
*)

Let Term : Set := exp.
Let BTerm : Set := ((list Ast.name) *exp).

(** this was needed in eval to select the right branch *)
Let numBvars (b:BTerm) : nat (* switch to N? *) := length (fst b).

Require Import L4.L4_to_L4_1_to_L4_2.

Let toOpidBTerms (t:Term) : option (L4Opid * list BTerm):=
match t  return option (L4Opid * list BTerm) with
| Var_e _ => None
| Lam_e n x => Some (NLambda, [([n],x)])
| App_e f a => Some (NApply, [([],f) ; ([],a)])
| Let_e n a f => Some (NLet, [([],a) ; ([n],f)])
| Con_e d es => 
    let es := exps_as_list es in 
    Some (NDCon d (length es), map (fun e => ([],e)) es)
| Match_e e _ bs =>
    let bs := branches_as_list bs in
    let numBound p := (fst (snd (fst p))) in 
    let op :(list (dcon * nat)) := 
        map (fun p => (fst (fst p), (N.to_nat (numBound p)))) bs in
    let lb  := 
        map (fun p => ((snd (snd (fst p))), snd p) ) bs in
    Some (NMatch op, ([],e)::lb)
| Fix_e fs n =>
    let fs := efnlst_as_list fs in
    let ns := map fst fs in
    Some (NFix (length fs) (N.to_nat n), map (fun e => (ns,snd e)) fs)

(** Fix : An axiom behaves differently from a constructor: (Ax _) --> Ax *)
| Ax_e s => Some (NDCon (dummyind,0) 0, [])
end.

Require Import ExtLib.Structures.Monads.
Require Import ExtLib.Data.Monads.OptionMonad.
Require Import Common.ExtLibMisc.

Import Monad.MonadNotation.
Open Scope monad_scope.

Typeclasses eauto :=5.

(** just switch the input and output in toOpidBTerms *)
Let fromOpidBTerms  (l: list BTerm) (o: L4Opid) : option Term :=
match (o,l) with
| (NLambda, [([n],x)]) => Some (Lam_e n x)
| (NApply, [([],f) ; ([],a)]) => Some (App_e f a)
| (NLet, [([],a) ; ([n],f)]) => Some (Let_e n a f)
| (NDCon d l, cs) => Some (Con_e d (exps_from_list (map snd cs)))
| (NMatch op, ([],e)::lb) => Some (Match_e e 0 (* params? *) 
    (branches_from_list 
      (map 
          (fun ob => let o := fst ob in let b := snd ob in
            (fst o, (NLength (fst b) , fst b) , snd b)) 
          (combine op lb))))
| (NFix l n, fs)
   => let fes := map snd fs in
      f1 <-head fs;;
        let names := fst f1 in
        Some (Fix_e (efnlst_from_list (combine names fes)) (N.of_nat n))
(* Axioms ? Indistinguisable from constructors ? *)
| _ => None
end.

Let getTerm (b : BTerm) : option Term :=
if decide (length (fst b) = O) then Some (snd b) else None.

(** must return None when the conditions for the substitution commuting
  (with DB to named conversion) dont hold *)
Let applyBTerm (b : BTerm) (l: list Term) : option Term :=
let (n,t):=b in
  if (Z.of_nat (length n) <? (maxFree t))%Z then None
else 
  (if (ZLmax (map maxFree l) (-1) <? 0)%Z then Some (sbst_real_list t l) else None).

Require Import TermAbs.
Definition L4Abs : Common.TermAbs.TermAbs L4Opid :=
(@Build_TermAbs _ _ 
  Term 
  BTerm 
  numBvars 
  toOpidBTerms 
  getTerm 
  applyBTerm 
  fromOpidBTerms
  (fun e => ([],e))).

End L4Inst.

Require Import Common.TermAbs_parametricity.

Parametricity Recursive eval_n.
Require Import L4.variables.

(* should be automatically provalble for all types with decidable equality.
  However, it cannot be internally stated. *)
Global Instance EqIfRL4Opid : EqIfR L4Opid_R.
Proof using.
  constructor; intros Hyp; subst.
- inverts Hyp; auto; f_equal; try apply eqIfR; auto.
  unfold dcon in *.
Admitted.

Let TermAbs_R_NamedDB2 :=
  (@TermAbs_R_NamedDB Ast.name NVar _ L4Opid _ _ _ _  _ _ Ast.nAnon mkNVar getNId getIdMkNVar
     L4Opid_R L4_o_polyEval_o_CoqL4GenericTermSig_R EqIfRL4Opid).

Lemma L4_1_to_L4_2_free_thm:
  forall (t1 : L4_1_Term) n,
termsDB.fvars_below 0 t1 (* free thm also implies that eval_n preserves this *)->
(option_R _ _ alpha_eq)
   (option_map tL4_1_to_L4_2 (@eval_n (TermAbsDB Ast.name L4Opid) n t1))
   (@eval_n (Named.TermAbsImpl variables.NVar L4Opid) n (tL4_1_to_L4_2 t1)).
Proof using.
  intros ? ? Hfb.
  pose proof (L4_o_polyEval_o_eval_n_R 
    (TermAbsDB Ast.name L4Opid) (Named.TermAbsImpl variables.NVar L4Opid)
    TermAbs_R_NamedDB2 n n ltac:(apply eqIfR; refl) t1) as Hp.
  simpl in Hp.
  unfold Term_R in Hp.
  specialize (Hp _ (conj Hfb (alpha_eq_refl _))).
  simpl in Hp.
  destruct (@eval_n (TermAbsDB Ast.name L4Opid) n t1).
  - invertsna Hp Hp. setoid_rewrite <- Hp0.
    constructor. tauto.
  - invertsna Hp Hp. setoid_rewrite <- Hp.
    constructor.
Qed.
  
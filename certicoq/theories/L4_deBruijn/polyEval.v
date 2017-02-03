Require Import SquiggleEq.export.
Require Import Common.classes Common.AstCommon.
Require Import Common.TermAbs.
Require Import SquiggleEq.bin_rels.
Require Import SquiggleEq.eq_rel.
Require Import SquiggleEq.universe.
Require Import SquiggleEq.LibTactics.
Require Import SquiggleEq.tactics.
Require Import Coq.Bool.Bool.
Require Import Coq.Program.Tactics.
Require Import Omega.
Require Import Coq.Program.Basics.
Require Import Coq.Lists.List.
Require Import Coq.Init.Notations.
Require Import SquiggleEq.UsefulTypes.
Require Import Coq.Classes.DecidableClass.
Require Import Coq.Classes.Morphisms.
Require Import SquiggleEq.list.

Require Import Recdef.
Require Import Eqdep_dec.
Require Import SquiggleEq.varInterface.
Require Import Common.ExtLibMisc.
Require Import ExtLib.Structures.Monads.
Require Import ExtLib.Data.Monads.OptionMonad.

Instance IndEqDec : Deq (inductive).
Proof using.
  apply @deqAsSumbool.
  exact eq_dec.
Defined.

Import Monad.MonadNotation.
Open Scope monad_scope.
Definition dcon : Set := inductive * N.

Inductive L4Opid : Set :=
 | NLambda
 | NFix (nMut index: nat) 
 | NDCon (dc : dcon) (nargs : nat)
 | NApply
 | NLet
 | NMatch (dconAndNumArgs : list (dcon * nat)).

Definition OpBindingsL4 (nc : L4Opid) : list nat :=
  match nc with
  | NLambda    => [1]
  | NFix nMut _ => repeat nMut nMut
  | NDCon _ nargs    => repeat 0 nargs
  | NApply     => [0,0]
(*  | NProj _ => [0] *)
  | NLet => [0,1]
  | NMatch numargsInBranches => 0::(List.map snd numargsInBranches)
  end.

Instance decc: DeqSumbool L4Opid.
Proof using.
  intros ? ?. unfold DecidableSumbool.
   repeat(decide equality).
Defined.

Instance CoqL4GenericTermSig : GenericTermSig L4Opid:=
{| 
  OpBindings := OpBindingsL4;
|}.


Section Branches.

Context (Opid:Type) {gts:GenericTermSig Opid} {ta : TermAbs Opid}.

(* this definition of branch and find_branch is shared with 
L4a and L5 *)
Definition branch 
  : Type := (dcon * (@AbsBTerm Opid  gts ta))%type.


(** Find a branch in a match expression corresponding to a given constructor
    and arity. *)
Definition find_branch  (d:dcon) (m:nat) (matcht :list branch) : 
    option (AbsBTerm Opid ta) 
  := 
  let obr :=
  find 
    (fun a : (branch) => decide ((d,m) = (fst a, absNumBound _ _ (snd a)))) matcht in
  option_map snd obr.

End Branches.

Section PolyEval.


(** eval_n for L4 (congrete DB), L4a (generic named), and
the (yet to be added) generic (Squiggle-style) DB language between them.
*)
Context (Opid:Type) {gts:GenericTermSig Opid} {Abs4_4a: @TermAbs L4Opid _}.

Local Notation AbsTerm := (AbsTerm _ Abs4_4a).
Local Notation absGetOpidBTerms := (absGetOpidBTerms _ Abs4_4a).
Local Notation absApplyBTerm := (absApplyBTerm _ Abs4_4a).
Local Notation absGetTerm := (absGetTerm _ Abs4_4a).
Local Notation absMakeTerm := (absMakeTerm _ Abs4_4a).
Local Notation absMakeBTerm := (absMakeBTerm _ Abs4_4a).


Typeclasses eauto :=4.

Open Scope program_scope.

(* generalized from L4.expresssion.eval_n *)
Fixpoint eval_n (n:nat) (e:AbsTerm) {struct n} :  option AbsTerm :=
match n with
|0%nat => None
| S n =>  match (absGetOpidBTerms e) with |None => None | Some (o,lbt) =>
  match (o,lbt) with
  (* values *)
  | (NLambda,_)
  | (NFix _ _,_) => Some e

  (* (possibly) non-values *)
  | (NLet, [a;f]) =>
        a <- absGetTerm a;;
        a <- eval_n n a ;;
        s <- (absApplyBTerm f [a]);;
        eval_n n s
  | (NDCon d ne, lb) => 
        vs <- flatten (map (fun b => t <- absGetTerm b ;; eval_n n t)lb) ;;
        (absMakeTerm (map absMakeBTerm vs) o)
  | (NMatch ldn, disc::brs) => 
        disc <- absGetTerm disc;;
        disc <- eval_n n disc;;
        match (absGetOpidBTerms disc) with
        | Some (NDCon d ne, clb) =>
          cvs <- flatten (map absGetTerm clb);;
          b <- find_branch _ d (length cvs) (combine (map fst ldn) brs);;
          (* TODO: skip the parameters in cvs. matches don't bind parameters.
          (If parameters are explicit, Coq forces us to write "_" at those positions
          in constructor patterns).
          A similar fix is needed in L5. *)
          s <- (absApplyBTerm b cvs);;
          eval_n n s
        | _ => None
        end
  | (NApply, [f;a]) =>
        a <- absGetTerm a;;
        a <- eval_n n a ;;
        f <- absGetTerm f;;
        f <- eval_n n f;;
        match (absGetOpidBTerms f) with
        | Some (NLambda,[b]) =>
            s <- (absApplyBTerm b [a]);;
            eval_n n s
        | Some (NFix nMut i,lm) =>
            let pinds := List.seq 0 (length lm) in
            let ls := map (fun n => absMakeTerm lm (NFix nMut n)) pinds in
            ls <- flatten ls;;
            im <- select i lm;;
            s <- (absApplyBTerm im ls);;
            s_a_pp <- (absMakeTerm (map absMakeBTerm [s;a]) NApply);;
            eval_n n s_a_pp
        | _ => None
        end
    | _ => None
  end
  end
end.

End PolyEval.


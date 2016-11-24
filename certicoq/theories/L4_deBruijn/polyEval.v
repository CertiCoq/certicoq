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

Generalizable Variable Opid.

Require Import terms.

(* TODO : unbundle *)


(* using dependent types, one can get rid of the incessant use of [option].
However, that would make it almost impossible to write programs over this interface
without using Ltac *)

Record TermAbs (Opid:Type) {gts:GenericTermSig Opid} : Type :=
{
  AbsTerm : Type;
  AbsBTerm : Type;
  absNumBound : AbsBTerm -> nat;

(** If None, then the term was a Var. In this interface, which is intended
to be polymorphic over choice of bindings styles, 
    e.g. named or de-bruijn, concrete or generic,
  there is no way to directly access a Var *)
  absGetOpidBTerms : AbsTerm -> option (Opid * list AbsBTerm);
  
(** A term can be obtained from a bound term iff it binds no variables.
This is just for efficiency. One can already do this by applying a
nil substitution. However, that may unnecessarily involve a traversal *)
  absGetTerm : AbsBTerm -> option AbsTerm;
  absGetTermSome: forall b, absNumBound b = 0 <-> isSome (absGetTerm b);


(** a limited form of substitution *)
  absApplyBTerm : AbsBTerm -> (list AbsTerm) -> option  AbsTerm;
  absApplyBTermSome: forall b l, absNumBound b = length l <-> isSome (absApplyBTerm b l);


  absMakeTerm : list AbsBTerm -> Opid -> option AbsTerm;
  absMakeTermCorr : forall l o,
    map absNumBound l = OpBindings o <-> isSome (absMakeTerm l o);

  absMakeBTerm : AbsTerm -> AbsBTerm;
  absMakeBTermCorr : forall t,
    absNumBound (absMakeBTerm t) = 0;


  absGetOpidBTermsCorr: forall a,
    match absGetOpidBTerms a with
    | Some (o, lb)=> OpBindings o = map absNumBound lb
    | None => True
    end;
}.

(*
Can be added to the above, but not needed yet:
(* Because we cannot look inside binders, size is not definable w.r.t the interface *)
  absSizeTerm :  AbsTerm -> nat;
  absSizeBTerm :  AbsBTerm -> nat;

(* size decrease: allows recursion based on size. 
The parametricity plugin seems to fail on Coq's [Function]s.
However, the plugin correctly generated
the abstraction theorem for a proof of the complete natural induction principle 
*)
  sizeDecreasOt : forall a b,
    In b (absGetBTerms a) -> (absSizeBTerm b) < (absSizeTerm a);

  sizeDecreasBt : forall b p,
     (absSizeTerm (absGetTerm b p)) < (absSizeBTerm b);
*)


Definition deqOption {A:Type} `{Deq A} (oa ob : option A) : bool :=
match (oa,ob) with
| (Some a, Some b) => decide (a=b)
| (None, None) => true
| _ => false 
end.

Lemma deqOptionCorr {A:Type} `{Deq A} :
  forall x y, deqOption x y = true <-> x = y.
Proof.
  destruct x, y; unfold deqOption; simpl; auto; 
  unfold decide; try rewrite  Decidable_spec;
  split; intro;
  subst; try discriminate; auto.
  inverts H0. refl.
Qed.

Instance optionEqDec {A:Type} `{Deq A}: Deq (option A).
Proof using.
  (* if it is already defined, don't create a duplicate instance *)
  Fail (eauto with typeclass_instances; fail).
  intros x y. exists (deqOption x y). apply deqOptionCorr.
Defined.

Instance NEqDec2 : Deq N.
Proof using.
  (* if it is already defined, don't create a duplicate instance *)
  Fail (eauto with typeclass_instances; fail).
  intros x y. exists (N.eqb x y). apply N.eqb_eq.
Defined.


(* All of above is not specific to Certicoq and should eventually end up
in the SquiggleEq library.*)

Require Import ExtLib.Structures.Monads.
Require Import ExtLib.Data.Monads.OptionMonad.
Require Import Common.ExtLibMisc.
Require Import Common.classes Common.AstCommon.

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











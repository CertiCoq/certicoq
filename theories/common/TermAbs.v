(* This file is not specific to Certicoq and should eventually end up
in the SquiggleEq library.*)

Require Import SquiggleEq.bin_rels.
Require Import SquiggleEq.eq_rel.
Require Import SquiggleEq.universe.
Require Import SquiggleEq.LibTactics.
Require Import SquiggleEq.tactics.
Require Import SquiggleEq.list.
Require Import SquiggleEq.UsefulTypes.
Require Import SquiggleEq.varInterface.
Require Import SquiggleEq.terms.
Require Import Coq.Bool.Bool.
Require Import Coq.Program.Tactics.
Require Import Omega.
Require Import Coq.Program.Basics.
Require Import Coq.Lists.List.
Require Import Coq.Init.Notations.
Require Import Coq.Classes.DecidableClass.
Require Import Coq.Classes.Morphisms.

Require Import Recdef.
Require Import Eqdep_dec.

Generalizable Variable Opid.


(* TODO : unbundle *)


(* using dependent types, one can get rid of the incessant use of [option].
However, that would make it almost impossible to write programs over this interface
without using Ltac *)

Record TermAbs (Opid:Type) (* {gts:GenericTermSig Opid} *) : Type :=
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
(*  absGetTermSome: forall b, absNumBound b = 0 <-> isSome (absGetTerm b); *)


(** a limited form of substitution *)
  absApplyBTerm : AbsBTerm -> (list AbsTerm) -> option  AbsTerm;
(*  absApplyBTermSome: forall b l, absNumBound b = length l <-> isSome (absApplyBTerm b l); *)


  absMakeTerm : list AbsBTerm -> Opid -> option AbsTerm;
(*absMakeTermCorr : forall l o,
    map absNumBound l = OpBindings o <-> isSome (absMakeTerm l o);*)

  absMakeBTerm : AbsTerm -> AbsBTerm;
(*absMakeBTermCorr : forall t,
    absNumBound (absMakeBTerm t) = 0; *)


(*absGetOpidBTermsCorr: forall a,
    match absGetOpidBTerms a with
    | Some (o, lb)=> OpBindings o = map absNumBound lb
    | None => True
    end;*)
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

Require Import SquiggleEq.export.
Module Named. (* just for namespaces *)
Section SquiggleNamedInst.
Context  (NVar Opid:Type) {VarClass} {deqnvar : Deq NVar} {varcl freshv} 
{varclass: @VarType NVar VarClass deqnvar varcl freshv} 
 `{hdeq : Deq Opid} {gts : GenericTermSig Opid}.

Definition safeGetNT (b:@BTerm NVar Opid) : option (@NTerm NVar Opid) :=
match b with
| bterm [] nt => Some nt
| _ => None
end.


Definition mkBTermSafe (lb : list BTerm) (o: Opid) : option (@NTerm NVar Opid) :=
(* if (decide ((map num_bvars lb) = OpBindings o))%nat then Some (oterm o lb) else None. *)
Some (oterm o lb).

(* move to SquiggleEq.terms? *)
Definition getOpidBTerms (t: @NTerm NVar Opid) : option (Opid * list BTerm):=
match t with
| vterm _ => None
| oterm o lb => Some (o, lb)
end.

Definition applyBTermClosed (b : BTerm) (l: list NTerm) : option (@NTerm NVar Opid) :=
if (num_bvars b =? length l) then Some (apply_bterm b l) else None.

Definition TermAbsImpl : TermAbs Opid :=
 (@Build_TermAbs _ 
  (@NTerm NVar Opid) (@BTerm NVar Opid)
   num_bvars
   getOpidBTerms
   safeGetNT
   applyBTermClosed
   mkBTermSafe
   (bterm [])).

End SquiggleNamedInst.
End Named.



Require Import SquiggleEq.termsDB.

Section SquiggleDBInst.
Context (Name Opid:Type) {gts:GenericTermSig Opid}.

Definition safeGetNT (b:@DBTerm Name Opid) : option (@DTerm Name Opid) :=
match b with
| bterm [] nt => Some nt
| bterm (_::_) nt => None (* must return None. returing nt in this case will break alpha equality *)
end.

Definition applyBTermClosed (b : DBTerm) (l: list DTerm) : option (@DTerm Name Opid) :=
let (n,t):=b in
  if (num_bvars b  =? length l)%nat then  Some (subst_aux_list 0 t l) else None.

Definition mkBTermSafe (lb : list DBTerm) (o: Opid) : option (@DTerm Name Opid) :=
(*if (decide ((map num_bvars lb) = OpBindings o))%nat then Some (oterm o lb) else None. *)
Some (oterm o lb).


Definition TermAbsDB : TermAbs Opid :=
 (@Build_TermAbs _ 
  (@DTerm Name Opid) (@DBTerm Name Opid)
   num_bvars
   getOpidBTerms
   safeGetNT
   applyBTermClosed
   mkBTermSafe
   (bterm [])).


End SquiggleDBInst.

(* Move to Common.TermAbsImpl *)
Lemma getNtNamedMapBtCommute {O1 O2 V} (f : @NTerm V O1 -> @NTerm V O2) b:
  Named.safeGetNT _ _ (btMapNt f b) = option_map f (Named.safeGetNT _ _ b).
Proof using.
  destruct b as [l ?]. simpl. destruct l; refl.
Qed.

Require Import SquiggleEq.terms.
(* Move to Common.TermAbsImpl *)
Lemma numBvarsBtMapNt {O1 O2 V} (f : @NTerm V O1 -> @NTerm V O2) (b : @BTerm V O1):
  num_bvars (btMapNt f b) = num_bvars b.
Proof using.
  destruct b; refl.
Qed.

Require Import SquiggleEq.ExtLibMisc.
(* Move to Common.TermAbsImpl *)
Lemma safeGetNTmap {O V} (lbt: list (@BTerm V O)) m:
  map num_bvars lbt = repeat 0%nat m->
  (flatten (map (Named.safeGetNT V O) lbt)) =
  Some (map get_nt lbt).
Proof using.
  revert m.
  induction lbt; auto;[].
  intros ? Hm.
  simpl in *.
  simpl.
  destruct m; [invertsn Hm | ].
  simpl in *. inverts Hm as Hma Hm.
  rewrite Hma in Hm.
  specialize (IHlbt _ Hm).
  rewrite IHlbt. destruct a as [lv nt].
  destruct lv; [refl |  inverts Hma].
Qed.

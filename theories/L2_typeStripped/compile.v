(****)
Add LoadPath "../common" as Common.
Add LoadPath "../L1_5_box" as L1_5.
(****)

Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.Arith.Peano_dec.
Require Import Common.Common.
Require Import L1_5.compile.

Local Open Scope string_scope.
Local Open Scope bool.
Local Open Scope list.
Set Implicit Arguments.

Definition L1_5Term := L1_5.compile.Term.
Definition L1_5Terms := L1_5.compile.Terms.
Definition L1_5Defs := L1_5.compile.Defs.
Definition L1_5EC := L1_5.compile.envClass.
Definition L1_5Env := L1_5.compile.environ.
Definition L1_5Pgm := L1_5.compile.Program.


Inductive Term : Type :=
| TRel       : nat -> Term
| TSort      : Srt -> Term
| TProof     : Term
| TCast      : Term -> Term
| TProd      : name -> Term -> Term
| TLambda    : name -> Term -> Term
| TLetIn     : name -> Term -> Term -> Term
| TApp       : Term -> Term (* first arg must exist *) -> Terms -> Term
| TConst     : string -> Term
| TInd       : inductive -> Term
| TConstruct : inductive -> nat (* cnstr no *) -> Term
| TCase      : (nat * list nat) (* # parameters, # args per branch *) ->
               Term -> Terms -> Term
| TFix       : Defs -> nat -> Term
with Terms : Type :=
| tnil : Terms
| tcons : Term -> Terms -> Terms
with Defs : Type :=
| dnil : Defs
| dcons : name -> Term -> nat -> Defs -> Defs.
Hint Constructors Term Terms Defs.
Scheme Trm_ind' := Induction for Term Sort Prop
  with Trms_ind' := Induction for Terms Sort Prop
  with Defs_ind' := Induction for Defs Sort Prop.
Scheme Trm_ind2 := Induction for Term Sort Type
  with Trms_ind2 := Induction for Terms Sort Type
  with Defs_ind2 := Induction for Defs Sort Type.
Combined Scheme TrmTrmsDefs_ind from Trm_ind', Trms_ind', Defs_ind'.
Combined Scheme TrmTrms_ind from Trm_ind', Trms_ind'.
Definition tunit (t:Term) : Terms := (tcons t tnil).
Notation prop := (TSort SProp).
Notation set_ := (TSort SSet).
Notation type_ := (TSort SType).
Notation x_ := (nAnon).


Function strip (t:L1_5Term) : Term :=
  match t with
    | L1_5.compile.TProof => TProof
    | L1_5.compile.TRel n => TRel n
    | L1_5.compile.TSort s => TSort s
    | L1_5.compile.TCast t _ _ => TCast (strip t)
    | L1_5.compile.TProd nm _ bod => TProd nm (strip bod)
    | L1_5.compile.TLambda nm _ bod => TLambda nm (strip bod)
    | L1_5.compile.TLetIn nm dfn _ bod =>
      TLetIn nm (strip dfn) (strip bod)
    | L1_5.compile.TApp fn arg args =>
      TApp (strip fn) (strip arg) (strips args)
    | L1_5.compile.TConst nm => TConst nm
    | L1_5.compile.TInd i => TInd i
    | L1_5.compile.TConstruct i m => TConstruct i m
    | L1_5.compile.TCase n _ mch brs => TCase n (strip mch) (strips brs)
    | L1_5.compile.TFix ds n => TFix (stripDs ds) n
  end
with strips (ts:L1_5Terms) : Terms := 
  match ts with
    | L1_5.compile.tnil => tnil
    | L1_5.compile.tcons t ts => tcons (strip t) (strips ts)
  end
with stripDs (ts:L1_5Defs) : Defs := 
  match ts with
    | L1_5.compile.dnil => dnil
    | L1_5.compile.dcons nm _ t m ds => dcons nm (strip t) m (stripDs ds)
  end.


(** this function for use in translation from L2 to L3 **)
Fixpoint arity_from_dtyp
        (npars:nat) (itps:itypPack) (tndx:nat) (cndx:nat) : exception nat :=
  do ity <- exnNth itps tndx;
  do itp <- exnNth (itypCnstrs ity) cndx;
  ret (npars + (CnstrArity itp)).

(** environments and programs **)
Definition envClass := AstCommon.envClass Term.
Definition environ := AstCommon.environ Term.
Definition Program := AstCommon.Program Term.

Function stripEC (ec:L1_5EC) : envClass :=
  match ec with
    | ecTrm _ t => ecTrm Term (strip t)
    | ecTyp _ n itp => ecTyp Term n itp
    | ecAx _ => ecAx Term
  end.

Definition  stripEnv : L1_5Env -> environ :=
  List.map (fun nmec : string * L1_5EC => (fst nmec, stripEC (snd nmec))).

Definition stripProgram (p:L1_5Pgm) : Program :=
  {| env:= stripEnv (env _ p);
     main:= strip (main _ p) |}.

(*** from L0 to L2 ***)
Definition program_Program (pgm:program) : option Program :=
  match L1_5.compile.program_Program pgm with
    | Exc str => None
    | Ret pgm => Some (stripProgram pgm)
  end.
Definition term_Term (t:term) : option Term :=
  match L1_5.compile.term_Term t with
    | Exc str => None
    | Ret trm => Some (strip trm)
  end.

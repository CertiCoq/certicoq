(****)
Add LoadPath "../common" as Common.
Add LoadPath "../L1g" as L1g.
(****)

Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.Arith.Peano_dec.
Require Import Common.Common.
Require Import L1g.compile.
Require Import L1g.term.

Local Open Scope string_scope.
Local Open Scope bool.
Local Open Scope list.
Set Implicit Arguments.

Definition L1gTerm := L1g.compile.Term.
Definition L1gTerms := L1g.compile.Terms.
Definition L1gDefs := L1g.compile.Defs.
Definition L1gPgm := Program L1gTerm.
Definition L1gEC := envClass L1gTerm.
Definition L1gEnv := environ L1gTerm.


Inductive Term : Type :=
| TRel       : nat -> Term
| TSort      : Srt -> Term
| TProof     : Term -> Term
| TCast      : Term -> Term
| TProd      : name -> Term -> Term
| TLambda    : name -> Term -> Term
| TLetIn     : name -> Term -> Term -> Term
| TApp       : Term -> Term (* first arg must exist *) -> Terms -> Term
| TConst     : string -> Term
| TAx        : Term
| TInd       : inductive -> Term
| TConstruct : inductive -> nat (* cnstr no *) -> nat (* arity *) -> Term
| TCase      : (inductive * nat * list nat) (* # params, args per branch *) ->
               Term -> Terms -> Term
| TFix       : Defs -> nat -> Term
| TWrong     : Term
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
Combined Scheme TrmTrmsDefs_ind from Trm_ind', Trms_ind', Defs_ind'.
Combined Scheme TrmTrms_ind from Trm_ind', Trms_ind'.
Notation prop := (TSort SProp).
Notation set_ := (TSort SSet).
Notation type_ := (TSort SType).
Notation tunit t := (tcons t tnil).


Function strip (t:L1gTerm) : Term :=
  match t with
    | L1g.compile.TRel n => TRel n
    | L1g.compile.TSort s => TSort s
    | L1g.compile.TCast t _ (L1g.compile.TCast _ _ (L1g.compile.prop)) =>
      TProof (strip t)
    | L1g.compile.TCast t _ _ => TCast (strip t)
    | L1g.compile.TProd nm _ bod => TProd nm (strip bod)
    | L1g.compile.TLambda nm _ bod => TLambda nm (strip bod)
    | L1g.compile.TLetIn nm dfn _ bod =>
      TLetIn nm (strip dfn) (strip bod)
    | L1g.compile.TApp fn arg args =>
      TApp (strip fn) (strip arg) (strips args)
    | L1g.compile.TConst nm => TConst nm
    | L1g.compile.TAx => TAx
    | L1g.compile.TInd i => TInd i
    | L1g.compile.TConstruct i m arty => TConstruct i m arty
    | L1g.compile.TCase n _ mch brs => TCase n (strip mch) (strips brs)
    | L1g.compile.TFix ds n => TFix (stripDs ds) n
    | L1g.compile.TWrong _ => TWrong
  end
with strips (ts:L1gTerms) : Terms := 
  match ts with
    | L1g.compile.tnil => tnil
    | L1g.compile.tcons t ts => tcons (strip t) (strips ts)
  end
with stripDs (ts:L1gDefs) : Defs := 
  match ts with
    | L1g.compile.dnil => dnil
    | L1g.compile.dcons nm _ t m ds => dcons nm (strip t) m (stripDs ds)
  end.

Lemma notPrf_stripCast:
  forall x, ~ L1g.term.isProp x ->
  forall t1 ck1 t2 ck2,
    strip (L1g.compile.TCast
             t1 ck1 (L1g.compile.TCast t2 ck2 x)) = TCast (strip t1).
  destruct x; intros; cbn; try reflexivity.
  destruct s; try reflexivity.
  elim H. reflexivity.
Qed.

(** environments and programs **)
Function stripEC (ec:L1gEC) : AstCommon.envClass Term :=
  match ec with
    | ecTrm t => ecTrm (strip t)
    | ecTyp _ n itp => ecTyp Term n itp
  end.

Definition  stripEnv : L1gEnv -> AstCommon.environ Term :=
  List.map (fun nmec : string * L1gEC => (fst nmec, stripEC (snd nmec))).

Definition stripProgram (p:L1gPgm) : Program Term :=
  {| env:= stripEnv (env p);
     main:= strip (main p) |}.

(*** from L1 to L2 ***) 
Definition program_Program (p:program) : Program Term :=
  stripProgram (L1g.compile.program_Program p).

Definition term_Term (e:AstCommon.environ L1gTerm) (t:term) : Term :=
  strip (L1g.compile.term_Term e t).

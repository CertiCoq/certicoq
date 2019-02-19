
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
Definition L1gBrs := L1g.compile.Brs.
Definition L1gDefs := L1g.compile.Defs.
Definition L1gPgm := Program L1gTerm.
Definition L1gEC := envClass L1gTerm.
Definition L1gEnv := environ L1gTerm.


Inductive Term : Type :=
| TRel       : nat -> Term
| TProof     : Term
| TLambda    : name -> Term -> Term
| TLetIn     : name -> Term -> Term -> Term
| TApp       : Term -> Term -> Term
| TConst     : string -> Term
| TConstruct : inductive -> nat (* cnstr no *) ->
               nat (* # pars *) -> nat (* # args *) -> Term
                                  (* use Defs to code branches *)
| TCase      : (inductive * nat) (* # of pars *) ->
               Term (* discriminee *) -> Brs (* # args, branch *) -> Term
| TFix       : Defs -> nat -> Term
| TWrong     : string -> Term
with Brs : Type :=
| bnil : Brs
| bcons : nat -> Term -> Brs -> Brs
with Defs : Type :=
| dnil : Defs
| dcons : name -> Term -> nat -> Defs -> Defs.
Hint Constructors Term Brs Defs.
Scheme Trm_ind' := Induction for Term Sort Prop
  with Brs_ind' := Induction for Brs Sort Prop
  with Defs_ind' := Induction for Defs Sort Prop.
Combined Scheme TrmTrmsBrsDefs_ind from Trm_ind', Brs_ind', Defs_ind'.
Notation dunit nm t m := (dcons nm t m dnil).
Notation Terms := (list Term).

(**************
with Terms : Type :=
| tnil : Terms
| tcons : Term -> Terms -> Terms

Function tlast t ts: (Terms * Term) :=
  match ts with
  | tnil => (tnil, t)
  | tcons u us => let (xs, x) := tlast u us in (tcons t xs, x)
  end.

Fixpoint Terms_list (ts:Terms) : list Term :=
  match ts with
    | tnil => nil
    | tcons u us => cons u (Terms_list us)
  end.
 ***************)

(** turn (App fn [x1;...;xn]) into (App (... (App fn x1) x2 ...) xn) **)
(** TDummy and TWrong eat all their arguments **
Function TApp_eats (fn:Term): option Term :=
  match fn with
  | TDummy => Some TDummy
  | TWrong s => Some (TWrong s)
  | TApp gn _ => TApp_eats gn
  | _ => None
  end.
 ***********)

Function mkApp (fn:Term) (ts:Terms) : Term :=
  match ts with
  | nil => fn
  | cons y ys => mkApp (TApp fn y) ys
  end.

(*************
Function tappend (ts1 ts2:Terms) : Terms :=
  match ts1 with
    | tnil => ts2
    | tcons t ts => tcons t (tappend ts ts2)
  end.
 ************)

Lemma mkApp_idempotent:
  forall ts (fn:Term) (ss:Terms),
    mkApp (mkApp fn ts) ss = mkApp fn (app ts ss).
Proof.
  induction ts; destruct fn; intros; cbn; try reflexivity;
  try rewrite <- IHts; try reflexivity.
Qed.                                                       
  
Lemma mkApp_nil: forall fn, mkApp fn nil = fn.
  intros. reflexivity.
Qed.

Lemma mkApp_cons:
  forall fn u us, mkApp fn (cons u us) = mkApp (TApp fn u) us.
Proof.
  intros. reflexivity.
Qed.

Lemma mkApp_out:
  forall ts fn u,
    mkApp fn (app ts (unit u)) = TApp (mkApp fn ts) u.
Proof.
  induction ts; intros. reflexivity.
  - cbn. rewrite IHts. reflexivity.
Qed.

Lemma mkApp_tl:
  forall bs fn b, mkApp fn (app bs (unit b)) = TApp (mkApp fn bs) b.
Proof.
  induction bs; intros.
  - reflexivity.
  - cbn. rewrite IHbs. reflexivity.
Qed.

Lemma mkApp_unit:
  forall fn u, 
    mkApp fn (unit u) = TApp fn u.
Proof.
  intros. destruct fn; try reflexivity.
Qed.

(********************
Function AppMk (fn:Term) (ts:Terms) : Term :=
  match fn with
  | TDummy as tc
  | (TWrong _) as tc => tc    (* throw away arg of Dummy, Wrong *)
  | fn => match ts with
          | tnil => fn
          | tcons y ys =>
            let (us, u) := tlast y ys in TApp (mkApp fn us) u
          end
  end.
    
Lemma AppMk_tnil:
  forall fn, AppMk fn tnil = fn.
Proof.
  destruct fn; try reflexivity.
Qed.

Lemma AppMk_Wrong:
  forall ts s, AppMk (TWrong s) ts = TWrong s.
Proof.
  induction ts; intros; reflexivity.
Qed.

Lemma AppMk_Dummy:
  forall ts, AppMk TDummy ts = TDummy.
Proof.
  induction ts; intros; reflexivity.
Qed.
**************************)

Function strip (t:L1gTerm) : Term :=
  match t with
    | L1g.compile.TRel n => TRel n
    | L1g.compile.TProof => TProof
    | L1g.compile.TLambda nm bod => TLambda nm (strip bod)
    | L1g.compile.TLetIn nm dfn bod =>
      TLetIn nm (strip dfn) (strip bod)
    | L1g.compile.TApp fn arg => TApp (strip fn) (strip arg)
    | L1g.compile.TConst nm => TConst nm
    | L1g.compile.TConstruct i m np na => TConstruct i m np na
    | L1g.compile.TCase n mch brs => TCase n (strip mch) (stripBs brs)
    | L1g.compile.TFix ds n => TFix (stripDs ds) n
    | L1g.compile.TWrong str => TWrong str
  end
with stripBs (bs:L1gBrs) : Brs := 
  match bs with
    | L1g.compile.bnil => bnil
    | L1g.compile.bcons n t ts => bcons n (strip t) (stripBs ts)
  end
with stripDs (ts:L1gDefs) : Defs := 
  match ts with
    | L1g.compile.dnil => dnil
    | L1g.compile.dcons nm t m ds => dcons nm (strip t) m (stripDs ds)
  end.

(***********
with strips (ts:L1gTerms) : Terms := 
  match ts with
    | L1g.compile.tnil => tnil
    | L1g.compile.tcons t ts => tcons (strip t) (strips ts)
  end


Lemma strips_tcons:
  forall t ts,
    strips (L1g.compile.tcons t ts) = tcons (strip t) (strips ts).
Proof.
  reflexivity.
Qed.
*****************)
  
(************
Lemma strip_TCast_TCast:
  forall t, ~ L1g.term.isCastProp t ->
            forall u, strip (L1g.compile.TCast u t) = TCast (strip u).
Proof.
  intros t ht u. unfold isCastProp in ht.
  assert (j: forall prp, t <> L1g.compile.TCast prp L1g.compile.prop).
  { intros prp j. elim ht. exists prp. assumption. }
  destruct t; cbn; try reflexivity.
  destruct t2; cbn; try reflexivity.
  destruct s; cbn; try reflexivity.
  specialize (j t1). destruct j. reflexivity.
Qed.

Lemma strip_TCast_TCast':
  forall u t, ~ L1g.term.isProofCast (L1g.compile.TCast u t) ->
            strip (L1g.compile.TCast u t) = TCast (strip u).
Proof.
  intros u t h. unfold isProofCast in h.
  assert (j: forall prf prp,
            L1g.compile.TCast u t <>
            L1g.compile.TCast prf (L1g.compile.TCast prp L1g.compile.prop)).
  { intros prf prp k. apply h. exists prf, prp. assumption. }
  destruct t; cbn; try reflexivity.
  destruct t2; cbn; try reflexivity.
  destruct s; cbn; try reflexivity.
  specialize (j u t1). destruct j. reflexivity.
Qed.
*******************)

(** environments and programs **)
Function stripEC (ec:L1gEC) : AstCommon.envClass Term :=
  match ec with
    | ecTrm t => ecTrm (strip t)
    | ecTyp _ n itp => ecTyp Term n itp
  end.

Definition  stripEnv : L1gEnv -> AstCommon.environ Term :=
  List.map (fun nmec : string * L1gEC => (fst nmec, stripEC (snd nmec))).

Lemma stripEcTrm_hom:
  forall t, stripEC (ecTrm t) = ecTrm (strip t).
Proof.
  intros. reflexivity.
Qed.

Lemma stripEnv_pres_fresh:
  forall nm p, fresh nm p -> fresh nm (stripEnv p).
Proof.
  induction 1.
  - constructor; assumption.
  - constructor.
Qed.

Lemma stripEnv_inv:
  forall gp s ec p, stripEnv gp = (s, ec) :: p ->
                    exists ec2 p2, ec =stripEC ec2 /\ p = stripEnv p2.
Proof.
  intros. destruct gp. discriminate. cbn in H. injection H; intros. subst.
  exists (snd p0), gp. intuition.
Qed.
  
Definition stripProgram (p:L1gPgm) : Program Term :=
  {| env:= stripEnv (env p);
     main:= strip (main p) |}.

(*** from L1g to L2d ***)
Require Import Coq.Arith.PeanoNat.
Instance fuel : utils.Fuel := { fuel := 2 ^ 14 }.
Definition program_Program (p:Ast.program) : Program Term :=
  stripProgram (L1g.compile.program_Program p).

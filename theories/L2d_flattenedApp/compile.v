
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.Arith.Peano_dec.
Require Import Common.Common.
Require Import L2.compile.
Require Import L2.term.

Local Open Scope string_scope.
Local Open Scope bool.
Local Open Scope list.
Set Implicit Arguments.

Definition L2Term := L2.compile.Term.
Definition L2Terms := L2.compile.Terms.
Definition L2Brs := L2.compile.Brs.
Definition L2Defs := L2.compile.Defs.
Definition L2Pgm := Program L2Term.
Definition L2EC := envClass L2Term.
Definition L2Env := environ L2Term.


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
| TDummy     : string -> Term    (* residual of Sort, Ind and Products in L2 *)
with Terms : Type :=
| tnil : Terms
| tcons : Term -> Terms -> Terms
with Brs : Type :=
| bnil : Brs
| bcons : nat -> Term -> Brs -> Brs
with Defs : Type :=
| dnil : Defs
| dcons : name -> Term -> nat -> Defs -> Defs.
Hint Constructors Term Terms Brs Defs.
Scheme Trm_ind' := Induction for Term Sort Prop
  with Trms_ind' := Induction for Terms Sort Prop                             
  with Brs_ind' := Induction for Brs Sort Prop
  with Defs_ind' := Induction for Defs Sort Prop.
Combined Scheme TrmTrmsBrsDefs_ind
         from Trm_ind', Trms_ind', Brs_ind', Defs_ind'.
Notation tunit t := (tcons t tnil).
Notation dunit nm t m := (dcons nm t m dnil).

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
  | tnil => fn
  | tcons y ys => mkApp (TApp fn y) ys
  end.

Function tappend (ts1 ts2:Terms) : Terms :=
  match ts1 with
    | tnil => ts2
    | tcons t ts => tcons t (tappend ts ts2)
  end.

Lemma mkApp_idempotent:
  forall ts (fn:Term) (ss:Terms),
    mkApp (mkApp fn ts) ss = mkApp fn (tappend ts ss).
Proof.
  induction ts; destruct fn; intros; cbn; try reflexivity;
  try rewrite <- IHts; try reflexivity.
Qed.                                                       
  
Lemma mkApp_tnil: forall fn, mkApp fn tnil = fn.
  intros. reflexivity.
Qed.

Lemma mkApp_cons:
  forall fn u us, mkApp fn (tcons u us) = mkApp (TApp fn u) us.
Proof.
  intros. reflexivity.
Qed.

Lemma mkApp_out:
  forall ts fn u,
    mkApp fn (tappend ts (tunit u)) = TApp (mkApp fn ts) u.
Proof.
  induction ts; intros. reflexivity.
  - cbn. rewrite IHts. reflexivity.
Qed.

Lemma mkApp_tl:
  forall bs fn b, mkApp fn (tappend bs (tunit b)) = TApp (mkApp fn bs) b.
Proof.
  induction bs; intros.
  - reflexivity.
  - cbn. rewrite IHbs. reflexivity.
Qed.

Lemma mkApp_tunit:
  forall fn u, 
    mkApp fn (tunit u) = TApp fn u.
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

Function strip (t:L2Term) : Term :=
  match t with
    | L2.compile.TRel n => TRel n
    | L2.compile.TProof => TProof
    | L2.compile.TLambda nm bod => TLambda nm (strip bod)
    | L2.compile.TLetIn nm dfn bod =>
      TLetIn nm (strip dfn) (strip bod)
    | L2.compile.TApp fn arg args =>
      mkApp (strip fn) (tcons (strip arg) (strips args))
    | L2.compile.TConst nm => TConst nm
    | L2.compile.TConstruct i m np na => TConstruct i m np na
    | L2.compile.TCase n mch brs => TCase n (strip mch) (stripBs brs)
    | L2.compile.TFix ds n => TFix (stripDs ds) n
    | L2.compile.TDummy str => TDummy str
    | L2.compile.TWrong str => TWrong str
  end
with strips (ts:L2Terms) : Terms := 
  match ts with
    | L2.compile.tnil => tnil
    | L2.compile.tcons t ts => tcons (strip t) (strips ts)
  end
with stripBs (bs:L2Brs) : Brs := 
  match bs with
    | L2.compile.bnil => bnil
    | L2.compile.bcons n t ts => bcons n (strip t) (stripBs ts)
  end
with stripDs (ts:L2Defs) : Defs := 
  match ts with
    | L2.compile.dnil => dnil
    | L2.compile.dcons nm t m ds => dcons nm (strip t) m (stripDs ds)
  end.

Lemma strips_tcons:
  forall t ts,
    strips (L2.compile.tcons t ts) = tcons (strip t) (strips ts).
Proof.
  reflexivity.
Qed.

  
(************
Lemma strip_TCast_TCast:
  forall t, ~ L2.term.isCastProp t ->
            forall u, strip (L2.compile.TCast u t) = TCast (strip u).
Proof.
  intros t ht u. unfold isCastProp in ht.
  assert (j: forall prp, t <> L2.compile.TCast prp L2.compile.prop).
  { intros prp j. elim ht. exists prp. assumption. }
  destruct t; cbn; try reflexivity.
  destruct t2; cbn; try reflexivity.
  destruct s; cbn; try reflexivity.
  specialize (j t1). destruct j. reflexivity.
Qed.

Lemma strip_TCast_TCast':
  forall u t, ~ L2.term.isProofCast (L2.compile.TCast u t) ->
            strip (L2.compile.TCast u t) = TCast (strip u).
Proof.
  intros u t h. unfold isProofCast in h.
  assert (j: forall prf prp,
            L2.compile.TCast u t <>
            L2.compile.TCast prf (L2.compile.TCast prp L2.compile.prop)).
  { intros prf prp k. apply h. exists prf, prp. assumption. }
  destruct t; cbn; try reflexivity.
  destruct t2; cbn; try reflexivity.
  destruct s; cbn; try reflexivity.
  specialize (j u t1). destruct j. reflexivity.
Qed.
*******************)

(** environments and programs **)
Function stripEC (ec:L2EC) : AstCommon.envClass Term :=
  match ec with
    | ecTrm t => ecTrm (strip t)
    | ecTyp _ n itp => ecTyp Term n itp
  end.

Definition  stripEnv : L2Env -> AstCommon.environ Term :=
  List.map (fun nmec : string * L2EC => (fst nmec, stripEC (snd nmec))).

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
  
Definition stripProgram (p:L2Pgm) : Program Term :=
  {| env:= stripEnv (env p);
     main:= strip (main p) |}.

(*** from L2 to L2d ***) 
Definition program_Program (p:program) : Program Term :=
  stripProgram (L2.compile.program_Program p).

(**
Check strip.
Check L2.compile.term_Term.
  Definition term_Term (e:AstCommon.environ L2Term) (t:Term) : Term :=
  strip (strip (L2.compile.term_Term e t)).
***)

Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.Arith.Peano_dec.
Require Import Common.Common.
Require Import Omega.
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
| TProof     : Term -> Term
| TCast      : Term -> Term
| TLambda    : name -> Term -> Term
| TLetIn     : name -> Term -> Term -> Term
| TApp       : Term -> Term (* first arg must exist *) -> Terms -> Term
| TConst     : string -> Term
| TAx        : L2Term -> Term
(* constructors fully applied: eta expand and drop parameters *)
| TConstruct : inductive -> nat (* index *) -> Terms -> Term
         (* use Defs to code branches in Case *)
| TCase      : inductive -> Term (* discriminee *) ->
               Brs (* # args, branch *) -> Term
| TFix       : Defs -> nat -> Term
| TWrong     : Term
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
Notation bunit t m := (bcons t m bnil).

Fixpoint Terms_list (ts:Terms) : list Term :=
  match ts with
    | tnil => nil
    | tcons u us => cons u (Terms_list us)
  end.

Function tlength (ts:Terms) : nat :=
  match ts with 
    | tnil => 0
    | tcons _ ts => S (tlength ts)
  end.

Function blength (ts:Brs) : nat :=
  match ts with 
    | bnil => 0
    | bcons _ _ ts => S (blength ts)
  end.

Lemma tlength_S:
  forall ts p,
    tlength ts > p ->
    exists u us, ts = tcons u us /\ tlength us >= p.
Proof.
  induction ts; intros.
  - cbn in H. omega.
  - cbn in H. case_eq ts; intros; subst.
    + exists t, tnil. auto. cbn in H. assert (j:p = 0). omega. subst.
      intuition.
    + exists t, (tcons t0 t1). intuition.
Qed.

Fixpoint tappend (ts1 ts2:Terms) : Terms :=
  match ts1 with
    | tnil => ts2
    | tcons t ts => tcons t (tappend ts ts2)
  end.

Lemma tappend_tnil: forall ts:Terms, tappend ts tnil = ts.
Proof.
  induction ts; simpl; try reflexivity.
  rewrite IHts. reflexivity.
Qed.

Lemma tappend_assoc:
  forall xts yts zts,
       (tappend xts (tappend yts zts)) = (tappend (tappend xts yts) zts).
  induction xts; intros yts zts; simpl.
  - reflexivity.
  - rewrite IHxts. reflexivity.
Qed.

Lemma tappend_pres_tlength:
  forall ts us, tlength (tappend ts us) = (tlength ts) + (tlength us).
Proof.
  induction ts; intros.
  - reflexivity.
  - cbn. rewrite IHts. reflexivity.
Qed.

(** reversing Terms **)
Fixpoint treverse (ts: Terms) : Terms :=
  match ts with
    | tnil => tnil
    | tcons b bs => tappend (treverse bs) (tunit b)
  end.

Lemma treverse_tappend_distr:
  forall x y:Terms,
    treverse (tappend x y) = tappend (treverse y) (treverse x).
Proof.
  induction x as [| a l IHl]; cbn; intros.
  - destruct y as [| a l]; cbn. reflexivity.
    rewrite tappend_tnil. reflexivity.
  - rewrite (IHl y). rewrite tappend_assoc. reflexivity.
Qed.

Remark treverse_tunit:
  forall (l:Terms) (a:Term),
    treverse (tappend l (tunit a)) = tcons a (treverse l).
Proof.
  intros.
  apply (treverse_tappend_distr l (tunit a)); simpl; auto.
Qed.

Lemma treverse_involutive:
  forall ts:Terms, treverse (treverse ts) = ts.
Proof.
  induction ts as [| a l IHl]; cbn; intros. reflexivity.
  - rewrite treverse_tunit. rewrite IHl. reflexivity.
Qed.
   
Remark tunit_treverse:
    forall (l:Terms) (a:Term),
    tappend (treverse l) (tunit a) = treverse (tcons a l).
Proof.
  intros. cbn. reflexivity.
Qed.

Lemma treverse_pres_tlength:
  forall ts, tlength ts = tlength (treverse ts).
Proof.
  induction ts; intros. reflexivity.
  - cbn. rewrite IHts. rewrite tappend_pres_tlength. cbn. omega.
Qed.
  
Fixpoint dlength (ts:Defs) : nat :=
  match ts with 
    | dnil => 0
    | dcons _ _ _ ts => S (dlength ts)
  end.


(** lift a Term over a new binding **)
Function lift (n:nat) (t:Term) : Term :=
  match t with
    | TRel m => TRel (match m ?= n with
                        | Lt => m
                        | _ => S m
                      end)
    | TProof t => TProof (lift n t)
    | TCast t => TCast (lift n t)
    | TLambda nm bod => TLambda nm (lift (S n) bod)
    | TLetIn nm df bod => TLetIn nm (lift n df) (lift (S n) bod)
    | TApp fn arg args => TApp (lift n fn) (lift n arg) (lifts n args)
    | TConstruct i x args => TConstruct i x (lifts n args)
    | TCase iparsapb mch brs => TCase iparsapb (lift n mch) (liftBs n brs)
    | TFix ds y => TFix (liftDs (n + dlength ds) ds) y
    | _ => t
  end
with lifts (n:nat) (ts:Terms) : Terms :=
       match ts with
         | tnil => tnil
         | tcons u us => tcons (lift n u) (lifts n us)
       end
with liftBs (n:nat) (ts:Brs) : Brs :=
       match ts with
         | bnil => bnil
         | bcons m b bs => bcons m (lift n b) (liftBs n bs)
       end
with liftDs n (ds:Defs) : Defs :=
       match ds with
         | dnil => dnil
         | dcons nm u j es => dcons nm (lift n u) j (liftDs n es)
       end.
Functional Scheme lift_ind' := Induction for lift Sort Prop
with lifts_ind' := Induction for lifts Sort Prop
with liftBs_ind' := Induction for liftBs Sort Prop
with liftDs_ind' := Induction for liftDs Sort Prop.
Combined Scheme liftLiftsliftBsLiftDs_ind
         from lift_ind', lifts_ind', liftBs_ind', liftDs_ind'.


Lemma lifts_pres_tlength:
  forall n ts, tlength (lifts n ts) = tlength ts.
Proof.
  induction ts.
  + reflexivity.
  + simpl. intuition.
Qed.

Lemma liftDs_pres_dlength:
  forall n ds, dlength (liftDs n ds) = dlength ds.
Proof.
  induction ds.
  + reflexivity.
  + simpl. intuition.
Qed.

Lemma tappend_pres_lifts:
  forall ts ss n, lifts n (tappend ts ss) = tappend (lifts n ts) (lifts n ss).
Proof.
  induction ts; intros.
  - reflexivity.
  - cbn. rewrite IHts. reflexivity.
Qed.
  
Lemma treverse_pres_lifts:
  forall ts n, lifts n (treverse ts) = treverse (lifts n ts).
Proof.
  induction ts; intros.
  - reflexivity.
  - cbn. rewrite <- IHts. rewrite tappend_pres_lifts.
    reflexivity.
Qed.


(** turn (Construct [x1;...;xn; 0;...k-1]])  with arity n+k into
*** (Lam ... (Lam (Construct [x1;...;xn; 0;...k-1])...))
*** lift [x1;...;xn] k times,
*** then append the k fresh variables and surround with k lambdas
**)
(******************************)
Function addDummyArgs n args :=
  match n with
    | 0 => treverse args
    | S m => addDummyArgs m (tcons (TRel 0) (lifts 0 args))
  end.
         
Function mkEtaArgs npars nargs args: Terms :=
  match npars, args with
    | S m, tcons u us => mkEtaArgs m nargs us
    | 0, us => (* removed all params, possibly some args left *)
      (addDummyArgs (nargs - tlength us) (treverse us))
    | _, tnil => (* possibly some params left, no args visible *)
      (addDummyArgs nargs tnil)
  end.
                                               
Lemma addDummyArgs_sanity:
  forall n args, tlength (addDummyArgs n args) = n + (tlength args).
Proof.
  induction n; induction args; cbn in *; intros; try reflexivity.
  - rewrite tunit_treverse. rewrite <- treverse_pres_tlength. reflexivity.
  - rewrite IHn. cbn. omega.
  - rewrite IHn. cbn. rewrite lifts_pres_tlength. omega.
Qed.                                           

Function mkEtaLams (xtraArity:nat) (body:Term) : Term :=
  match xtraArity with
    | 0 => body
    | S n => TLambda nAnon (mkEtaLams n body)
  end.
  
Function etaExp_cnstr
           (i:inductive) (x npars nargs:nat) (args:Terms) : Term :=
  let body := TConstruct i x (mkEtaArgs npars nargs args) in
  mkEtaLams (npars + nargs - (tlength args)) body.


Eval cbn in (etaExp_cnstr (mkInd "" 0) 9 1 2 tnil).
Eval cbn in (etaExp_cnstr (mkInd "" 0) 9 1 2 (tcons (TConst "A") tnil)).
Eval cbn in (etaExp_cnstr (mkInd "" 0) 9 1 2
                          (tcons (TConst "A") (tcons (TConst "b") tnil))).
Eval cbn in (etaExp_cnstr
               (mkInd "" 0) 9 1 2
               (tcons (TConst "A")
                      (tcons (TConst "b") (tcons (TConst "bs") tnil)))).
(********************************)

(************************************
(** oneMore preserves closed **)
Fixpoint oneMore bod : Term :=
  match bod with
  | TConstruct i x args =>
    TLambda nAnon (TConstruct i x (tappend (lifts 0 args) (tunit (TRel 0))))
  | TLambda _ b => TLambda nAnon (oneMore b)
  | _ => TWrong
  end.

Fixpoint manyMore (b:Term) (m:nat) {struct m} :=
      match m with
      | 0 => b
      | S m => manyMore (oneMore b) m
      end.

Function mkEtaLams (xtraArity:nat) (body:Term) : Term :=
  match xtraArity with
    | 0 => body
    | S n => TLambda nAnon (mkEtaLams n body)
  end.

Function etaExp_cnstr
           (i:inductive) (x npars nargs:nat) (args:Terms) : Term :=
  match npars, args with
  | S m, tcons u us => (* more params to remove, more args visible *)
    etaExp_cnstr i x m nargs us
  | 0, us => (* all params gone, [us] are remaining args *)
    manyMore (TConstruct i x us) (nargs - tlength us)
  | _, tnil => (* some params left, no args visible: need more Lams *)
    mkEtaLams npars (manyMore (TConstruct i x tnil) nargs)
  end.

(***********
Eval cbn in (etaExp_cnstr (mkInd "" 0) 9 1 2 tnil).
Eval cbn in (etaExp_cnstr (mkInd "" 0) 9 1 2 (tcons (TConst "A") tnil)).
Eval cbn in (etaExp_cnstr (mkInd "" 0) 9 1 2
                          (tcons (TConst "A") (tcons (TConst "b") tnil))).
Eval cbn in (etaExp_cnstr
               (mkInd "" 0) 9 1 2
               (tcons (TConst "A")
                      (tcons (TConst "b") (tcons (TConst "bs") tnil)))).
********************)
***********************************************)

Function strip (t:L2Term) : Term :=
  match t with
    | L2.compile.TRel n => TRel n
    | L2.compile.TSort s => TProof (TAx (L2.compile.TSort s))
    | L2.compile.TProof t => TProof (strip t)
    | L2.compile.TCast t => TCast (strip t)
    | L2.compile.TProd nm bod => TProof (TAx (L2.compile.TProd nm bod))
    | L2.compile.TLambda nm bod => TLambda nm (strip bod)
    | L2.compile.TLetIn nm dfn bod => TLetIn nm (strip dfn) (strip bod)
    | L2.compile.TApp fn arg args =>
      let sarg := strip arg in
      let sargs := strips args in
      match fn with
        | L2.compile.TConstruct i m npars nargs =>
          etaExp_cnstr i m npars nargs (tcons sarg sargs)
        | _ => TApp (strip fn) sarg sargs
      end
    | L2.compile.TConst nm => TConst nm
    | L2.compile.TAx s => TAx (L2.compile.TConst s)
    | L2.compile.TInd i => TProof (TAx (L2.compile.TInd i))
    | L2.compile.TConstruct i m npars nargs =>
      etaExp_cnstr i m npars nargs tnil
    | L2.compile.TCase (i,_) mch brs => TCase i (strip mch) (stripBs brs)
    | L2.compile.TFix ds n => TFix (stripDs ds) n
    | L2.compile.TWrong => TWrong
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

Lemma strips_tappend:
  forall (ts us:L2.compile.Terms),
    strips (L2.term.tappend ts us) = tappend (strips ts) (strips us).
Proof.
  induction ts; intros.
  - reflexivity.
  - rewrite strips_tcons.
    change
      (strips (L2.compile.tcons t (L2.term.tappend ts us)) =
        tcons (strip t) (tappend (strips ts) (strips us))).
    rewrite <- IHts. rewrite strips_tcons. reflexivity.
Qed.

Lemma strip_pres_dlength:
  forall ds:L2Defs, L2.term.dlength ds = dlength (stripDs ds).
Proof.
  induction ds; intros.
  - reflexivity.
  - cbn. rewrite IHds. reflexivity.
Qed.
                  
Lemma strips_pres_tlength:
  forall ts:L2Terms, L2.term.tlength ts = tlength (strips ts).
Proof.
  induction ts; intros.
  - reflexivity.
  - cbn. rewrite IHts. reflexivity.
Qed.
                  
  
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

(*** from L1g to L2k ***)
Definition program_Program (p:program) : Program Term :=
  stripProgram (L2.compile.program_Program p).

(***
Definition term_Term (e:AstCommon.environ L1g.compile.Term) (t:term) : Term :=
  strip (L2.compile.term_Term e t).
***)
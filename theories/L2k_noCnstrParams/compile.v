
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.Arith.Peano_dec.
Require Import Common.Common.
Require Import Omega.
Require Import L2d.compile.
Require Import L2d.term.

Local Open Scope string_scope.
Local Open Scope bool.
Local Open Scope list.
Set Implicit Arguments.

Definition L2dTerm := L2d.compile.Term.
Definition L2dTerms := L2d.compile.Terms.
Definition L2dBrs := L2d.compile.Brs.
Definition L2dDefs := L2d.compile.Defs.
Definition L2dPgm := Program L2dTerm.
Definition L2dEC := envClass L2dTerm.
Definition L2dEnv := environ L2dTerm.


Inductive Term : Type :=
| TRel       : nat -> Term
| TProof     : Term -> Term
| TLambda    : name -> Term -> Term
| TLetIn     : name -> Term -> Term -> Term
| TApp       : Term -> Term -> Term
| TConst     : string -> Term
(* constructors fully applied: eta expand *)
| TConstruct : inductive -> nat (* cnstr no *) -> Terms (* args *) -> Term
| TCase      : inductive ->
               Term (* discriminee *) -> Brs (* # args, branch *) -> Term
| TFix       : Defs -> nat -> Term
| TWrong     : string -> Term
| TDummy     : string -> Term
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

Lemma tappend_tcons:
  forall ts u us,
    tappend ts (tcons u us) = tappend (tappend ts (tunit u)) us.
Proof.
  intros. rewrite <- tappend_assoc. apply f_equal2; reflexivity.
Qed.

Lemma tappend_pres_tlength:
  forall ts us, tlength (tappend ts us) = (tlength ts) + (tlength us).
Proof.
  induction ts; intros.
  - reflexivity.
  - cbn. rewrite IHts. reflexivity.
Qed.

Fixpoint tdrop n ts : Terms :=
  match n, ts with
  | 0, us => us
  | S m, tnil => tnil
  | S m, tcons _ us => tdrop m us
  end.

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

Definition isApp (t:Term) : Prop :=
  exists fn arg, t = TApp fn arg.
Lemma IsApp: forall fn arg, isApp (TApp fn arg).
  intros. exists fn, arg. reflexivity.
Qed.
Hint Resolve IsApp.
Lemma isApp_dec: forall t, {isApp t}+{~ isApp t}.
  destruct t; try (right; not_isApp). left. auto.
Qed.

    
(** lift a Term over a new binding **)
Function lift (n:nat) (t:Term) : Term :=
  match t with
    | TRel m => TRel (match m ?= n with
                        | Lt => m
                        | _ => S m
                      end)
    | TProof t => TProof (lift n t)
    | TLambda nm bod => TLambda nm (lift (S n) bod)
    | TLetIn nm df bod => TLetIn nm (lift n df) (lift (S n) bod)
    | TApp fn arg => TApp (lift n fn) (lift n arg)
    | TConstruct i x args => TConstruct i x (lifts n args)
    | TCase i mch brs => TCase i (lift n mch) (liftBs n brs)
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


(** Carefully separate various paths to eta expansion of constructors
*** to keep control of the shape (constructor vs lambda) of the result.
**)
Function etaExpand_args_Lam'   (* no more parameters expected *)
         (nargs:nat)            (* inputs *)
         (body:Terms -> Term) (computedArgs:Terms)  (* accumulators *)
          { struct nargs } : Term :=
  match nargs with
  (* no more actual args, no more pars or args expected: finished *)
  | 0 => (fun b => TLambda nAnon (body b)) computedArgs
  (* more actual args than [npars + nargs]: impossible *)
  | S n =>
    etaExpand_args_Lam' n (fun b => TLambda nAnon (TLambda nAnon (body b)))
                   (tappend (lifts 0 computedArgs) (tunit (TRel 0)))
  (* more actual args *)
  end.
(* Functional Scheme etaExpand_args_Lam'_ind := *)
(*   Induction for etaExpand_args_Lam' Sort Prop. *)

Function etaExpand_args_Lam   (* no more parameters expected *)
         (nargs:nat) (actualArgs:Terms)             (* inputs *)
         (body:Terms -> Term) (computedArgs:Terms)  (* accumulators *)
          { struct nargs } : Term :=
  match nargs, actualArgs with
  (* no more actual args, no more pars or args expected: finished *)
  | 0, tnil => body computedArgs
  (* more actual args than [npars + nargs]: impossible *)
  | 0, tcons _ _ => TDummy "strip; Constructor; too many args"
  (* no more actual args but more args expected: eta expand *)
  | S n, tnil =>
    etaExpand_args_Lam' n body
                   (tappend (lifts 0 computedArgs) (tunit (TRel 0)))
  (* more actual args *)
  | S n, tcons u us =>
    etaExpand_args_Lam n us body (tappend computedArgs (tunit u))
  end.
(* Functional Scheme etaExpand_args_Lam_ind' := *)
(*   Induction for etaExpand_args_Lam Sort Prop. *)
                                      
Definition etaExpand_args_Construct   (* no more parameters expected *)
         (nargs:nat) (actualArgs:Terms)             (* inputs *)
         (i:inductive) (m:nat) (* accumulator *)
  : Term :=
  match nargs, actualArgs with
  (* no more actual args, no more pars or args expected: finished *)
  | 0, tnil => TConstruct i m tnil
  (* more actual args than [npars + nargs]: impossible *)
  | 0, tcons u us => TDummy "strip; Constructor; too many args"
  (* no more actual args but more args expected: eta expand *)
  | S n, tnil =>
    etaExpand_args_Lam' n (TConstruct i m ) (tunit (TRel 0))
  (* more actual args *)
  | S n, tcons u us => etaExpand_args_Lam n us (TConstruct i m) (tunit u)
  end.
(***********************                       
  | S 0, tcons u tnil => TConstruct i m (tunit u)
  | S 0, tcons u (tcons _ _) => TWrong "strip; Constructor; too many args"
  | S (S n), tcons u (tcons w ws) =>
    etaExpand_args_Lam n us (TConstruct i m) (tunit u) *)

(** wrap a term with n lambdas; used below for missing parameters **)
Function nLambda (n:nat) (F:Term) : Term :=
  match n with
  | 0 => F
  | S m => TLambda nAnon (nLambda m F)
  end.

Function Lambdan (n:nat) (F:Term) : Term :=
  match n with
  | 0 => F
  | S m => Lambdan m (TLambda nAnon F)
  end.

Lemma pre_nLambda_Lambdan:
  forall (n:nat) (F:Term),
    nLambda n (TLambda nAnon F) = TLambda nAnon (nLambda n F).
Proof.
  induction n; intros.
  - reflexivity.
  - cbn. rewrite IHn. reflexivity.
Qed.
                          
Lemma nLambda_Lambdan:
  forall (n:nat) (F:Term),
    nLambda n F = Lambdan n F.
Proof.
  induction n; intros.
  - reflexivity.
  - cbn. rewrite <- pre_nLambda_Lambdan. rewrite IHn. reflexivity.
Qed.         

Function mkExpand n (F:Terms -> Term) (cArgs:Terms) : Term :=
  match n with
  | 0 => F cArgs
  | S m =>
    TLambda nAnon (mkExpand m F (tappend (lifts 0 cArgs) (tunit (TRel 0))))
  end.

Section ee.   (** drop params, eta expand what's left **)
  Variable (F:Terms -> Term).
  
(** move all of aArgs (which are closed) into cArgs **)
Function etaExpand_aArgs (nargs nlams:nat) (aArgs cArgs:Terms) :=
  match nargs, aArgs with
    (* step through nargs expected and actual args found *)
  | S n, tcons u us => etaExpand_aArgs n nlams us (tappend cArgs (tunit u))
    (* error: more actual args than expected *)
  | 0, tcons _ _ => TDummy "strip; Constructor; too many args"
    (* ran out of actual args; more args expected; finish expanding *)
  | n, tnil => nLambda nlams (mkExpand n F cArgs)
  end.

(** drop actually appearing parameters. if not enough actual params,
    pass a count of the number of non-binding lambdas **)
Function etaExpand (actualArgs:Terms) (npars nargs:nat)  (* inputs *) : Term :=
  match actualArgs, npars with
  (* drop an actual param and reduce param count. keep looking for params *)
  | tcons u us, S n => etaExpand us n nargs
  (* ran out of actual args, but n more params expected:
     need nlams lambdas that don't bind, then eta expand *)
  | tnil, nlams => etaExpand_aArgs nargs nlams tnil tnil
  (* no more params expected; start on actual args and nargs *)
  | aArgs, 0 => etaExpand_aArgs nargs 0 aArgs tnil
  end.
End ee.

Section Strip.
  Variable pre_strip: L2dTerm -> Term.
  Function CanonicalP (fn:L2dTerm) (arg:Term) :
    option ((Terms->Term) * Terms * nat * nat) :=
    match fn with
    | L2d.compile.TConstruct i m np na =>
      Some (TConstruct i m, tunit arg, np, na)
    | L2d.compile.TApp gn brg =>
      match CanonicalP gn (pre_strip brg) with
      | Some (F, brgs, np, na) =>
        Some (F, tappend brgs (tunit arg), np, na)
      | None => None
      end
    | _ => None
  end.
End Strip.

Function strip (t:L2dTerm) : Term :=
  match t with
  | L2d.compile.TRel n => TRel n
  | L2d.compile.TProof t => TProof (TDummy "") (* OS [04/2018]: replace  "TProof (strip t)" to avoid expensive operations on proof terms just before their removal  *)
  | L2d.compile.TLambda nm bod => TLambda nm (strip bod)
  | L2d.compile.TLetIn nm dfn bod => TLetIn nm (strip dfn) (strip bod)
  | L2d.compile.TApp fn arg =>
    let sarg := strip arg in
    match CanonicalP strip fn sarg with
    | None => TApp (strip fn) sarg
    | Some (F, args, npars, nargs) => etaExpand F args npars nargs
    end
  | L2d.compile.TConst nm => TConst nm
  | L2d.compile.TConstruct i m npars nargs =>
    etaExpand (TConstruct i m) tnil npars nargs
  | L2d.compile.TCase i mch brs => TCase (fst i) (strip mch) (stripBs brs)
  | L2d.compile.TFix ds n => TFix (stripDs ds) n
  | L2d.compile.TWrong str => TWrong str
  | L2d.compile.TDummy str => TDummy str
  end
with strips (ts:L2dTerms) : Terms :=
    match ts with
    | L2d.compile.tnil => tnil
    | L2d.compile.tcons u us => tcons (strip u) (strips us)
    end
with stripBs (bs:L2dBrs) : Brs := 
       match bs with
       | L2d.compile.bnil => bnil
       | L2d.compile.bcons n t ts => bcons n (strip t) (stripBs ts)
       end
with stripDs (ts:L2dDefs) : Defs := 
       match ts with
       | L2d.compile.dnil => dnil
       | L2d.compile.dcons nm t m ds => dcons nm (strip t) m (stripDs ds)
       end.

Lemma strip_pres_dlength:
  forall ds:L2dDefs, L2d.term.dlength ds = dlength (stripDs ds).
Proof.
  induction ds; intros.
  - reflexivity.
  - cbn. rewrite IHds. reflexivity.
Qed.
                  
Lemma strips_pres_tlength:
  forall ts:L2dTerms, L2d.term.tlength ts = tlength (strips ts).
Proof.
  induction ts; intros.
  - reflexivity.
  - cbn. rewrite IHts. reflexivity.
Qed.

  
(** environments and programs **)
Function stripEC (ec:L2dEC) : AstCommon.envClass Term :=
  match ec with
  | ecTrm t => ecTrm (strip t)
  | ecTyp _ n itp =>
    (** We stripped the parameters of all constructors *)
    ecTyp Term 0 itp
  end.

Definition  stripEnv : L2dEnv -> AstCommon.environ Term :=
  List.map (fun nmec : string * L2dEC => (fst nmec, stripEC (snd nmec))).

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

Definition stripProgram (p:L2dPgm) : Program Term :=
  {| env:= stripEnv (env p);
     main:= strip (main p) |}.

(*** from L2 to L2k ***)
Definition program_Program (p:program) : Program Term :=
  stripProgram (L2d.compile.program_Program p).

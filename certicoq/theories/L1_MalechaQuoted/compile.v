
(****)
Add LoadPath "../common" as Common.
Add LoadPath "../L0_QuotedCoq" as L0.
(****)

Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.omega.Omega.
Require Import Coq.Bool.Bool.
Require Import Template.Ast.
Require Import Common.Common.
Require Import L0.term.
Require Import L0.program.

Local Open Scope string_scope.
Local Open Scope bool.
Local Open Scope list.
Set Implicit Arguments.
  
(** A slightly cleaned up notion of object term.
*** The simultaneous definitions of [Terms] and [Defs] make
*** inductions over this type long-winded but straightforward.
*** This version contains type fields.
*** There is a special term constructor for axioms, which
*** should be seen as having a type but no value.
**)
(** Assumptions:
*** there are no nested applicatione and every application has an argument
*** every Fixpoint has at least one function
**)
Inductive Term : Type :=
| TRel       : nat -> Term
| TSort      : Srt -> Term
| TCast      : Term -> cast_kind -> Term -> Term
| TProd      : name -> Term (* type *) -> Term -> Term
| TLambda    : name -> Term (* type *) -> Term -> Term
| TLetIn     : name ->
               Term (* dfn *) -> Term (* type *) -> Term (* body *) -> Term
| TApp       : Term -> Term (* first arg must exist *) -> Terms -> Term
| TConst     : string -> Term
| TInd       : inductive -> Term
| TConstruct : inductive -> nat (* index of constructor in type *) -> Term
| TCase      : (nat * list nat) (* # of parameters, args per branch *) ->
               Term (* type info *) -> Term -> Terms -> Term
| TFix       : Defs -> nat -> Term
with Terms : Type :=
| tnil : Terms
| tcons : Term -> Terms -> Terms
with Defs : Type :=
| dnil : Defs
| dcons : name -> Term -> Term -> nat -> Defs -> Defs.
Hint Constructors Term Terms Defs.
Scheme Trm_ind' := Induction for Term Sort Prop
  with Trms_ind' := Induction for Terms Sort Prop
  with Defs_ind' := Induction for Defs Sort Prop.
Combined Scheme TrmTrmsDefs_ind from Trm_ind', Trms_ind', Defs_ind'.
Combined Scheme TrmTrms_ind from Trm_ind', Trms_ind'.
Scheme Trm_ind2 := Induction for Term Sort Type
  with Trms_ind2 := Induction for Terms Sort Type
  with Defs_ind2 := Induction for Defs Sort Type.
Notation prop := (TSort SProp).
Notation set_ := (TSort SSet).
Notation type_ := (TSort SType).
Notation tunit t := (tcons t tnil).

Definition pre_checked_term_Term:
  forall n,
  (forall (t:term), WF_term n t = true -> Term) *
  (forall (ts:list term), WF_terms n ts = true -> Terms) *
  (forall (ds:list (def term)), WF_defs n ds = true -> Defs).
Proof.
  induction n; repeat split; try (solve[cbn; intros; discriminate]).
  destruct IHn as [[j1 j2] j3]; intros x hx; destruct x; cbn in hx;
  try discriminate.
  - exact (TRel n0).
  - apply TSort. destruct s; [ exact SProp | exact SSet | exact SType].
  - destruct (andb_true_true _ _ hx) as [k2 k1].
    refine (TCast (j1 _ k2) c (j1 _ k1)).
  - destruct (andb_true_true _ _ hx) as [k1 k2].
    refine (TProd n0 (j1 _ k1) (j1 _ k2)).
  - destruct (andb_true_true _ _ hx) as [k1 k2].
    refine (TLambda n0 (j1 _ k1) (j1 _ k2)).
  - destruct (andb_true_true _ _ hx) as [z1 k3].
    destruct (andb_true_true _ _ z1) as [k1 k2].
    refine (TLetIn n0 (j1 _ k1) (j1 _ k2) (j1 _ k3)).
  - destruct l. discriminate.
    destruct (andb_true_true _ _ hx) as [z1 k4].
    destruct (andb_true_true _ _ z1) as [z2 k3].
    destruct (andb_true_true _ _ z2) as [k1 k2].
    refine (TApp (j1 _ k2) (j1 _ k3) (j2 _ k4)).
  - exact (TConst s).
  - exact (TInd i).
  - exact (TConstruct i n0).
  - destruct (andb_true_true _ _ hx) as [z1 k3].
    destruct (andb_true_true _ _ z1) as [k1 k2].
    refine (TCase (n0, map fst l) (j1 _ k1) (j1 _ k2) (j2 _ k3)).
  - refine (TFix (j3 _ hx) n).
  - destruct IHn as [[j1 j2] j3]. destruct ts; intros.
    + exact tnil.
    + cbn in H. destruct (andb_true_true _ _ H) as [k2 k1].
      refine (tcons (j1 _ k2) (j2 _ k1)).
  - destruct IHn as [[j1 j2] j3]. destruct ds; intros.   
    + exact dnil.
    + cbn in H.
      destruct (andb_true_true _ _ H) as [z1 k3].
      destruct (andb_true_true _ _ z1) as [k1 k2].
      refine (dcons (dname _ d) (j1 _ k1) (j1 _ k2) (rarg _ d) (j3 _ k3)).
Defined.

(** following definition only works for _ground_ terms t **)
Definition
  checked_term_Term (t:term) : WF_term (termSize t) t = true -> Term :=
  (fst (fst (pre_checked_term_Term (termSize t)))) t.



(** translate Gregory Malecha's [term] into my [Term]
*** (without constructor arity, to be filled in at L2)
**)
Section term_Term_sec.
  Variable A : Set.
  Variable term_Term: A -> exception Term.
  Fixpoint terms_Terms (ts:list A) : exception Terms :=
    match ts with
      | nil => ret tnil
      | cons r rs => do R <- term_Term r;
                     do Rs <- terms_Terms rs;
                     ret (tcons R Rs)
    end.
  Fixpoint defs_Defs (ds: list (def A)) : exception Defs :=
   match ds with
     | nil => ret dnil
     | cons d ds => 
         do Dt <- term_Term (dtype _ d);
         do Db <- term_Term (dbody _ d);
         do Ds <- defs_Defs ds;
         ret (dcons (dname _ d) Dt Db (rarg _ d) Ds)
   end.
End term_Term_sec.
   
Fixpoint term_Term (t:term) : exception Term :=
  match t with
    | tRel n => ret (TRel n)
    | tSort srt =>
      ret (TSort (match srt with 
                    | sProp => SProp
                    | sSet => SSet
                    | sType _ => SType  (* throwing away sort info *)
                  end))
    | tCast tm ck ty =>
      match term_Term ty, term_Term tm with
        | Ret Ty, Ret Tm => ret (TCast Tm ck Ty)
        | _, _ => Exc "term_Term; tCast"
      end
    | tProd nm ty bod =>
      match term_Term ty, term_Term bod with
        | Ret Ty, Ret Bod => ret (TProd nm Ty Bod)
        | _, _ => Exc "term_Term; tProd"
      end
    | tLambda nm ty bod =>
      match term_Term ty, term_Term bod with
        | Ret Ty, Ret Bod => ret (TLambda nm Ty Bod)
        | _, _ => Exc "term_Term; tLambda"
      end
    | tLetIn nm dfn ty bod =>
      match term_Term dfn, term_Term ty, term_Term bod with
        | Ret Dfn, Ret Ty, Ret Bod => ret (TLetIn nm Dfn Ty Bod)
        | _, _, _ => Exc "term_Term; tLetIn"
      end
    | tApp fn us =>
      match term_Term fn, terms_Terms term_Term us with
        | Ret Fn, Ret (tcons arg args) => ret (TApp Fn arg args)
        | _, _ => Exc "term_Term; tApp"
      end
    | tConst pth => ret (TConst pth)
    | tInd ind => ret (TInd ind)
    | tConstruct ind m => ret (TConstruct ind m)
    | tCase npars ty mch brs => 
      match term_Term mch,
            terms_Terms (fun x => term_Term (snd x)) brs,
            term_Term ty
      with
        | Ret Mch, Ret Brs, Ret Ty =>
          let Ars := map fst brs in ret (TCase (npars, Ars) Ty Mch Brs)
        | _, _, _ => Exc "term_Term; tCase"
      end
    | tFix defs m =>
      match defs_Defs term_Term defs with
        | Ret Defs => ret (TFix Defs m)
        | Exc s => Exc ("term_Term; tFix " ++ s)
      end
    | _ => raise "term_Term"
  end.


    
(** environments and programsn **)
Definition envClass := Common.AstCommon.envClass Term.
Definition environ := Common.AstCommon.environ Term.
Definition Program := Common.AstCommon.Program Term.


(** convert Malecha's inductive type package into L1 **)
Definition cnstr_Cnstr (c: string * term * nat) : Cnstr :=
  mkCnstr (fst (fst c)) (snd c).

Definition ibody_ityp (iib:ident * inductive_body) : ityp :=
  let Ctors := map cnstr_Cnstr (ctors (snd iib))
  in mkItyp (fst iib) Ctors.

Definition ibodies_itypPack (ibs:list (ident * inductive_body)) : itypPack :=
  map ibody_ityp ibs.

Fixpoint program_Program
         (p:program) (e:exception environ): exception Program :=
  match p with
    | PIn t =>
      do T <- term_Term t;
      do E <- e;
      ret {| main:= T; env:= E |}
    | PConstr nm t p =>
      do T <- term_Term t;
      program_Program p (econs (epair2 nm (ret (ecTrm T))) e)
    | PType nm npar ibs p =>
      let Ibs := ibodies_itypPack ibs
      in program_Program p (econs (epair2 nm (ret (ecTyp Term npar Ibs))) e)
    | PAxiom nm ty p =>
      do Ty <- term_Term ty;
      program_Program p (econs (epair2 nm (ret (ecAx Term))) e)
  end.

(*********************
Fixpoint checked_program_Program (p:program) (e:environ): Program :=
  match p with
    | PIn t => {| main:= checked_term_Term t; env:= e |}
    | PConstr nm t p =>
      checked_program_Program
        p (cons (nm, ecTrm (checked_term_Term t eq_refl)) e)
    | PType nm npar ibs p =>
      let Ibs := ibodies_itypPack ibs
      in checked_program_Program p (cons (nm, ecTyp Term npar Ibs) e)
    | PAxiom nm ty p =>
      let Ty := checked_term_Term ty in
      checked_program_Program p (cons (nm, ecAx Term) e)
  end.
**************************)

(******************************
Goal
  (forall (n:nat) (menv:AstCommon.environ term) (mmain:term),
         Crct n menv mmain -> n = 0 ->
         forall p:program, menv = env (wf_program.program_mypgm p nil) ->
                           mmain = main (wf_program.program_mypgm p nil) ->
                           exists mp, program_Program p (Ret nil) = Ret mp) /\
(forall (n:nat) (menv:AstCommon.environ term) (ip:itypPack),
   CrctTyp n menv ip -> True).
Proof.
  apply (wf_program.CrctCrctTyp_ind'
        (fun (n:nat) menv (mmain:term) => n = 0 ->
         forall p:program, menv = env (wf_program.program_mypgm p nil) ->
                           mmain = main (wf_program.program_mypgm p nil) ->
                           exists mp, program_Program p (Ret nil) = Ret mp)
        (fun (n:nat) menv (ip:itypPack) => True));
  intros.
  - symmetry in H0. destruct (nil_hom _ H0).
    Check (mkPgm (term_Term x) nil).
  - subst. specialize (H0 eq_refl _ H5). apply H2. reflexivity.


  ; intros; subst.
  - destruct p; cbn.
    + inversion_Clear H. discriminate.
***********************************************)
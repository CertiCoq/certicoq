
(****)
Add LoadPath "../common" as Common.
(****)

Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Template.Ast.
Require Import Common.Common.  (* shared namespace *)

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
| TConstruct : inductive -> nat -> Term
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

Function term_Term (t:term) : exception Term :=
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
(****
Functional Scheme term_Term_ind' := Induction for term_Term Sort Prop
with terms_Terms_ind' := Induction for terms_Terms Sort Prop
with wcbvDEvals_ind' := Induction for defs_Defs Sort Prop.
Combined Scheme term_TermEvalsDEvals_ind
         from term_Term_ind', terms_Terms_ind', wcbvDEvals_ind'.
***)

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

(** Functions to actually convert from Malecha's quoted Coq
*** to the L1 language that we reason about
**)

(****)
Add LoadPath "../common" as Common.
Add LoadPath "../L1_MalechaQuoted" as L1.
(****)

Require Import Lists.List.
Require Import Strings.String.
Require Import Strings.Ascii.
Require Import Arith.Compare_dec.
Require Import L1.term.
Require Import L1.program.

Local Open Scope string_scope.
Local Open Scope bool.
Local Open Scope list.
Set Implicit Arguments.


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
      let srt' := match srt with 
                    | sProp => SProp
                    | sSet => SSet
                    | sType _ => SType  (* throwing away some sort info *)
                  end
      in ret (TSort srt')
    | tCast tm ck ty =>
        do Tm <- term_Term tm;
        do Ty <- term_Term ty;
        ret (TCast Tm ck Ty)
    | tProd nm ty bod =>
        do Ty <- term_Term ty;
        do Bod <- term_Term bod;
        ret (TProd nm Ty Bod)
    | tLambda nm ty bod =>
        do Ty <- term_Term ty;
        do Bod <- term_Term bod;
        ret (TLambda nm Ty Bod)
    | tLetIn nm dfn ty bod =>
        do Dfn <- term_Term dfn;
        do Ty <- term_Term ty;
        do Bod <- term_Term bod;
        ret (TLetIn nm Dfn Ty Bod)
    | tApp fn us => 
        do Fn <- term_Term fn;
        do Us <- terms_Terms term_Term us;
        ret (mkApp Fn Us)
    | tConst pth => ret (TConst pth)
    | tInd ind => ret (TInd ind)
    | tConstruct ind m => ret (TConstruct ind m)
    | tCase n ty mch brs =>
        do Ty <- term_Term ty;
        do Mch <- term_Term mch;
        do Brs <- terms_Terms (fun x => term_Term (snd x)) brs;
        let Ars := List.map fst brs in
        ret (TCase (n,Ars) Ty Mch Brs)
    | tFix defs m =>
        do Defs <- defs_Defs term_Term defs;
        ret (TFix Defs m)
    | _ => raise "term_Term"
end.

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
    | PType nm ibs p =>
      let Ibs := ibodies_itypPack ibs
      in program_Program p (econs (epair2 nm (ret (ecTyp Ibs))) e)
    | PAxiom nm ty p =>
      do Ty <- term_Term ty;
      program_Program p (econs (epair2 nm (ret ecAx)) e)
  end.


(************
Goal forall (t:term) (T:Term), term_Term t = Ret T -> WFApp T.
induction t; intros T h;
try (solve [compute in h; injection h; intuition; subst; auto]);
try (solve [compute in h; discriminate]);
try (solve [injection h; intros; subst; constructor; not_isApp]);
try (solve [simpl in h; destruct (term_Term t1); destruct (term_Term t2);
            simpl in h; try discriminate;
            injection h; intros; subst; constructor; not_isApp]).
- simpl in h; destruct (term_Term t1); destruct (term_Term t2);
  destruct (term_Term t3);
  simpl in h; try discriminate;
  injection h; intros; subst; constructor; not_isApp.
- simpl in h; destruct (term_Term t); simpl in h.
  + discriminate.
  + destruct (terms_Terms l).


try injection h; intros; subst; constructor; try not_isApp. 

- change ((do Tm <- term_Term t1;
           do Ty <- term_Term t2;
           Ret (TCast Tm c Ty)) = Ret T) in h.

unfold ret in h. injection h.

apply wfa1; not_isApp.

- simpl in h; destruct t1; destruct t2; simpl in h; try injection h; intros; subst; constructor; try not_isApp. 

*************)

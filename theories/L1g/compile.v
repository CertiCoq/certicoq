
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.omega.Omega.
Require Import Coq.Bool.Bool.
Require Import Template.Ast.
Require Import Common.Common.
Require Import L1.L1.

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
| TProof     : Term -> Term
| TCast      : Term -> Term -> Term
| TProd      : name -> Term (* type *) -> Term -> Term
| TLambda    : name -> Term (* type *) -> Term -> Term
| TLetIn     : name ->
               Term (* dfn *) -> Term (* type *) -> Term (* body *) -> Term
| TApp       : Term -> Term (* first arg must exist *) -> Terms -> Term
| TConst     : string -> Term
| TAx        : Term
| TInd       : inductive -> Term
| TConstruct : inductive -> nat (* index of constructor in type *) ->
               nat (* arity *) -> Term
| TCase      : (inductive * nat * list nat) (* # of pars, args per branch *) ->
               Term (* type info *) -> Term -> Terms -> Term
| TFix       : Defs -> nat -> Term
| TWrong     : string -> Term
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

(** Printing terms in exceptions for debugging purposes **)
Fixpoint print_template_term (t:term) : string :=
  match t with
    | tRel n => " (" ++ (nat_to_string n) ++ ") "
    | tSort _ => " SRT "
    | tCast _ _ _ => " CAST "
    | tProd _ _ _ => " PROD "
    | tLambda _ _ _ => " LAM "
    | tLetIn _ _ _ _ => " LET "
    | tApp fn args =>
      " (APP" ++ (print_template_term fn) ++ " _ " ++ ") "
    | tConst s => "[" ++ s ++ "]"
    | tInd _ => " IND "
    | tConstruct _ n => " (CSTR " ++ (nat_to_string n) ++ ") "
    | tCase n _ mch _ =>
      " (CASE " ++ (nat_to_string (snd n)) ++ " _ " ++
                (print_template_term mch) ++ " _ " ++") "
    | tFix _ n => " (FIX " ++ (nat_to_string n) ++ ") "
    | _ =>  " Wrong "
  end.

(** needed for compiling L1 to L1g **)
Function tappend (ts1 ts2:Terms) : Terms :=
  match ts1 with
    | tnil => ts2
    | tcons t ts => tcons t (tappend ts ts2)
  end.

Function mkApp (t:Term) (args:Terms) {struct t} : Term :=
  match t with
    | TApp fn b bs => TApp fn b (tappend bs args)
    | fn => match args with
              | tnil => fn
              | tcons c cs => TApp fn c cs
            end
  end.


(************************
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
    refine (TCase (p, map fst l) (j1 _ k1) (j1 _ k2) (j2 _ k3)).
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
****************************)

(** Store strings reversed to make inequality testing faster **)
(***  FIX: DEBUGGIBG ONLY  strip off "Coq.Init." ******)
Fixpoint revStr (str accum: string): string :=
  match str with
    | String "C" (String "o" (String "q" (String "."
       (String "I" (String "n" (String "i" (String "t"
        (String "." x)))))))) => x
    | String "T" (String "o" (String "p" (String "." x))) => x
    | y => y
  end.
 (***
  match str with
    | String asci st => revStr st (String asci accum)
    | EmptyString => accum
  end.
***)
Definition revInd (i:inductive): inductive :=
  match i with
    | mkInd nm m => mkInd (revStr nm EmptyString) m
  end.
Definition rev_npars (np: inductive * nat) :=
  match np with
    | (i, n) => (revInd i, n)
  end.

(** translate Gregory Malecha's [term] into my [Term] **)
Section datatypeEnv_sec.
  Variable e : environ Term.
Section term_Term_sec.
  Variable A : Set.
  Variable term_Term: A -> Term.
  Fixpoint terms_Terms (ts:list A) : Terms :=
    match ts with
      | nil => tnil
      | cons r rs => tcons (term_Term r) (terms_Terms rs)
    end.
  Fixpoint defs_Defs (ds: list (def A)) : Defs :=
   match ds with
     | nil => dnil
     | cons d ds =>
       dcons (dname _ d) (term_Term (dtype _ d))
             (term_Term (dbody _ d))  (rarg _ d) (defs_Defs ds )
   end.
End term_Term_sec.
   
Function term_Term (t:term) : Term :=
  match t with
    | tRel n => (TRel n)
    | tSort srt =>
      TSort (match srt with 
                    | sProp => SProp
                    | sSet => SSet
                    | sType _ => SType  (* throwing away sort info *)
             end)
    | tCast tm _ (tCast _ _ (tSort sProp)) => TProof (term_Term tm)
    | tCast tm _ ty => (TCast (term_Term tm) (term_Term ty))
    | tProd nm ty bod => (TProd nm (term_Term ty) (term_Term bod))
    | tLambda nm ty bod => (TLambda nm (term_Term ty) (term_Term bod))
    | tLetIn nm dfn ty bod =>
      (TLetIn nm (term_Term dfn) (term_Term ty) (term_Term bod))
    | tApp (tApp _ _) us => TWrong "term_Term: nested App"
    | tApp fn nil => TWrong "term_Term: App with no arg"
    | tApp fn (cons u us) => TApp (term_Term fn) (term_Term u)
                                  (terms_Terms term_Term us)
    | tConst pth =>   (* ref to axioms in environ made into [TAx] *)
      let rth := revStr pth EmptyString in
      match lookup rth e with  (* only lookup ecTyp at this point! *)
        | Some (ecTyp _ 0 nil) => TAx  (* note coding of axion in environ *)
        | Some (ecTyp _ _ _) =>
          TWrong ("Const refers to inductive: " ++ pth)
        | _  => TConst rth
      end
    | tInd ind => TInd (revInd ind)
    | tConstruct ind m =>
      match cnstrArity e (revInd ind) m with
        | Ret arty => (TConstruct (revInd ind) m arty)
        | Exc str => TWrong ("term_Term: Cnstr arity not found: " ++ str)
      end
    | tCase npars ty mch brs =>
      let Ars := map fst brs in
      (TCase (rev_npars npars, Ars) (term_Term ty) (term_Term mch)
             (terms_Terms (fun x => term_Term (snd x)) brs))
    | tFix defs m => (TFix (defs_Defs term_Term defs) m)
    | _ => TWrong "term_Term: Unknown term"
  end.

End datatypeEnv_sec.
    
(** environments and programs **)
(** given an L0 program, return an L1 environment containing the
*** datatypes of the program: this can be done without a term 
*** translation function
**)
Fixpoint program_datatypeEnv (p:program) (e:environ Term) : environ Term :=
  match p with
    | PIn _ => e
    | PConstr _ _ p => program_datatypeEnv p e
    | PType nm npar ibs p =>
      let Ibs := ibodies_itypPack ibs in
      program_datatypeEnv p (cons (pair (revStr nm EmptyString)
                                        (ecTyp Term npar Ibs)) e)
    | PAxiom nm _ p =>
      program_datatypeEnv p (cons (pair (revStr nm EmptyString)
                                        (ecTyp Term 0 nil)) e)
  end.

Fixpoint program_Pgm
         (dtEnv: environ Term) (p:program) (e:environ Term) : Program Term :=
  match p with
    | PIn t => {| main:= (term_Term dtEnv t); env:= e |}
    | PConstr nm t p =>
      program_Pgm dtEnv p (cons (pair (revStr nm EmptyString)
                                      (ecTrm (term_Term dtEnv t))) e)
    | PType nm npar ibs p =>
      let Ibs := ibodies_itypPack ibs in
      program_Pgm dtEnv p (cons (pair (revStr nm EmptyString)
                                      (ecTyp Term npar Ibs)) e)
    | PAxiom nm ty p =>
      program_Pgm dtEnv p (cons (pair (revStr nm EmptyString)
                                      (ecAx Term)) e)
  end.

Definition program_Program (p:program) : Program Term :=
  let dtEnv := program_datatypeEnv p (nil (A:= (string * envClass Term))) in
  program_Pgm dtEnv p nil.


(*********************

  Fixpoint program_Pgm (p:program) (e:environ Term): Program Term :=
                                 (* e is an accumulator *)
  let dtEnv := program_datatypeEnv p (nil (A:= (string * envClass Term))) in
  match p with
    | PIn t => {| main:= (term_Term dtEnv t); env:= e |}
    | PConstr nm t p =>
      program_Pgm p (cons (pair nm (ecTrm (term_Term dtEnv t))) e)
    | PType nm npar ibs p =>
      let Ibs := ibodies_itypPack ibs in
      program_Pgm p (cons (pair nm (ecTyp Term npar Ibs)) e)
    | PAxiom nm ty p =>
      program_Pgm p (cons (pair nm (ecAx Term)) e)
  end.


(*** toplevel compilation ***)
Definition program_Program (p:program) := program_Pgm p nil.
********************)


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

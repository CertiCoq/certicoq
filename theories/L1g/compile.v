
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.omega.Omega.
Require Import Coq.Bool.Bool.
Require Import FunInd.
Require Import Common.Common.

Require Import TemplateExtraction.EAst Template.kernel.univ.

Local Open Scope string_scope.
Local Open Scope bool.
Local Open Scope list.
Set Implicit Arguments.

(** TODO move to TemplateExtraction.Ast *)
Arguments dname {term} _.
Arguments dbody {term} _.
Arguments dtype {term} _.
Arguments rarg {term} _.

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
| TProof     : Term
| TLambda    : name -> Term -> Term
| TLetIn     : name -> Term (* dfn *) -> Term (* body *) -> Term
| TApp       : Term -> Term -> Term
| TConst     : string -> Term
| TConstruct : inductive (* inductive type *) -> nat (* constructor # *) ->
               nat (* # pars *) -> nat (* # args *) -> Term
| TCase      : (inductive * nat) (* # of pars *) ->
               Term (* discriminee *) -> Brs (* # args, branch *) -> Term
| TFix       : Defs (* all mutual bodies *)->
               nat (* indx of this body *) -> Term
| TProj   : projection -> Term ->Term
| TWrong     : string -> Term
with Brs: Type :=
| bnil: Brs
| bcons: nat -> Term -> Brs -> Brs
with Defs : Type :=
| dnil : Defs
| dcons : name -> Term -> nat -> Defs -> Defs.
Hint Constructors Term Brs Defs.
Scheme Trm_ind' := Induction for Term Sort Prop
  with Brs_ind' := Induction for Brs Sort Prop
  with Defs_ind' := Induction for Defs Sort Prop.
Combined Scheme TrmTrmsBrsDefs_ind
         from Trm_ind', Brs_ind', Defs_ind'.
Notation Terms := (list Term).
Notation tunit t := (unit t).
Notation btunit n t := (bcons n t bnil).
Notation dunit nm t m := (dcons nm t m dnil).

(** Printing terms in exceptions for debugging purposes **
Fixpoint print_template_term (t:term) : string :=
  match t with
    | tRel n => " (" ++ (nat_to_string n) ++ ") "
    | tLambda _ _ => " LAM "
    | tLetIn _ _ _ => " LET "
    | tApp fn args =>
      " (APP" ++ (print_template_term fn) ++ " _ " ++ ") "
    | tConst s => "[" ++ s ++ "]"
    | tConstruct i n =>
      "(CSTR:" ++ print_inductive i ++ ":" ++ (nat_to_string n) ++ ") "
    | tCase n mch _ =>
      " (CASE " ++ (nat_to_string (snd n)) ++ " _ " ++
                (print_template_term mch) ++ " _ " ++") "
    | tFix _ n => " (FIX " ++ (nat_to_string n) ++ ") "
    | _ =>  " Wrong "
  end.
 *********************)

(** needed for compiling L1 to L1g **
Function tappend (ts1 ts2:Terms) : Terms :=
  match ts1 with
    | tnil => ts2
    | tcons t ts => tcons t (tappend ts ts2)
  end.
 ************)

(** some utility operations on [Terms] ("lists" of Term) **)
Lemma append_mk_canonical:
  forall ts s ss, exists u us, app (A:=Term) ts (cons s ss) = cons u us.
Proof.
  destruct ts; intros s ss; simpl.
  - exists s, ss. reflexivity.
  - exists t, (app ts (cons s ss)). reflexivity.
Qed.

Lemma mk_canonical_append:
  forall us u, exists ts t, cons (A:=Term) u us = ts ++ (unit t).
Proof.
  induction us; intros.
  - exists nil, u. reflexivity.
  - dstrctn (IHus a). rewrite j. exists (u::x), y. reflexivity.
Qed.

(** operations on Brs and Defs **)
Fixpoint blength (ts:Brs) : nat :=
  match ts with 
    | bnil => 0
    | bcons _ _ ts => S (blength ts)
  end.

(** operations on Defs **)
Fixpoint dlength (ts:Defs) : nat :=
  match ts with 
    | dnil => 0
    | dcons _ _ _ ts => S (dlength ts)
  end.

Function dnthBody (n:nat) (l:Defs) {struct l} : option (Term * nat) :=
  match l with
    | dnil => None
    | dcons _ x ix t => match n with
                           | 0 => Some (x, ix)
                           | S m => dnthBody m t
                         end
  end.

Function bnth (n:nat) (l:Brs) {struct l} : option (Term * nat) :=
  match l with
    | bnil => None
    | bcons ix x bs => match n with
                           | 0 => Some (x, ix)
                           | S m => bnth m bs
                       end
  end.

Lemma n_lt_0 : forall n, n < 0 -> Term * nat.
Proof.
  intros. omega.
Defined.

Fixpoint
  dnth_lt (ds:Defs) : forall (n:nat), (n < dlength ds) -> Term * nat :=
  match ds return forall n, (n < dlength ds) -> Term * nat with
  | dnil => n_lt_0
  | dcons nm bod ri es =>
    fun n =>
      match n return (n < dlength (dcons nm bod ri es)) -> Term * nat with
        | 0 => fun _ => (bod, ri)
        | S m => fun H => dnth_lt es (lt_S_n _ _ H)
      end
  end.

(** syntactic control of "TApp": no nested apps, app must have an argument **)
Function mkApp (fn:Term) (ts:Terms) : Term :=
  match ts with
  | nil => fn
  | cons y ys => mkApp (TApp fn y) ys
  end.

Lemma mkApp_idempotent:
  forall ts (fn:Term) (ss:Terms),
    mkApp (mkApp fn ts) ss = mkApp fn (app ts ss).
Proof.
  induction ts; destruct fn; intros; cbn; try reflexivity;
  try rewrite <- IHts; try reflexivity.
Qed.                                                       
  
Lemma mkApp_tnil: forall fn, mkApp fn nil = fn.
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
 
      
(** translate Gregory Malecha's [term] into my [Term] **)
Section datatypeEnv_sec.
  Variable datatypeEnv : environ Term.
  
Section term_Term_sec.
  Variable term_Term: term -> Term.
  (* Fixpoint defs *)
  Fixpoint defs_Defs (ds: list (def term)) : Defs :=
   match ds with
     | nil => dnil
     | cons d ds =>
       dcons (dname d)
             (term_Term (dbody d))  (rarg d) (defs_Defs ds )
   end.
  (* Case branches *)
  Fixpoint natterms_Brs (nts: list (nat * term)) : Brs :=
    match nts with
     | nil => bnil
     | cons (n,t) ds => bcons n (term_Term t) (natterms_Brs ds)
   end.
End term_Term_sec.

Function term_Term (t:term) : Term :=
  match t with
    | tRel n => TRel n
    | tBox => TProof
    | tLambda nm bod => (TLambda nm (term_Term bod))
    | tLetIn nm dfn bod => (TLetIn nm (term_Term dfn) (term_Term bod))
    | tApp fn arg => TApp (term_Term fn) (term_Term arg)
    | tConst pth => (* ref to axioms in environ made into [TAx] *)
      match lookup pth datatypeEnv with  (* only lookup ecTyp at this point! *)
      | Some (ecTyp _ _ _) =>
        TWrong ("term_Term:Const inductive or axiom: " ++ pth)
      | _  => TConst pth
      end
    | tConstruct ind m =>
      match cnstrArity datatypeEnv ind m with
        | Ret (npars, nargs) => TConstruct ind m npars nargs
        | Exc s => TWrong ("term_Term;tConstruct:" ++ s)
      end
    | tCase npars mch brs =>
      TCase npars (term_Term mch) (natterms_Brs term_Term brs)
    | tFix defs m => TFix (defs_Defs term_Term defs) m
    | tProj prj bod => TProj prj (term_Term bod)
    | _ => TWrong "(term_Term:Unknown)"
  end.

End datatypeEnv_sec.
    
(** environments and programs **)
(** given an L0 program, return an L1g environment containing the
*** datatypes of the program: this can be done without a term 
*** translation function
**)
Fixpoint program_Pgm_aux
         (dtEnv: environ Term) (g:global_declarations) (t : term)
         (e:environ Term) : Program Term :=
  match g with
  | nil => {| main := (term_Term dtEnv t); env := e |}
  | ConstantDecl nm cb :: p =>
    let decl :=
        match cb.(cst_body) with
        | Some t => pair nm (ecTrm (term_Term dtEnv t))
        | None => pair nm (ecAx Term)
        end
    in
    program_Pgm_aux dtEnv p t (cons decl e)
  | InductiveDecl nm mib :: p =>
    let Ibs := ibodies_itypPack mib.(ind_bodies) in
    program_Pgm_aux
      dtEnv p t (cons (pair nm (ecTyp Term mib.(ind_npars) Ibs)) e)
  end.

Definition program_Pgm
           (dtEnv: environ Term)
           (p:program) (e:environ Term) : Program Term :=
  let '(gctx, t) := p in
  program_Pgm_aux dtEnv gctx t e.

Definition program_Program_ext (p:program) : Program Term :=
  let dtEnv := program_datatypeEnv
                 (fst p) (nil (A:= (string * envClass Term))) in
  program_Pgm dtEnv p nil.

Require Template.Ast.
Require Import PCUIC.TemplateToPCUIC.
Require Import TemplateExtraction.Extract.

Definition program_Program
           `{F:utils.Fuel} (p:Template.Ast.program) : Program Term :=
  let '(genv, t) := p in
  let gc := (genv, uGraph.init_graph) in
  let genv' := trans_global gc in
  let genv'' := extract_global genv' in
  let t' := extract genv' nil (trans t) in
  match genv'', t' with
  | PCUICChecker.Checked genv', PCUICChecker.Checked t' =>
    (program_Program_ext (genv', t'))
  | _, _ => {| main := TWrong "program_Program"; env := nil |}
  end.

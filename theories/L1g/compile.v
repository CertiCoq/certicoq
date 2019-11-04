From MetaCoq.Template Require Import monad_utils utils.

Import MonadNotation.

Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.omega.Omega.
Require Import Coq.Bool.Bool.
Require Import FunInd.
Require Import Common.Common.

From MetaCoq.Template Require Import utils.
From MetaCoq.Erasure Require Import EAst ETyping.

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

(** Printing terms in exceptions for debugging purposes **)
Fixpoint print_template_term (t:term) : string :=
  match t with
    | tRel n => " (" ++ (nat_to_string n) ++ ") "
    | tBox => "BOX"
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
    | tCoFix _ n => " (COFIX " ++ (nat_to_string n) ++ ") "
    | _ =>  " Wrong "
  end.
 
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

(** for debuggung **)
Fixpoint print_global_declarations (g:global_declarations) : string :=
  match g with
  | cons (ConstantDecl knm _) p => knm ++ print_global_declarations p
  | cons (InductiveDecl knm _) p => knm ++ print_global_declarations p
  | nil => "!"
  end.

(** can compile terms using global_declarations from EAst.v **)
Definition Cstr_npars_nargs
  (g:global_declarations) (ind:inductive) (ncst:nat): exception (nat * nat) :=
  match ind with
  | {| inductive_mind:= knm;  inductive_ind:= nbod |} =>
    match lookup_env g knm with
    | Some (ConstantDecl _ _) =>
      raise ("Cstr_npars_nargs:lookup_env ConstantDecl")
    | None =>
      raise ("Cstr_npars_nargs:lookup_env; "
               ++ knm ++ "," ++ (nat_to_string nbod) ++
               "," ++ (nat_to_string ncst) ++
               "/" ++ print_global_declarations g)
    | Some (InductiveDecl _ {| ind_npars:= npars; ind_bodies:= bodies |}) =>
      match List.nth_error bodies nbod with
      | None => raise ("Cstr_npars_nargs:nth_error bodies")
      | Some  {| ind_ctors := ctors |} =>
        match List.nth_error ctors ncst with
        | Some (_, _, nargs) => ret (npars, nargs)
        | None => raise ("Cstr_npars_nargs:nth_error ctors")
        end
      end
    end
  end.

Function term_Term (g:global_declarations) (t:term) : Term :=
  match t with
    | tRel n => TRel n
    | tBox => TProof
    | tLambda nm bod => (TLambda nm (term_Term g bod))
    | tLetIn nm dfn bod => (TLetIn nm (term_Term g dfn) (term_Term g bod))
    | tApp fn arg => TApp (term_Term g fn) (term_Term g arg)
    | tConst pth =>
      match lookup_env g pth with
      | Some (ConstantDecl _ _) => TConst pth
      | _ => TWrong ("term_Term:Const inductive or axiom: " ++ pth)
      end
    | tConstruct ind ncst =>
      match Cstr_npars_nargs g ind ncst with
      | Ret (npars, nargs) => TConstruct ind ncst npars nargs
      | Exc s => TWrong ("term_Term;tConstruct:" ++ s)
      end
    | tCase npars mch brs =>
      TCase npars (term_Term g mch) (natterms_Brs (term_Term g) brs)
    | tFix defs m => TFix (defs_Defs (term_Term g) defs) m
    | tProj prj bod => TProj prj (term_Term g bod)
    | _ => TWrong "(term_Term:Unknown)"
  end.
    
(*** environments and programs ***)
Definition trans_global_decl (g:global_declarations) (dcl:global_decl) :
  (string * envClass Term) :=
  match dcl with
    | ConstantDecl nm cb =>
      match cb.(cst_body) with
      | Some t => pair nm (ecTrm (term_Term g t))
      | None => pair nm (ecAx Term)
      end
    | InductiveDecl nm mib =>
        let Ibs := ibodies_itypPack mib.(ind_bodies) in
        pair nm (ecTyp Term mib.(ind_npars) Ibs)
  end.  

  
(** given global_declarations (from EAst), return an L1g environment **)
Fixpoint program_Pgm_aux (g:global_declarations) : environ Term :=
  match g with
  | nil => nil
  | gd :: g => cons (trans_global_decl g gd) (program_Pgm_aux g)
  end.

From MetaCoq Require Import SafeChecker.SafeTemplateChecker.
From MetaCoq.SafeChecker Require Import PCUICSafeChecker.
From MetaCoq.PCUIC Require Import TemplateToPCUIC.
From MetaCoq.Erasure Require Import ErasureFunction SafeTemplateErasure.

Existing Instance envcheck_monad.
Import MonadNotation.

Open Scope string_scope.

Definition program_Program (p:Template.Ast.program) : Program Term :=
  let p := fix_program_universes p in
  match erase_template_program p with
  | CorrectDecl (gc, t) =>
    {| main := term_Term gc t;
       env := program_Pgm_aux gc |}
  | EnvError err => 
    let str :=
      match err with
      | AlreadyDeclared id => "Already declared: " ++ id
      | IllFormedDecl id e => "Type error: " ++ PCUICSafeChecker.string_of_type_error e ++ ", while checking " ++ id
      end
    in
    {| main := TWrong ("L1g.program_Program: erase_template_program failed with error:" ++ str); env := nil |}
  end.

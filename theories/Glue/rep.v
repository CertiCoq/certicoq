(*
  Author: Joomy Korkut (joomy@cs.princeton.edu), 2020

  Generator for the [rep] relation for a given Coq type.

  The [rep] function should match on a Coq value of a given type,
  and check if a C value represents that Coq value
  the same way CertiCoq represents it.

  This is similar to the pattern in VST but instead of [T -> val -> mpred],
  our [rep] function has the type [graph -> T -> mtype -> Prop],
  for a given [T].

  This file defines a [Rep] type class containing the [rep] relation,
  and it also defines a MetaCoq program that generates a [Rep] instance
  for a given Coq type.

  Currently our generator works on:
  [x] simple types like [bool]
  [x] recursive types like [nat]
  [ ] mutually recursive types like [even] and [odd]
  [ ] polymorphic types like [option]
  [ ] multi-polymorphic types like [pair]
  [ ] recursive and polymorphic types like [list]
  [ ] recursive and dependent types like [vector]
  [ ] types of sort Prop like [and] or [le]

  Game plan:
  * Take a type constructor (in Coq, not reified) as an input.
  * Recursively quote the type constructor, get a type environment as well.
  * The type environment consists of mutual inductive type declarations.
  * For every type in every mutual block,
    find out if there is a [Rep] instance for it,
    and remember it in a list of lists.
    * In order to find out the [Rep] instance, you have to
      quantify over all parameters and indices.
  * If a block is missing any instance,
    define type class instances for each type in the block.
*)
Require Import Coq.ZArith.ZArith
               Coq.Program.Basics
               Coq.Strings.String
               Coq.Lists.List
               Coq.Lists.ListSet.

Require Import ExtLib.Structures.Monads
               ExtLib.Data.Monads.OptionMonad
               ExtLib.Data.Monads.StateMonad
               ExtLib.Data.String.

From MetaCoq Require Import BasicAst.
Require Import MetaCoq.Template.All.

Require Import glue_utils.

Require CertiCoq.LambdaANF.Prototype.
Module DB.
  (* Uses code written by John Li.
     We should eventually consider making a MetaCoq_utils module. *)
  Import Prototype.

  Definition runGM {A : Type} (m : GM A) : TemplateMonad A :=
    match runStateT m 0%N with
    | inl err => tmFail err
    | inr (t', _) => ret t'
    end.

  (* Takes a named representation, which we hack by using names starting with $,
     and converts it into the de Bruijn representation. *)
  Definition deBruijn (t : term) : TemplateMonad term :=
    runGM (indices_of [] t).

  (* Example usage for deBruijn:

     MetaCoq Run (t <- DB.deBruijn <% fun (x : bool) => x %> ;;
                  tmPrint t).
  *)

  (* Takes a de Bruijn representation and adds $ to local variables,
     and changes [tRel]s to [tVar]s referring to those variabstarting with $. *)
  Definition undeBruijn (initial : list ident) (t : term) : TemplateMonad term :=
    runGM (named_of initial t).

  (* Example usage for undeBruijn:

     MetaCoq Run (t <- DB.undeBruijn nil (tLambda (nNamed "$x") <% bool %> (tVar "$x")) ;;
                  t' <- tmUnquoteTyped (bool -> bool) t ;;
                  tmPrint t).
  *)
End DB.

(* Warning: MetaCoq doesn't use the Monad notation from ExtLib,
  therefore don't expect ExtLib functions to work with TemplateMonad. *)
Import monad_utils.MonadNotation
       ListNotations
       MetaCoqNotations.

Notation "f >=> g" := (fun x => (f x) >>= g)
                      (at level 51, right associativity) : monad_scope.

Variables (graph : Type) (mtype : Type).

Inductive cRep : Set :=
| enum : forall (ordinal : N), cRep
| boxed : forall (ordinal : N) (arity : N), cRep.

Variable fitting_index : graph -> mtype -> cRep -> list mtype -> Prop.

Class Rep (A : Type) : Type :=
  { rep : forall (g : graph) (x : A) (p : mtype), Prop }.


(* Starting generation of [Rep] instances! *)

(* (* Possibly useful code: *)

Record TypeCtorInfo :=
  { type_ctor_kername : kername
  ; type_ctor_inductive : inductive
  ; type_ctor_term : term
  }.

Definition getTypeCtor {kind : Type} (T : kind) : TemplateMonad TypeCtorInfo :=
  '(env, t) <- tmQuoteRec T ;;
  match t with
  | tInd ind _ =>
    let first_kn := inductive_mind ind in
    match lookup first_kn env with
    | Some (InductiveDecl mut) =>
      match nth_error (ind_bodies mut) (inductive_ind ind) with
      | None =>
        tmFail ("Could not find #" ++ string_of_nat (inductive_ind ind)
                ++ " in the mutual type block of " ++ string_of_kername first_kn)
               (* this should never happen *)
      | Some one =>
        ret {| type_ctor_kername := (fst first_kn, ind_name one)
             ; type_ctor_inductive := ind
             ; type_ctor_term := t
             |}
      end
    | _ =>
      tmFail ("Could not find the inductive declaration for "
              ++ string_of_kername first_kn ++ " in the type environment")
             (* this should never happen *)
    end
  | _ =>
    tmPrint T ;; tmFail "is not an inductive type constructor."
  end.

MetaCoq Run (getTypeCtor term).
*)

Definition generate_instance_type
           (ind : inductive)
           (one : one_inductive_body)
           (replacer : term -> term) : TemplateMonad term :=
  (* Convert the type of the type to explicitly named representation *)
  ty <- DB.undeBruijn [] (ind_type one) ;;
  (* Goes over a nested π-type and collects binder names,
     makes up a name where there isn't one.
     It also builds a function to replace the part after the π-binders. *)
  let fix collect
          (t : term) (count : nat) (replacer : term -> term)
          : list ident * (term -> term) :=
    match t with
    | tProd nAnon ty rest =>
        let '(idents, f) := collect rest (S count) replacer in
        let new_name := "$arg" ++ string_of_nat count in
        (new_name :: idents, (fun t' => tProd (nNamed new_name) ty (f t')))
    | tProd (nNamed id) ty rest =>
        let '(idents, f) := collect rest (S count) replacer in
        (id :: idents, (fun t' => tProd (nNamed id) ty (f t')))
    | _ => (nil, replacer)
    end in
  let (names, new) := collect ty 0 replacer in
  let vars := map tVar names in
  (* Fully apply the quantified type constructor.
     If you had [list] initially, now you have [forall (A : Type), list A] *)
  let result := new (tApp (tInd ind []) vars) in
  (* Convert back to de Bruijn notation and return. *)
  DB.deBruijn result.

(* Checks if the given type class instance type has an instance.
   This wrapper function makes type checking easier
   since [tmInferInstance] is dependently typed but we don't need that now. *)
Definition has_instance (A : Type) : TemplateMonad bool :=
  opt_ins <- tmInferInstance (Some all) A ;;
  ret (match opt_ins with | my_Some _ => true | my_None => false end).

(* Constructs the instance type for the type at hand,
   checks if there's an instance for it. *)
Definition find_missing_instance
           (ind : inductive)
           (one : one_inductive_body) : TemplateMonad bool :=
  t <- generate_instance_type ind one (fun t => tApp <% Rep %> [t]) ;;
  t' <- tmUnquoteTyped Type t ;;
  has_instance t'.

(* Take in a [global_env], which is a list of declarations,
   and find the inductive declarations in that list
   that do not have [Rep] instances. *)
Fixpoint find_missing_instances
        (env : global_env) : TemplateMonad (list kername) :=
    match env with
    | (kn, InductiveDecl mut) :: env' =>
      rest <- find_missing_instances env' ;;
      ones <- monad_map_i
                (fun i => find_missing_instance
                            {| inductive_mind := kn ; inductive_ind := i |})
                (ind_bodies mut) ;;
      if (fold_left andb ones true) (* if there are instances for all *)
        then ret rest (* then this one is not missing *)
        else ret (kn :: rest)
    | _ :: env' => find_missing_instances env'
    | nil => ret nil
    end.




Record arg_info : Type :=
  { arg_name : BasicAst.ident
    (* the bound name used in the constructor, inside the pattern *)
  ; p_name : BasicAst.ident
    (* the bound name used in the exists *)
  ; arg_type : term
    (* the term for the main inductive type used *)
    (* TODO think about the fully applied type for polymorphic/dependent types *)
  ; arg_inductive : inductive
    (* the name of the type constructor used in the argument, like [nat], [list], [option] *)
  }.

Fixpoint handle_dissected_args
         (args : list dissected_type)
         (count : nat)
          : TemplateMonad (list arg_info) :=
    match args with
    | nil => ret nil
    | cons (dInd ind) args' =>
      rest <- handle_dissected_args args' (S count) ;;
      let arg_s : BasicAst.ident := ("$arg" ++ string_of_nat count)%string in
      let ex_s : BasicAst.ident := ("$p" ++ string_of_nat count)%string in
      let t : term := tInd ind nil in
      ret ({| arg_name := arg_s
            ; p_name := ex_s
            ; arg_type := t
            ; arg_inductive := ind |} :: rest)
    | cons decl _ =>
      tmPrint decl ;;
      tmFail "Dissected type is not a type"
    end.

Fixpoint make_lambdas
         (args : list arg_info)
         : term -> term :=
  match args with
  | nil => fun x => x
  | arg :: args' =>
    fun x => tLambda (nNamed (arg_name arg))
                     (arg_type arg)
                     (make_lambdas args' x)
  end.

Fixpoint make_exists
         (args : list arg_info)
         : term -> term :=
  match args with
  | nil => fun x => x
  | arg :: args' =>
    fun x => tApp <% ex %>
                  [ <% mtype %>
                  ; tLambda (nNamed (p_name arg))
                            <% mtype %>
                            (make_exists args' x) ]
  end.


Definition t_cons (t : term) (t' : term) : term :=
  tApp <% @cons %> [<% mtype %> ; t ; t'].
Definition t_conses (xs : list term) : term :=
  fold_right t_cons <% @nil mtype %> xs.
Definition t_and (t : term) (t' : term) : term :=
  tApp <% @and %> [t ; t'].

Print one_inductive_body.
Compute (seq 0 4).
Fixpoint make_prop
         (ind : inductive)
         (one : one_inductive_body)
         (ctor : ctor_info)
         (args : list arg_info)
         : TemplateMonad term :=
  let t_g := tVar "$g" in
  let t_p := tVar "$p" in

  let make_prop_base : TemplateMonad term :=
    (* Create the [cRep] for this constructor and evaluate *)
    crep <- tmEval all
              (match ctor_arity ctor with
                | O => enum (N.of_nat (ctor_ordinal ctor))
                | a => boxed (N.of_nat (ctor_ordinal ctor)) (N.of_nat a)
                end) ;;
    t_crep <- tmQuote crep ;;
    (* Create list of [[p0;p1;p2;...]] to pass to [fitting_index] *)
    let l := t_conses (map (fun n => tVar ("$p" ++ string_of_nat n))
                           (seq 0 (ctor_arity ctor))) in
    ret (tApp <% fitting_index %>
              [ t_g ; t_p ; t_crep ; l])
  in

  (* Takes in the order of the argument and the [arg_info], *)
(*      generates the call to [rep] for that argument *)
  let make_arg_prop (arg' : nat * arg_info) : TemplateMonad term :=
    let '(i, arg) := arg' in
    let t_arg := tVar ("$arg" ++ string_of_nat i) in
    let t_p := tVar ("$p" ++ string_of_nat i) in

    (* Check if this is a recursive call to the [rep] we're defining *)
    if eq_inductive ind (arg_inductive arg)
    then
      let t_rep := tVar ("$rep_" ++ ind_name one) in
      ret (tApp t_rep [ t_g ; t_arg; t_p ])
    else
      (* not a recursive call, find the right [Rep] instance *)
      ty <- tmUnquoteTyped Type (arg_type arg) ;;
      opt_ins <- tmInferInstance (Some all) (Rep ty) ;; (* FIXME polymorphic *)
      match opt_ins with
      | my_Some ins =>
        t_ins <- tmQuote ins ;;
        ret (tApp <% @rep %> [ arg_type arg ; t_ins ; t_g ; t_arg; t_p ])
      | my_None =>
          tmFail ("No instance found")
      end
  in
  arg_props <- monad_map make_arg_prop (enumerate_nat args) ;;
  base <- make_prop_base ;;
  ret (fold_right t_and base arg_props).


Definition ctor_to_branch
    (ind : inductive)
      (* the type we're generating for *)
    (one : one_inductive_body)
      (* the single type we're generating for *)
    (tau : term)
      (* reified term of the type we're generating for *)
    (ctor : ctor_info)
      (* a single constructor to generate for *)
    : TemplateMonad (nat * term) :=
  let '(dissected_args, dissected_res) :=
      (* FIXME params *)
      dissect_types nil (dInd ind :: nil) (ctor_type ctor) in
  args <- handle_dissected_args dissected_args O ;;
  prop <- make_prop ind one ctor args ;;
  let t := make_lambdas args (make_exists args prop) in
  ret (ctor_arity ctor, t).

(* Generates a reified match expression *)
Definition matchmaker
    (ind : inductive)
      (* description of the type we're generating for *)
    (one : one_inductive_body)
      (* the single type we're generating for *)
    (tau : term)
      (* reified term of the type we're generating for *)
    (ctors : list ctor_info)
      (* constructors we're generating match branches for *)
    : TemplateMonad term :=
  branches <- monad_map (ctor_to_branch ind one tau) ctors ;;
  ret (tCase (ind, 0)
             (tLambda (nNamed "$y"%string) tau <% Prop %>)
             (tVar "$x")
             branches).


(* Make a single record to use in a [tFix].
   For mutually inductive types, we want to build them all once,
   and define all the [Rep] instances with that. *)
Definition make_fix_single
           (tau : term) (* fully applied type constructor *)
           (ind : inductive)
           (one : one_inductive_body) : TemplateMonad (BasicAst.def term) :=
  let this_name := nNamed ("$rep_" ++ ind_name one)%string in
  prop <- matchmaker ind one tau (process_ctors (ind_ctors one)) ;;
  let body :=
      (tLambda (nNamed "$g"%string) <% graph %>
        (tLambda (nNamed "$x"%string) tau
          (tLambda (nNamed "$p"%string) <% mtype %> prop))) in
  ret {| dname := this_name
       ; dtype := tProd (nNamed "$g"%string)
                       <% graph %>
                       (tProd (nNamed "$x"%string)
                               tau
                               (tProd (nNamed "$p"%string)
                                     <% mtype %>
                                     <% Prop %>))
       ; dbody := body
       ; rarg := 1 |}.

(* Remove all the initial consecutive π-type quantifiers from a [term]. *)
Fixpoint strip_quantifiers (t : term) : term :=
  match t with
  | tProd _ _ rest => strip_quantifiers rest
  | x => x
  end.

(* Get binder names and binding types for all
   initial consecutive π-type quantifiers in a [term]. *)
Fixpoint get_quantifiers (t : term) : list (name * term) :=
  match t with
  | tProd n ty rest => (n, ty) :: get_quantifiers rest
  | x => nil
  end.

(* Given binder names and binding types, add binders to the base [term].
   Can be used to add λs (with [tLambda]) or πs (with [tProd]). *)
Fixpoint build_quantifiers
         (binder : name -> term -> term -> term)
         (l : list (name * term))
         (base : term) : term :=
  match l with
  | nil => base
  | (n, t) :: rest => binder n t (build_quantifiers binder rest base)
  end.

Definition add_instances (kn : kername) : TemplateMonad unit :=
  mut <- tmQuoteInductive kn ;;
  (* Build the single function definitions for each of
     the mutually recursive types. *)
  singles <- monad_map_i
               (fun i one =>
                  (* FIXME get rid of repeated computation here *)
                  let ind := {| inductive_mind := kn ; inductive_ind := i |} in
                  quantified <- generate_instance_type ind one id ;;
                  quantified_named <- DB.undeBruijn [] quantified ;;
                  let tau := strip_quantifiers quantified_named in
                  make_fix_single tau {| inductive_mind := kn ; inductive_ind := i |} one)
               (ind_bodies mut) ;;

  (* Loop over each mutually recursive type again *)
  monad_map_i
    (fun i one =>
       let ind := {| inductive_mind := kn ; inductive_ind := i |} in
       (* This gives us something like
          [forall (A : Type) (n : nat), vec A n] *)
       quantified <- generate_instance_type ind one id ;;
       (* Now what can we do with this?
          Let's start by going to its named representation. *)
       quantified_named <- DB.undeBruijn [] quantified ;;

       (* The reified type of the fully applied type constructor,
          but with free variables! *)
       let tau := strip_quantifiers quantified_named in
       let fn_ty := tProd (nNamed "$g"%string)
                          <% graph %>
                          (tProd (nNamed "$x"%string)
                                 tau
                                 (tProd (nNamed "$p"%string)
                                        <% mtype %>
                                        <% Prop %>)) in
       let quantifiers := get_quantifiers quantified_named in
       let prog_named : term :=
           build_quantifiers tLambda quantifiers
                             (tApp (tConstruct {| inductive_mind := <? Rep ?>
                                                ; inductive_ind := 0 |} 0 [])
                                   [tau; tFix singles i]) in

       (* Convert generated program from named to de Bruijn representation *)
       prog <- DB.deBruijn prog_named ;;

       (* If need be, here's the reified type of our [Rep] instance: *)
       (*    instance_ty <-
               tmUnquoteTyped Type
                 (build_quantifiers tProd quantifiers
                                   (tApp <% Rep %> [quantified])) ;;
       *)

       instance <- tmUnquote prog ;;
       (* Remove [tmEval] when MetaCoq issue 455 is fixed: *)
       (* https://github.com/MetaCoq/metacoq/issues/455 *)
       name <- tmFreshName =<< tmEval all ("Rep_" ++ ind_name one)%string ;;

       (* This is sort of a hack. I couldn't use [tmUnquoteTyped] above
          because of a mysterious type error. (Coq's type errors in monadic
          contexts are just wild.) Therefore I had to [tmUnquote] it to get
          a Σ-type. But when you project the second field out of that,
          the type doesn't get evaluated to [Rep _], it stays as
          [my_projT2 {| ... |}]. The same thing goes for the first projection,
          which is the type of the second projection. When the user prints
          their [Rep] instance, Coq shows the unevaluated version.
          But we don't want to evaluate it [all] the way, that would unfold
          the references to other instances of [Rep]. We only want to get
          the head normal form with [hnf].
          We have to do this both for the instance body and its type. *)
       tmEval hnf (my_projT2 instance) >>=
         tmDefinitionRed_ false name (Some hnf) ;;

       (* Declare the new definition a type class instance *)
       mp <- tmCurrentModPath tt ;;
       tmExistingInstance (ConstRef (mp, name)) ;;

       let fake_kn := (fst kn, ind_name one) in
       tmMsg ("Added Rep instance for " ++ string_of_kername fake_kn) ;;
       ret tt) (ind_bodies mut) ;;
  ret tt.

(* Derives a [Rep] instance for the type constructor [Tau] *)
(*    and the types its definition depends on. *)
Definition rep_gen {kind : Type} (Tau : kind) : TemplateMonad unit :=
  '(env, tau) <- tmQuoteRec Tau ;;
  missing <- find_missing_instances env ;;
  monad_iter add_instances (rev missing).


(* Let's see it in action: *)

MetaCoq Run (rep_gen bool).
Print Rep_bool.

MetaCoq Run (rep_gen nat).
Print Rep_nat.

(* MetaCoq Run (rep_gen list). *)
(* Print Rep_list. *)

Inductive rgx : Type :=
| empty   : rgx
| epsilon : rgx
| literal : string -> rgx
| or      : rgx -> rgx -> rgx
| and     : rgx -> rgx -> rgx
| star    : rgx -> rgx.

MetaCoq Run (rep_gen rgx).
Print Rep_rgx.

Inductive R1 :=
| r1 : R1
with R2 :=
| r2 : R2.

MetaCoq Run (rep_gen R1).
Print Rep_R1.

Inductive T1 :=
| c1 : T2 -> T1
with T2 :=
| c2 : T1 -> T2.

(* MetaCoq Run (rep_gen T1). *)
(* Print Rep_T1. *)

Inductive param_and_index (a b : nat) : a < b -> Type :=
| foo : forall (pf : a < b), param_and_index a b pf.

(* MetaCoq Run (rep_gen param_and_index). *)
(* Print Rep_param_and_index. *)

Inductive indexed : nat -> Type :=
| bar : indexed O.

(* MetaCoq Run (rep_gen indexed). *)
(* Print Rep_indexed. *)

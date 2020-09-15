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
*)
Require Import Coq.ZArith.ZArith
               Coq.Program.Basics
               Coq.Strings.String
               Coq.Lists.List
               Coq.Lists.ListSet.

Require Import ExtLib.Structures.Monads
               ExtLib.Data.Monads.OptionMonad
               ExtLib.Data.String.

From MetaCoq.Template Require Import BasicAst.
Require Import MetaCoq.Template.All.

Require Import glue_utils.

(* Warning: MetaCoq doesn't use the Monad notation from ExtLib,
  therefore don't expect ExtLib functions to work with TemplateMonad *)
Import monad_utils.MonadNotation
       ListNotations.

Notation "f >=> g" := (fun x => (f x) >>= g)
                      (at level 51, right associativity) : monad_scope.
Import MetaCoqNotations.

Variables (graph : Type) (mtype : Type).

Inductive cRep : Set :=
| enum : forall (ordinal : N), cRep
| boxed : forall (ordinal : N) (arity : N), cRep.

Variable fitting_index : graph -> mtype -> cRep -> list mtype -> Prop.

Class Rep (A : Type) : Type :=
  { rep : forall (g : graph) (x : A) (p : mtype), Prop }.

Definition lookup {A : Type} (x : kername) (xs : list (kername * A)) : option A :=
  match find (fun '(y, _) => eq_kername x y) xs with
  | None => None
  | Some (_, a) => Some a
  end.

(* Look in [global_env] for the types mutually recursively
   defined with the type with the given [kername]. *)
Fixpoint find_mutuals
         (kn : kername)
         (env : global_env) : list kername :=
  match env with
  | (kn', InductiveDecl mut) :: env' =>
    if eq_kername kn kn'
    then map (fun b => (fst kn, ind_name b))
             (filter (fun b => negb (eq_string (ind_name b) (snd kn)))
                     (ind_bodies mut))
    else find_mutuals kn env'
  | _ :: env' => find_mutuals kn env'
  | nil => nil
  end.

(* Take in a [global_env], which is a list of declarations,
   and find the inductive declarations in that list
   that do not have [Rep] instances. *)
Fixpoint find_missing_instances
        (env : global_env) : TemplateMonad (list inductive) :=
    match env with
    | (kn, InductiveDecl _) :: env' =>
      rest <- find_missing_instances env' ;;
      let ind := {| inductive_mind := kn ; inductive_ind := 0 |} in
      ty <- tmUnquoteTyped Type (tInd ind nil) ;;
      opt_ins <- tmInferInstance (Some all) (Rep ty) ;; (* FIXME polymorphic *)
      match opt_ins with
      | my_Some _ => ret rest
      | my_None => ret (ind :: rest)
      end
    | _ :: env' => find_missing_instances env'
    | nil => ret nil
    end.

Definition get_mutual_inductive_body
           (ind : inductive) : TemplateMonad mutual_inductive_body :=
  let tau := tInd ind nil in
  Tau <- tmUnquoteTyped Type tau ;;
  '(env, _) <- tmQuoteRec Tau ;;
  let ind_name : kername := inductive_mind ind in
  match lookup ind_name env with
  | Some (InductiveDecl mut) => ret mut
  | _ => tmFail "No inductive declaration found"
  end.

Definition get_one_inductive_body
           (mut : mutual_inductive_body) : TemplateMonad one_inductive_body :=
    match ind_bodies mut with
    | nil => tmFail "No inductive body in type description"
    | _ :: _ :: _ => tmFail "Mutually inductive type description"
    | one :: _ => ret one
    end.

Record arg_info : Type :=
  { arg_name : BasicAst.ident
    (* the bound name used in the constructor, inside the pattern *)
  ; p_name : BasicAst.ident
    (* the bound name used in the exists *)
  ; arg_type : term
    (* the term for the main inductive type used *)
    (* TODO think about the fully applied type for polymorphic/dependent types *)
  ; arg_ind_name : kername
    (* the name of the type constructor used in the argument, like [nat], [list], [option] *)
  }.

Fixpoint handle_dissected_args
         (args : list dissected_type)
         (count : nat)
          : TemplateMonad (list arg_info) :=
    match args with
    | nil => ret nil
    | cons (dInd kn) args' =>
      rest <- handle_dissected_args args' (S count) ;;
      let arg_s : BasicAst.ident := ("arg" ++ string_of_nat count)%string in
      let ex_s : BasicAst.ident := ("p" ++ string_of_nat count)%string in
      let t : term := tInd {| inductive_mind := kn ; inductive_ind := 0 |} nil in
      ret ({| arg_name := arg_s
            ; p_name := ex_s
            ; arg_type := t
            ; arg_ind_name := kn |} :: rest)
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

Fixpoint make_prop
         (ind_name : kername)
           (* name of the type we're generating for *)
         (ctor : ctor_info)
         (args : list arg_info)
         : TemplateMonad term :=
  let twice := ctor_arity ctor * 2 in
  let t_g := tRel (twice + 2) in
  let t_p := tRel (twice) in

  let make_prop_base : TemplateMonad term :=
    (* Create the [cRep] for this constructor and evaluate *)
    crep <- tmEval all
              (match ctor_arity ctor with
                | O => enum (N.of_nat (ctor_ordinal ctor))
                | a => boxed (N.of_nat (ctor_ordinal ctor)) (N.of_nat a)
                end) ;;
    t_crep <- tmQuote crep ;;
    (* Create list of [[p0;p1;p2;...]] to pass to [fitting_index] *)
    let l := t_conses (map tRel (rev (seq 0 (ctor_arity ctor)))) in
    ret (tApp <% fitting_index %>
              [ t_g ; t_p ; t_crep ; l])
  in

  (* Takes in the order of the argument and the [arg_info],
     generates the call to [rep] for that argument *)
  let make_arg_prop (arg' : nat * arg_info) : TemplateMonad term :=
    let '(i, arg) := arg' in
    let t_arg := tRel (twice - 1 - i) in
    let t_p := tRel (ctor_arity ctor - 1 - i) in

    (* Check if this is a recursive call to the rep we're defining *)
    if eq_kername ind_name (arg_ind_name arg)
    then
      let t_rep := tRel (twice + 3) in
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
    (ind_name : kername)
      (* name of the type we're generating for *)
    (tau : term)
      (* reified term of the type we're generating for *)
    (ctor : ctor_info)
      (* a single constructor to generate for *)
    : TemplateMonad (nat * term) :=
  let '(dissected_args, dissected_res) :=
      (* FIXME params *)
      dissect_types nil (dInd ind_name :: nil) (ctor_type ctor) in
  args <- handle_dissected_args dissected_args O ;;
  prop <- make_prop ind_name ctor args ;;
  let t := make_lambdas args (make_exists args prop) in
  ret (ctor_arity ctor, t).

(* Generates a reified match expression *)
Definition matchmaker
    (ind_name : kername)
      (* name of the type we're generating for *)
    (ind : inductive)
      (* description of the type we're generating for *)
    (tau : term)
      (* reified term of the type we're generating for *)
    (ctors : list ctor_info)
      (* constructors we're generating match branches for *)
    : TemplateMonad term :=
  branches <- monad_map (ctor_to_branch ind_name tau) ctors ;;
  ret (tCase (ind, 0)
             (tLambda (nNamed "y"%string) tau <% Prop %>)
             (tRel 1)
             branches).

Definition make_fix (tau : term) (body : term) :=
  tFix
    [{| dname := nNamed "rep'"%string
      ; dtype := tProd (nNamed "g"%string)
                       <% graph %>
                       (tProd (nNamed "x"%string)
                               tau
                               (tProd (nNamed "p"%string)
                                     <% mtype %>
                                     <% Prop %>))
      ; dbody := body
      ; rarg := 1 |}] 0.

Definition add_instance (ind : inductive) : TemplateMonad unit :=
  t_graph <- tmQuote graph ;;
  t_mtype <- tmQuote mtype ;;
  let ind_name : kername := inductive_mind ind in
  let tau : term := tInd ind nil in
  (* TODO untyped unquote to avoid kind issues *)
  Tau <- tmUnquoteTyped Type tau ;;

  mut <- get_mutual_inductive_body ind ;;
  one <- get_one_inductive_body mut ;;
  prop <- matchmaker ind_name ind tau (process_ctors (ind_ctors one)) ;;

  let prog : term :=
    make_fix tau
      (tLambda (nNamed "g"%string) t_graph
        (tLambda (nNamed "x"%string) tau
          (tLambda (nNamed "p"%string) t_mtype prop))) in

  fn <- tmUnquoteTyped (graph -> Tau -> mtype -> Prop) prog ;;
  (* Remove [tmEval] when MetaCoq issue 455 is fixed:
     https://github.com/MetaCoq/metacoq/issues/455 *)
  name <- tmFreshName =<< tmEval all ("Rep_" ++ snd ind_name)%string ;;
  (* FIXME no types are parametrized for now *)
  _ <- tmDefinition name {| rep := fn |} ;;

  (* Declare the new definition a type class instance *)
  mp <- tmCurrentModPath tt ;;
  tmExistingInstance (ConstRef (mp, name)) ;;
  tmMsg ("Added Rep instance for " ++ string_of_kername ind_name).

(* Derives a [Rep] instance for the type constructor [Tau]
   and the types its definition depends on. *)
Definition rep_gen {kind : Type} (Tau : kind) : TemplateMonad unit :=
  '(env, tau) <- tmQuoteRec Tau ;;
  (* let mutuals := find_mutuals _ env in *)
  missing <- find_missing_instances env ;;
  monad_iter add_instance (rev missing).

(* Let's see it in action: *)
MetaCoq Run (rep_gen bool).
MetaCoq Run (rep_gen nat).

Inductive rgx : Type :=
| empty   : rgx
| epsilon : rgx
| literal : string -> rgx
| or      : rgx -> rgx -> rgx
| and     : rgx -> rgx -> rgx
| star    : rgx -> rgx.

MetaCoq Run (rep_gen rgx).
Print Rep_rgx.

Inductive T1 :=
| c1 : T2 -> T1
with T2 :=
| c2 : T1 -> T2.
Check <% T2 %>.
Check ~(tInd {| inductive_mind := (MPfile ["rep"; "Glue"; "CertiCoq"], "T1");
                inductive_ind := 0 |} []).
Check tFix.
Print BasicAst.def.
Search _ (BasicAst.def).

Inductive V :=
| v1 : T1 -> V
| v2 : T2 -> V.
Check <%% V %%>.

Inductive U1 :=
| u1 : U2 -> U1
with U2 :=
| u2 : U3 -> U2
with U3 :=
| u3 : U1 -> U3.
Check <%% U1 %%>.


Fixpoint rep_t1 (g : graph) (x : T1) (p : mtype) : Prop :=
  match x with
  | c1 y => rep_t2 g y p
  end
with rep_t2 (g : graph) (x : T2) (p : mtype) : Prop :=
  match x with
  | c2 y => rep_t1 g y p
  end.
Check (<% fix rep_t1 (x : T1) : Prop := match x with c1 y => rep_t2 y end
        with rep_t2 (x : T2) : Prop := match x with c2 y => rep_t1 y end
        for rep_t1 %>).

(* MetaCoq Run (rep_gen T1). *)
(* MetaCoq Run (rep_gen T2). *)

(* Set Printing All. *)
(* Print Rep_bool. *)
(* Print Rep_color. *)
(* Print Rep_nat. *)
(* Print Rep_T. *)
(* Print Rep_T1. *)
(* Print Rep_T2. *)

(* Inductive nat_list := *)
(* | my_nil : nat_list *)
(* | my_cons : nat -> nat_list -> nat_list. *)

(* MetaCoq Run (rep_gen nat_list). *)
(* Print Rep_nat_list. *)

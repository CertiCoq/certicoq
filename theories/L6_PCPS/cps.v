(* Continuation-Passing Style language for the CertiCoq project.
 *   Initial design, Andrew W. Appel, June 2014
 *)
Require Import Coq.Relations.Relations Coq.ZArith.ZArith Coq.ZArith.Znumtheory
               Coq.Bool.Bool Coq.Lists.List Coq.funind.Recdef.
Require Import ExtLib.Structures.Monad ExtLib.Core.Type.
Require Maps.
Import Nnat.

Require Import List_util.
Require Import HashMap.


(* We will use several maps from identifiers to types, values, etc.
 * For now we'll use Xavier Leroy's efficient polymorphic maps from 
 * positive numbers to _. When the MMaps module of the Coq stdlib is
 * created, we'll use that. *)

Module M := Maps.PTree.
Module T := ExtLib.Core.Type.

Fixpoint getlist {A} (xs: list M.elt) (rho: M.t A) : option (list A) :=
  match xs with 
    | x :: xs' => match M.get x rho, getlist xs' rho with
                    | Some v, Some vs => Some (v::vs)
                    | _, _ => None
                  end
    | nil => Some nil
  end.

Fixpoint setlist {A} (xs: list M.elt) (vs: list A) (rho: M.t A) : option (M.t A) :=
  match xs, vs with
    | x::xs', v::vs' => match setlist xs' vs' rho with
                          | Some rho' => Some (M.set x v rho')
                          | None => None
                        end
    | nil, nil => Some rho
    | _, _ => None
  end.

Definition var := M.elt.   (* value variables *)
Definition type := positive.
Definition tag := M.elt.   (* discrimination tags *)
Definition prim := M.elt. (* primitive operators *)

(* Remark.  It sure would be nice if we could use abstraction here,
   so that M was instantiated differently for vars, types, and tags,
   such that [var] was not beta-eta equal to [type].  But then the
   type of maps [M.t] would have to be abstract, and that in turn
   would mean that Coq could not determine that [M.t(A)] is covariant
   in A.  Which, in turn, would make impossible the inductive definition
   of [val], below. 
 *)


(* To describe the [i]th field of a record, we use type BinNat,
   that is, [N].  This has a more efficient representation than [nat],
   which is a consideration for programs that process large
   abstract syntax trees.
 *)

(* Given a list of tagged variants, return the one with the matching tag. *)
Fixpoint findtag {A} (cl: list (tag * A)) (c: tag) : option A :=
  match cl with
    | (c',a)::cl' => if M.elt_eq c' c then Some a else findtag cl' c
    | nil => None
  end.

(** * CPS Expressions *)

(* Expressions [exp] of the CPS language. *)
Inductive exp : Type :=
| Econstr: var -> type -> tag -> list var -> exp -> exp
| Ecase: var -> list (tag * exp) -> exp
| Eproj: var -> type -> N -> var -> exp -> exp
| Efun: fundefs -> exp -> exp
| Eapp: var -> list var -> exp
| Eprim: var -> type -> prim -> list var -> exp -> exp (* where prim is id *)
(* | Eprim: var -> type -> list var -> exp -> exp *)
with fundefs : Type :=
     | Fcons: var -> type -> list var -> exp -> fundefs -> fundefs
     | Fnil: fundefs.



(* [Econstr x t c ys e] applies a data constructor with tag [c] to
           a list of values denoted by variables [ys].   The resulting
           value is bound to variable [x] of type [t], and then execution
           continues with expression [e].  Static typing requires that
           the typeinfo bound to [t] has a variant consistent with [c]
           and the types of [ys].
    [Ecase v cl] does case-discrimination on value [v], which
           must be a [Vconstr t c vl] value. One of the elements of 
           [cl] must be the pair [(c,e)], where [e] a expression
           that uses [v]. 
           Older approach:  
           One of the elements of [cl] must be the pair [(c,k)], where
           [k] is a continuation; this continuation is then applied to
           the argument [v].  The bound variable of [k] then contains
           the same value as [v], but with a refined type.
    [Eproj v t n y e] projects the record value [y] by selecting
           the [n]th element of the record.   This is bound to [v] of type [t]
           and execution continues with [e].  Typechecking requires
           that the type of [y] be a Tdata with a single variant, whose 
           data list has length at least n.
    [Efun fl e]  binds the set of mutually recursive functions [fl]
           into the environment, and continues with [e].
    [Eapp f ys]   applies the function [f] to arguments [ys]
    [Eprim x t f ys e] applies primop [f] to arguments [ys]
            and binds the result to [x] of type [t], continues with [e].
            The primop [f] is a primitive operator, whose type is equivalent to
            the CPS transform of [ts->t], where [ts] are the type of the [ys].

   [Fdef f t ys e]   defines a function [f] of type [t] with parameters [ys]
             and body [e].  We do not syntactically distinguish continuations 
             from other functions, as Andrew Kennedy does [Compiling with 
             Continuations, Continued, 2007].  Instead, we rely on the type 
             system to do it; see below.  This mechanism also permits
             classifying functions into different calling conventions, even 
             if they have the same source-language type.
 *)

(* Remark.  It is conventional in CPS representations to guarantee
   that no two binding occurrences bind the same variable-name.
   However, neither the static (typing) semantics nor the dynamic
   (small-step) semantics requires this.  Some of the transformation
   (optimization, rewrite) algorithms may require it.
 *)

(** Induction principles for exp *)
Lemma exp_ind' :
  forall P : exp -> Type,
    (forall (v : var) (t : type) (t0 : tag) (l : list var) (e : exp),
       P e -> P (Econstr v t t0 l e)) ->
    (forall (v : var), P (Ecase v nil)) ->
    (forall (v : var) (l : list (tag * exp)) (c : tag) (e : exp),
       P e -> P (Ecase v l) -> P (Ecase v ((c, e) :: l))) ->
    (forall (v : var) (t : type) (n : N) (v0 : var) (e : exp),
       P e -> P (Eproj v t n v0 e)) ->
    (forall (f2 : fundefs) (e : exp), P e -> P (Efun f2 e)) ->
    (forall (v : var) (l : list var), P (Eapp v l)) ->
    (forall (v : var) (t : type) (p : prim) (l : list var) (e : exp),
       P e -> P (Eprim v t p l e)) -> forall e : exp, P e.
Proof.
  intros P H1 H2 H3 H4 H5 H6 H7. fix 1.
  destruct e; try (now clear exp_ind'; eauto).
  - eapply H1. eapply exp_ind'; eauto.
  - induction l as [ | [c e] xs IHxs].
    + eapply H2.
    + eapply H3. apply exp_ind'. eauto.
  - eapply H4. eapply exp_ind'; eauto.
  - eapply H5. eapply exp_ind'; eauto.
  - eapply H7. eapply exp_ind'; eauto.
Qed.

(** Mutual induction scheme for exp and fundefs *)
Lemma exp_mut :
  forall (P : exp -> Type) (P0 : fundefs -> Type),
    (forall (v : var) (t : type) (t0 : tag) (l : list var) (e : exp),
       P e -> P (Econstr v t t0 l e)) ->
    (forall (v : var), P (Ecase v nil)) ->
    (forall (v : var) (l : list (tag * exp)) (c : tag) (e : exp),
       P e -> P (Ecase v l) -> P (Ecase v ((c, e) :: l))) ->
    (forall (v : var) (t : type) (n : N) (v0 : var) (e : exp),
       P e -> P (Eproj v t n v0 e)) ->
    (forall f2 : fundefs, P0 f2 -> forall e : exp, P e -> P (Efun f2 e)) ->
    (forall (v : var) (l : list var), P (Eapp v l)) ->
    (forall (v : var) (t : type) (p : prim) (l : list var) (e : exp),
       P e -> P (Eprim v t p l e)) ->
    (forall (v : var) (t : type) (l : list var) (e : exp),
       P e -> forall f5 : fundefs, P0 f5 -> P0 (Fcons v t l e f5)) ->
    P0 Fnil -> forall e : exp, P e                                 
with fundefs_mut :
  forall (P : exp -> Type) (P0 : fundefs -> Type),
    (forall (v : var) (t : type) (t0 : tag) (l : list var) (e : exp),
       P e -> P (Econstr v t t0 l e)) ->
    (forall (v : var), P (Ecase v nil)) ->
    (forall (v : var) (l : list (tag * exp)) (c : tag) (e : exp),
       P e -> P (Ecase v l) -> P (Ecase v ((c, e) :: l))) ->
    (forall (v : var) (t : type) (n : N) (v0 : var) (e : exp),
       P e -> P (Eproj v t n v0 e)) ->
    (forall f2 : fundefs, P0 f2 -> forall e : exp, P e -> P (Efun f2 e)) ->
    (forall (v : var) (l : list var), P (Eapp v l)) ->
    (forall (v : var) (t : type) (p : prim) (l : list var) (e : exp),
       P e -> P (Eprim v t p l e)) ->
    (forall (v : var) (t : type) (l : list var) (e : exp),
       P e -> forall f5 : fundefs, P0 f5 -> P0 (Fcons v t l e f5)) ->
    P0 Fnil -> forall f7 : fundefs, P0 f7.
Proof.
  - intros P1 P2 H1 H2 H3 H4 H5 H6 H7 H8 H9. 
    destruct e; eauto.
    + eapply H1. eapply exp_mut; eauto.
    + induction l as [ | [c e] xs IHxs].
      * eapply H2.
      * eapply H3; eauto. eapply exp_mut; eauto.
    + eapply H4. eapply exp_mut; eauto.
    + eapply H5. eapply fundefs_mut; eauto.
      eapply exp_mut; eauto.
    + eapply H7. eapply exp_mut; eauto.
  - intros P1 P2 H1 H2 H3 H4 H5 H6 H7 H8 H9 defs. 
    destruct defs; eauto.
    eapply H8. eapply exp_mut; eauto.
    eapply fundefs_mut; eauto.
Qed.

(* to do proofs simultaneously. *)
Lemma exp_def_mutual_ind :
  forall (P : exp -> Prop) (P0 : fundefs -> Prop),
    (forall (v : var) (t : type) (t0 : tag) (l : list var) (e : exp),
       P e -> P (Econstr v t t0 l e)) ->
    (forall (v : var), P (Ecase v nil)) ->
    (forall (v : var) (l : list (tag * exp)) (c : tag) (e : exp),
       P e -> P (Ecase v l) -> P (Ecase v ((c, e) :: l))) ->
    (forall (v : var) (t : type) (n : N) (v0 : var) (e : exp),
       P e -> P (Eproj v t n v0 e)) ->
    (forall f2 : fundefs, P0 f2 -> forall e : exp, P e -> P (Efun f2 e)) ->
    (forall (v : var) (l : list var), P (Eapp v l)) ->
    (forall (v : var) (t : type) (p : prim) (l : list var) (e : exp),
       P e -> P (Eprim v t p l e)) ->
    (forall (v : var) (t : type) (l : list var) (e : exp),
       P e -> forall f5 : fundefs, P0 f5 -> P0 (Fcons v t l e f5)) ->
    P0 Fnil -> (forall e : exp, P e) /\ (forall f : fundefs, P0 f).
Proof.
  intros. split.
  apply (exp_mut P P0); assumption.
  apply (fundefs_mut P P0); assumption.
Qed.

(** name the induction hypotheses only *)
Ltac exp_defs_induction IH1 IHl IH2 :=
  apply exp_def_mutual_ind;
  [ intros ? ? ? ? ? IH1 
  | intros ?
  | intros ? ? ? ? IH1 IHl 
  | intros ? ? ? ? ? IH1
  | intros ? IH2 ? IH1 
  | intros ? ?
  | intros ? ? ? ? ? IH1 
  | intros ? ? ? ? IH1 ? IH2
  | ].

(** * CPS Values *)

Inductive val : Type :=
| Vconstr: type -> tag -> list val -> val
| Vfun: M.t val -> fundefs -> var -> val
(* Vfun env fds f where 
       env is the environment at the function binding site
       fds is the list of mutually recursive functions including f *)
| Vint: Z -> val.


(** Induction principle for values. *)
Lemma val_ind' :
  forall P : val -> Prop,
    (forall (tau : type) (t : tag), P (Vconstr tau t nil)) ->
    (forall (tau : type) (t : tag) (v : val) (l : list val),
       P v -> P (Vconstr tau t l) -> P (Vconstr tau t (v :: l))) ->
    (forall (t : M.t val) (f0 : fundefs) (v : var), P (Vfun t f0 v)) ->
    (forall z : Z, P (Vint z)) ->
    forall v : val, P v.
Proof.
  intros P H1 H2 H3 H4.
  fix 1.
  destruct v; try (now clear val_ind'; eauto).
  - induction l as [ | x xs IHxs].
    eapply H1. eapply H2. apply val_ind'. eauto.
Qed.

Fixpoint def_funs (fl0 fl: fundefs) (rho0 rho: M.t val) : M.t val :=
  match fl with
    | Fcons f t xs e fl' => M.set f (Vfun rho0 fl0 f) (def_funs fl0 fl' rho0 rho)
    | Fnil => rho
  end.

Fixpoint find_def (f: var) (fl:  fundefs) :=
  match fl with
    | Fcons f' t ys e fl' => if M.elt_eq f f' then Some (t,ys,e)
                            else find_def f fl'
    | Fnil => None
  end.


  (** The following are not used anywhere. They have to do either with "well-typedness"
    * or observable values. We need to go through them to decide if can can through them
    * away altogether. *)

(*********** static typing ******************)
Inductive typeinfo : Type :=
| Tdata: list (tag * list type) -> typeinfo
| Tfun: tag -> list type -> typeinfo
| Tother: tag -> typeinfo
| Tunknown.

(* [Tdata (c1 ts1 :: c2 ts2 :: ... )] is a sum-of-products type.
   Each disjunct is tagged with a tag ([c1],[c2],...).   No two disjuncts
   may have the same tag, though the same tag may be used in
   different data types.  Each disjunct is a product (tuple) of 
   fields, with types given by the list [ts].  A tag may stand for any
   of many possible concrete representation strategies.

  [Tfun c ts]   is a (continuation) function that takes [length ts] arguments
    of types [ts] and does not return.  The calling sequence is implied
    by the tag [c]; function types with different tags are incompatible
    and never subtype.

  [Tother c]  allows room for expansion.
 *)
Require Coq.Structures.Orders.
Import RelationClasses.

(* Demonstrate that typeinfo has a computational total order,
   so that we can make a HashMap over it. *)
Module TypeInfo <: Orders.UsualOrderedType.
  Definition t := typeinfo.
  Definition eq := @eq t.
  Definition eq_equiv : Equivalence eq := eq_equivalence.

  Definition lexi {A}{B} (f: A -> A -> comparison) a a' (g: B -> B -> comparison) b b' : comparison :=
    match f a a' with Lt => Lt | Eq => g b b' | Gt => Gt end.

  Fixpoint compare_list {A} (f: A -> A -> comparison) (al bl: list A) : comparison := 
    match al, bl with
      | a::al', b::bl' => lexi f a b (compare_list f) al' bl'
      | nil, _::_ => Lt
      | _::_, nil => Gt
      | nil, nil => Eq
    end.

  Fixpoint compare_pair {A}{B} (f: A -> A -> comparison) (g: B -> B -> comparison)
           (x: A*B) (y: A*B) : comparison :=
    lexi f (fst x) (fst y) g (snd x) (snd y).

  Fixpoint compare (x y : t) : comparison :=
    match x, y with
      | Tdata tl, Tdata tl' => 
        compare_list (compare_pair Pos.compare (compare_list Pos.compare)) tl tl'
      | Tdata _, _ => Lt
      | _, Tdata _ => Gt
      | Tfun c tl, Tfun c' tl' => lexi Pos.compare c c' (compare_list Pos.compare) tl tl'
      | Tfun _ _, _ => Lt
      | _, Tfun _ _ => Gt
      | Tunknown, _ => Lt
      | _, Tunknown => Gt
      | Tother c, Tother c' => Pos.compare c c'
    end.

  Definition lt (x y: t) : Prop := compare x y = Lt.
  Lemma lt_strorder: StrictOrder lt.
  Proof.
  Admitted.

  Lemma lt_compat:  Morphisms.Proper
                      (Morphisms.respectful Logic.eq (Morphisms.respectful Logic.eq iff)) lt.
  Proof.
    hnf; intros. subst. split; subst; auto.
  Qed.

  Lemma compare_spec :
    forall x y : t, CompareSpec (x = y) (lt x y) (lt y x) (compare x y).
  Proof.
    intros.
    destruct (compare x y) eqn:?H;  constructor.
    admit.
    auto.
    admit.
  Admitted.

  Lemma eq_dec : forall x y : t, {x = y} + {x <> y}.
  Proof.
    intros.
    pose proof (compare_spec x y).
    destruct (compare x y).
    left; inversion H; auto.
    right; inversion H; intro; subst y; destruct (lt_strorder) as [H2 _]. apply (H2 x); auto.
    right; inversion H; intro; subst y; destruct (lt_strorder) as [H2 _]. apply (H2 x); auto.
  Defined.
End TypeInfo.

Module TDict := HashMap.MakeHashMap TypeInfo.
Definition tdict := TDict.t.
(* mapping from type to typeinfo.
   We use a HashMap for this, so that for any typeinfo we can
   find its (unique) index (i.e., "type"), and for any type we can
   look up the typeinfo.  *)

(* Remark. Stack-allocated continuations (and stack-allocated data records)
   must not "escape upwards", i.e. they must not be stored into data records
   nor passed to stack-allocated continuation functions.  This discipline is
   enforced by the tagging system.  The type of a function (or data record)
   includes its tag.  It must always be possible to partition the tags into
   two sets, the escaping and the nonescaping, such that nonescaping
   functions have all nonescaping parameters.  This is a wellformedness
   property of a tdict:  [tdict_wellformed TD]
 *)

Definition may_escape_type (TD: tdict) (may_escape: tag -> bool) (t: type) : bool :=
  match TDict.get t TD with
    | Some (Tdata cl) => existsb (Basics.compose may_escape fst) cl
    | Some (Tfun c _) => may_escape c
    | Some (Tother c) => may_escape c
    | _ => true
  end.

Definition tdict_type_ok (TD: tdict) (may_escape: tag -> bool) : Prop :=
  forall t,
    match t with             
      | Some (Tfun c tl) => 
        may_escape c = false ->
        existsb (may_escape_type TD may_escape) tl = false
      | _ => True
    end.

Definition tdict_wellformed (TD: tdict) : Type := sig (tdict_type_ok TD).

Definition tag_primcall : tag := 1%positive. (* tag for calling primitive functions *)
Definition tag_primreturn : tag := 2%positive. (* tag for "returning" from 
    primitive functions.  Primitive functions are all inlined, so they don't
    actually return, but the type system needs this place-holder tag. *)

Inductive subtype (TD: tdict): type -> type -> Prop :=
| subtype_refl: forall i, 
                  subtype TD i i
| subtype_i: forall (i j: type) (t u: typeinfo),
               TDict.get i TD = Some t ->
               TDict.get j TD = Some u ->
               subtypeinfo TD t u ->
               subtype TD i j
with subtypeinfo (TD: tdict): typeinfo -> typeinfo -> Prop :=
     | subtype_data: forall tl tl',
                       subtype_clist TD tl tl' ->
                       subtypeinfo TD (Tdata tl) (Tdata tl')
     | subtype_fun: forall c tl tl',
                      subtype_list TD tl' tl ->
                      subtypeinfo TD (Tfun c tl) (Tfun c tl')
     | subtype_irefl: forall t,
                        subtypeinfo TD t t
with subtype_clist  (TD: tdict): list (tag* list type) -> list (tag* list type) -> Prop :=
     | subtype_here: forall c t tl t' tl',
                       subtype_list TD t t' ->
                       subtype_clist TD tl tl' ->
                       subtype_clist TD ((c,t)::tl) ((c,t')::tl')
     | subtype_skip: forall c t tl tl',
                       subtype_clist TD tl tl' ->
                       subtype_clist TD tl ((c,t)::tl')
     | subtype_cnil: subtype_clist TD nil nil
with subtype_list (TD: tdict): list type -> list type -> Prop :=
     | subtype_cons: forall t tl t' tl',
                       subtype TD t t' ->
                       subtype_list TD tl tl' ->
                       subtype_list TD (t::tl) (t'::tl')
     | subtype_nil: subtype_list TD nil nil.

Definition tenv := M.t type.

Require Import ExtLib.Structures.Monads.
Require Import ExtLib.Data.Monads.OptionMonad.
Import MonadNotation.
Open Scope monad_scope.

(* this might even work, but it's not general enough to be useful:

Definition getSome {A} {B}  (f: A -> option B) (o: option A) :=
  match o with None => None | Some x => f x end.

Notation "'let' 'Some' x '<-' c1 ;; c2" := 
     (@pbind option _ _ _ _ c1 (getSome (fun x => c2)))
    (at level 100, c2 at next level, c1 at next level, right associativity) : monad_scope.
 *)

(* [cl_of_casecont TD Gamma ct] is given a list of tagged continuations,
     and returns the corresponding list of tagged typelists, by looking 
     up each continuation (variable) to get the types of its parameters. 
 *)
Definition cl_of_casecont (TD: tdict) (Gamma: tenv) (ct: tag*var) 
: option (tag * list type) :=
  t' <- M.get (snd ct) Gamma ;;
  f <- TDict.get t' TD ;;
  match f with
    | Tfun c2 (t2::nil) =>
      d <- TDict.get t2 TD ;;
        match d with
          | (Tdata ((c,t3)::nil)) => ret (fst ct, t3)
          | _ => None
        end
    | _ => None end.

Fixpoint fundefs_lists (f: fundefs) : (list var * list type * list (list var) * list exp)%type :=
  match f with
    | Fcons x t ys e' f' => match fundefs_lists f' with
                              | (xs, ts, yss, es) => (x::xs, t::ts, ys::yss, e'::es)
                            end
    | Fnil => (nil,nil,nil,nil)
  end.

Inductive welltyped (TD: tdict): forall (Gamma: tenv) (e: exp), Prop :=
| WTconstr: forall tll (tl ytl: list type) (Gamma: tenv) x t c ys e,
              TDict.get t TD = Some (Tdata tll) ->
              findtag tll c = Some tl ->
              getlist ys Gamma = Some ytl ->
              subtype_list TD ytl tl ->
              welltyped TD (M.set x t Gamma) e ->
              welltyped TD Gamma (Econstr x t c ys e)
| WTcase: forall Gamma y t (tl : list (tag * list type))  cl,
            M.get y Gamma = Some t ->
            TDict.get t TD = Some (Tdata tl) ->
            Forall (fun te => welltyped TD Gamma (snd te)) cl ->
            welltyped TD Gamma (Ecase y cl)
| WTproj: forall ty c tl t' Gamma x t n y e,
            M.get y Gamma = Some ty ->
            TDict.get ty TD = Some (Tdata ((c,tl)::nil)) ->
            nthN tl n = Some t' ->
            subtype TD t' t ->
            welltyped TD (M.set x t Gamma) e ->
            welltyped TD Gamma (Eproj x t n y e)
| WTfun: forall (Gamma Gamma': tenv) fl e,
           match fundefs_lists fl with (xs,ts,yss,es) => setlist xs ts Gamma = Some Gamma' end ->
           welltyped_funbodies TD Gamma' fl ->
           welltyped TD Gamma' e ->
           welltyped TD Gamma (Efun fl e)
| WTapp: forall Gamma t c tl ytl f ys,
           M.get f Gamma = Some t ->
           TDict.get t TD = Some (Tfun c tl) ->
           getlist ys Gamma = Some ytl ->
           subtype_list TD ytl tl ->
           welltyped TD Gamma (Eapp f ys)
| WTprim: forall tf ts tk ts' t' Gamma x t f ys e,
            getlist (f::ys) Gamma = Some (tf::ts) ->
            TDict.get tf TD = Some (Tfun tag_primcall (tk::ts')) ->
            TDict.get tk TD = Some (Tfun tag_primreturn (t'::nil)) ->
            subtype_list TD ts ts' ->
            subtype TD t' t ->
            welltyped TD (M.set x t Gamma) e ->
            welltyped TD Gamma (Eprim x t f ys e)                   
with welltyped_funbodies (TD: tdict): forall (Gamma: tenv) (fbody: fundefs), Prop :=
     | WTbody: forall tl Gamma Gamma' f c t ys e fbody',
                 TDict.get t TD = Some (Tfun c tl) ->
                 setlist ys tl Gamma = Some Gamma'  ->
                 welltyped TD Gamma' e ->
                 welltyped_funbodies TD Gamma (Fcons f t ys e fbody')
     | WTnil: forall Gamma, welltyped_funbodies TD Gamma Fnil.

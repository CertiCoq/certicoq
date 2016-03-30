(* Continuation-Passing Style language for the CertiCoq project.
 *   Initial design, Andrew W. Appel, June 2014
 *)
Require Import Coq.Relations.Relations.
Require Import ExtLib.Structures.Monad.
Require ExtLib.Core.Type.
Require Import ZArith.
Require Import Znumtheory.
Require Import Bool.
Require Import List.
Require Maps.
Require Recdef.
Import Nnat.



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

Function nthN {A: Type} (al: list A) (n: N) : option A :=
 match al, n with
 | a::al', 0%N => Some a
 | a::al', _ => nthN al' (n-1)%N
 | _, _ => None
 end.


Fixpoint mapopt {A} (al: list (option A)) : option (list A) :=
 match al with 
 | Some a :: al' => match mapopt al' with
                              | Some bl' => Some (a::bl')
                              | None => None
                             end
 | None :: _ => None
 | nil => Some nil
 end.

(* Given a list of tagged variants, return the one with the matching tag. *)
Fixpoint findtag {A} (cl: list (tag * A)) (c: tag) : option A :=
  match cl with
  | (c',a)::cl' => if M.elt_eq c' c then Some a else findtag cl' c
  | nil => None
  end.

(* Expressions [exp] of the CPS language. *)
Inductive exp : Type :=
| Econstr: var -> type -> tag -> list var -> exp -> exp
| Ecase: var -> list (tag * var) -> exp
| Eproj: var -> type -> N -> var -> exp -> exp
| Efun: fundefs -> exp -> exp
| Eapp: var -> list var -> exp
| Eprim: var -> type -> prim -> list var -> exp -> exp (* where prim is id *)
(* | Eprim: var -> type -> list var -> exp -> exp *)
with fundefs : Type :=
| Fcons: var -> type -> list var -> exp -> fundefs -> fundefs
| Fnil: fundefs.

Scheme exp_mut := Induction for exp Sort Prop
                            with fundefs_mut := Induction for fundefs Sort Prop.

(* [Econstr x t c ys e] applies a data constructor with tag [c] to
           a list of values denoted by variables [ys].   The resulting
           value is bound to variable [x] of type [t], and then execution
           continues with expression [e].  Static typing requires that
           the typeinfo bound to [t] has a variant consistent with [c]
           and the types of [ys].
    [Ecase v cl] does case-discrimination on value [v], which
           must be a [Vconstr t c vl] value.  One of the elements of 
           [cl] must be the pair [(c,k)], where [k] is a continuation;
           this continuation is then applied to the argument [v].
           The bound variable of [k] then contains the same value as [v],
           but with a refined type.
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

Ltac inv H := inversion H; clear H; subst.

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
Definition tdict := TDict.t.  (* mapping from type to typeinfo.
   We use a HashMap for this, so that for any typeinfo we can
   find its (unique) index (i.e., "type"), and for any type we can
   look up the typeinfo.
 *)

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
 match f with Tfun c2 (t2::nil) => d <- TDict.get t2 TD ;;
 match d with (Tdata ((c,t3)::nil)) => ret (fst ct, t3)
 | _ => None end
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
| WTcase: forall Gamma y t (tl tl': list (tag * list type))  cl,
      M.get y Gamma = Some t ->
      TDict.get t TD = Some (Tdata tl) ->
      map (cl_of_casecont TD Gamma) cl = map Some tl' ->
      subtype_clist TD tl tl' ->
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


(*********** evaluation ********************)

Inductive val : Type :=
| Vconstr: type -> tag -> list val -> val
| Vfun: M.t val -> fundefs -> var -> val
(* Vfun env fds f where 
       env is the environment at the function binding site
       fds is the list of mutually recursive functions including f *)
| Vint: Z -> val
| Vother: type -> val
(* OSB: add constructor for observer functions *)
| Vobvs: type -> val
(* Constructor to return values to the environment. 
 * Correspons to Obs with the difference that the values
 * in the list need not be observable. The type is the 
 * type of the observe *)
| Vobservable : type -> list val -> val.

Definition env := M.t val.  (* An [env]ironment maps [var]s to their [val]ues *)

(*
Inductive type_of_val : val -> type -> Prop :=
| TVconstr: type_of_val (Vconstr t _ _) t
| TVfun: type_of_val (?? ) t
| TVint: type_of_val (Vint _) ?   
| TVother: type_of_val (Vother t) t
| TVobvs : type_of_val (Vobs t) t   
. *)



Fixpoint def_funs (fl0 fl: fundefs) (rho0 rho: env) : env :=
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

Definition state := (env*exp)%type.

Definition prims := M.t (list val -> option val).

Section PRIMS.

  Variable pr: prims.  


(* small step semantics *)
Inductive step: state -> state -> Prop := 
| Step_constr: forall vs rho x t n ys e,
          getlist ys rho = Some vs ->
          step (rho, Econstr x t n ys e) (M.set x (Vconstr t n vs) rho, e)
| Step_proj: forall t' n' vs v rho x t n y e,
          M.get y rho = Some (Vconstr t' n' vs) ->
          nthN vs n = Some v ->
          step (rho, Eproj x t n y e) (M.set x v rho, e)
| Step_case: forall t c vl k rho y cl,
          M.get y rho = Some (Vconstr t c vl) ->
          findtag cl c = Some k ->
          step (rho, Ecase y cl) (rho, Eapp k (y::nil))
| Step_fun: forall rho fl e,
          step (rho, Efun fl e) (def_funs fl fl rho rho, e)
| Step_app: forall rho' fl f' vs xs e rho'' rho f t ys,
          M.get f rho = Some (Vfun rho' fl f') ->
          getlist ys rho = Some vs ->
          find_def f' fl = Some (t,xs,e) ->
          setlist xs vs (def_funs fl fl rho' rho') = Some rho'' ->
          step (rho, Eapp f ys) (rho'', e)
| Step_prim: forall vs v rho' rho x t f f' ys e,
          getlist ys rho = Some vs ->
          M.get f pr = Some f' ->
          f' vs = Some v ->
          M.set x v rho = rho' ->
          step (rho, Eprim x t f ys e) (rho', e).

Definition stepf (s: env * exp) : option (env * exp) := 
  let (rho,e) := s in
  match e with
  | Econstr x t n ys e => 
      vs <- getlist ys rho ;; 
      ret (M.set x (Vconstr t n vs) rho, e)
  | Eproj x t n y e =>
     match M.get y rho with Some (Vconstr t' n' vs) =>
            v <- nthN vs n ;; ret (M.set x v rho, e)
     | _ => None end
 | Ecase y cl =>
    match M.get y rho with Some (Vconstr t c vl) =>
           k <- findtag cl c ;; ret (rho, (Eapp k (y::nil)))
    | _ => None end
  | Efun fl e => 
      ret (def_funs fl fl rho rho, e)
  | Eapp f ys =>
       match M.get f rho with Some (Vfun rho' fl f') =>
       vs <- getlist ys rho ;;
       match find_def f' fl with Some (t',xs,e) =>
       rho'' <- setlist xs vs (def_funs fl fl rho' rho') ;;
       ret (rho'', e)
       | _ => None end
       | _ => None end
  | Eprim x t f ys e =>
       vs <- getlist ys rho ;;
       f' <- M.get f pr ;;
       v <- f' vs ;;
       ret (M.set x v rho, e)
 end.

Lemma step_stepf:
  forall s s',
      step s s' ->
      stepf s = Some s'.
Proof.
intros [rho e] [rho' e'] H;
inv H; simpl;
repeat match goal with
            | H: ?A= _ |- match ?A with _ => _ end = _ => rewrite H 
            end; 
  auto.
Qed.

Lemma stepf_step:
  forall s s',
   stepf s = Some s' ->
   step s s'.
Proof.
intros [rho e] [rho' e'] H.
destruct e; simpl in H; 
repeat 
  match goal with
  | H: match ?A with _ => _ end = Some _ |- _ => destruct A eqn:?; inv H
  | H: Some _ = Some _ |- _ => inv H
  end;
  try solve [econstructor; eauto].
Qed.



(* multi step *)
Inductive mstep: state -> state -> Prop :=
  | s_step: forall s1 s2 s3, step s1 s2 -> mstep s2 s3 -> mstep s1 s3
  | z_step: forall s, mstep s s.



Inductive observable_val: val -> Prop :=
  | obv_int : forall i, observable_val (Vint i)
  | obv_obvs : forall t, observable_val (Vobvs t)
.                                        


(* may want to force all vals in the list to be observable? *)
Inductive obs_val: Type :=
| Obs : forall vs:list val, type -> Forall observable_val vs -> obs_val.
                              


(* big step *)

Inductive bstep_e : env -> exp -> obs_val -> Prop :=
| BStep_app_obs:
    forall rho t ys vs f,
      forall vsobs:Forall observable_val vs, 
      M.get f rho = Some (Vobvs t) ->
      getlist ys rho = Some vs ->
      bstep_e rho (Eapp f ys) (Obs vs t vsobs)

| BStep_constr :
    forall x t n ys e rho rho' vs v ,
      getlist ys rho = Some vs ->
      M.set x (Vconstr t n vs) rho = rho' ->
      bstep_e rho' e v ->
      bstep_e rho (Econstr x t n ys e) v
| BStep_proj: forall t' n' vs v rho x t n y e ov,
               M.get y rho = Some (Vconstr t' n' vs) ->
               nthN vs n = Some v ->
               bstep_e (M.set x v rho) e ov ->
               bstep_e rho (Eproj x t n y e) ov 
               
| BStep_case :
    forall y v k c cl vl t rho rho',
    M.get y rho = Some (Vconstr t c vl) ->
    findtag cl c = Some k ->
    bstep_e rho' (Eapp k (y::nil)) v ->
    bstep_e rho (Ecase y cl) v
| BStep_app_fun :
    forall rho' fl f' vs xs e rho'' rho f t ys v,
                    M.get f rho = Some (Vfun rho' fl f') ->
                    getlist ys rho = Some vs ->
                    find_def f' fl = Some (t,xs,e) ->
                    setlist xs vs (def_funs fl fl rho' rho') = Some rho'' ->
                    bstep_e rho'' e v ->
                    bstep_e rho (Eapp f ys) v
| BStep_fun: forall rho fl e v,
               bstep_e (def_funs fl fl rho rho) e v ->
               bstep_e rho (Efun fl e) v
| BStep_prim: forall vs  rho' rho x t f f' ys e v v',
          getlist ys rho = Some vs ->
          M.get f pr = Some f' ->
          f' vs = Some v ->
          M.set x v rho = rho' ->
          bstep_e rho' e v'  ->
          bstep_e rho (Eprim x t f ys e) v'.


(* if only consider ints and observers (i.e observable_val), syntactic equality on val is the desired notion of equality. *)
Theorem forall2_eq_rel:
  forall (X:Type) (R:relation X), Equivalence R -> Equivalence (Forall2 R).
Proof.
  intros. inversion H. constructor.
  + red. intros. induction x. constructor. constructor. apply Equivalence_Reflexive. assumption.
  + red. intro x. induction x; intros. inversion H0. constructor. inversion H0; subst.   apply IHx in H5. constructor. apply (Equivalence_Symmetric _ _ H3). assumption.
  +   red. induction x; intros.
        * inversion H0; subst; inversion H1. constructor.
        *  inversion H0; subst; inversion H1; subst. constructor. eapply Equivalence_Transitive. apply H4. assumption. apply (IHx _ _ H6) in H8. assumption.
Qed.


Definition val_proper: val -> Prop := observable_val. 
Definition val_equiv: val -> val -> Prop := @eq val. 

Theorem val_equiv_eq_rel: Equivalence (val_equiv).
Proof.
  constructor; red.
  + intros. reflexivity.
  + intros. inversion H. reflexivity.
  + intros. inversion H. inversion H0. reflexivity.
Qed.  
  
Definition obs_val_proper: obs_val -> Prop := fun _ => True.
Definition obs_val_equiv: relation obs_val :=
  fun vso1 vso2 => match vso1, vso2 with
                     | Obs vs1 t1 vsop1, Obs vs2 t2 vsop2 => Forall2 (val_equiv) vs1 vs2 end.


Theorem obs_val_equiv_eq_rel: Equivalence (obs_val_equiv).
Proof.
  assert (Equivalence (Forall2 val_equiv)). apply forall2_eq_rel. apply val_equiv_eq_rel. constructor; red; intros.
  + unfold obs_val_equiv. destruct x.  apply H.
  + unfold obs_val_equiv. unfold obs_val_equiv in H0. destruct x; destruct y. revert H0. apply H.
  + unfold obs_val_equiv. unfold obs_val_equiv in H0. unfold obs_val_equiv in H1. destruct x; destruct y; destruct z. revert H1; revert H0. apply H.
Qed.


Definition type_obs_val : T.type (obs_val) :=
  {| T.equal := obs_val_equiv ;
     T.proper := obs_val_proper |}.

Instance typeOk_obs_val: T.typeOk (type_obs_val).
Proof.
  constructor.
  + intros. split; do 3 red; constructor.
  + do 3 red. intros. red.  destruct x. apply forall2_eq_rel. apply val_equiv_eq_rel.
  + do 3 red. intros. red in H. red in H. revert H. apply obs_val_equiv_eq_rel.
  + do 3 red. intros. do 2 (red in H). do 2 (red in H0). revert H0; revert H; apply obs_val_equiv_eq_rel.
Qed.
    (** 
(* syntactic equivalence up to alpha-renaming*)
Actually: only define val_equiv over observable_val, make functions non observable.

Function renamed (R:list (var * var)) (v v':var) : Prop :=
  match R with
    | (x, x')::R' =>
      (@eq var x v <-> @eq var x' v') /\ ((@eq var x v = False /\ @eq var x' v' = False) -> renamed R' v v') 
    | nil => False
  end.

Function renamed_list (R:list (var * var)) (vs vs': list var): Prop :=
  match (vs, vs') with
    | (v:: vss, v'::vss') => renamed R v v' /\ renamed_list R vss vss'
    | (nil, nil) => True
    | _ => False
  end.

  
Function exp_alphasyneq (R:list (var * var)) (e1 e2:exp) : Prop :=
  match (e1, e2) with
    | (Econstr v t tg vs e, Econstr v' t' tg' vs' e') =>
      renamed_list R vs vs' /\
      exp_alphasyneq ((v, v')::R) e e' 
    | (Eproj x t n y e, Eproj x' t' n' y' e') =>
      renamed R y y' /\ exp_alphasyneq ((x,x')::R) e e'
    | (Ecase y cl, Ecase y' cl') =>
      renamed R y y' /\ Forall2 (fun tl tl':(tag * var)=> match (tl, tl') with
                                                            | ((_, y), (_, y')) => renamed R y y' end ) cl cl'
    | (Efun fl e, Efun fl' e') =>
            exp_alphasyneq R e e'
    | (Eapp f ys, Eapp f' ys') =>
       renamed R f f' /\ renamed_list R ys ys'
    | (Eprim x t (f::ys) e, Eprim x' t' (f'::ys') e') =>
      exp_alphasyneq R e e'
    | _ => False
  end.

Function fundefs_alphasyneq (R:list (var * var)) (f1 f2:fundefs) : Prop :=
  match (f1, f2) with
    | (Fcons f t xs e f1', Fcons f' t' xs' e' f2' ) =>
      if beq_nat (length xs) (length xs') then
        False
      else
      (exp_alphasyneq ((combine xs xs')++R) e e') /\ (fundefs_alphasyneq R f1' f2')
    | (Fnil, Fnil) => True
    | _ => False
  end.

Function add_fundefseq (R:list (var * var))  (defs defs':fundefs) : option (list (var * var)) :=
  match (defs, defs') with
    | (Fcons f t ys e fdefs, Fcons f' t' ys' e' fdefs') =>
      add_fundefseq ((f,f')::R) fdefs fdefs'
    | (Fnil , Fnil) => Some R
    | _ => None
  end.

Function val_equiv' (v1 v2:val) {struct v1}: Prop :=
    match (v1, v2) with
      | (Vfun valsubst defs f, Vfun valsubst' defs' f') =>
        match (add_fundefseq nil defs defs') with
          | Some R' =>  fundefs_alphasyneq  R' defs defs' (* may instead start by checking f f' and recursively check for equality on function calls within f and f' *)
          | None => False (* lists are of different size, could instead explore from f and f', o.w. can't reorder/delete functions *)
        end

      |  _  => @eq val v1 v2
    end.

Instance eq_val: Equivalence val_equiv.

val_equiv is wrong, only superficial function, not rec.


*)
   
  
  
Definition var_equiv: env -> env -> relation var :=
fun rho1 rho2 => fun var1 var2 =>
                   match (M.get var1 rho1, M.get var2 rho2) with
                        |(Some v1, Some v2) => val_equiv v1 v2
                        | _ => False
                   end
    .




(* small-step based equality on state *)    
Definition valid_term_state (s:state) :=
  match s with
    | (rho, Eapp g varl) => match M.get g rho with
                              | Some (Vobvs t) => Forall (fun var => match M.get var rho with
                                                                       | Some val => observable_val val
                                                                       | _ => False
                                                                        end) varl
                              | _ => False
                            end
    | _ => False
  end
.



Definition state_equiv: relation state :=
  fun s1 s2 =>
    exists sv1 sv2,
    mstep s1 sv1 /\ mstep s2 sv2 /\
    valid_term_state sv2 /\ valid_term_state sv1 /\
    match (sv1, sv2) with
      |((rho1, Eapp g1 varl1) , (rho2, Eapp g2 varl2)) => (match (M.get g1 rho1, M.get g2 rho2) with 
                                                             | (Some v1, Some v2) => val_equiv v1 v2
                                                             | _ => False
                                                           end)
                                                          /\ Forall2 (var_equiv rho1 rho2) varl1 varl2
      | _ => False
    end.
    


(* Theorems about  (small-)step relation *)



(*
Definition env_of_tenv := fun rho:env => fun Gamma:tenv => forall var, (exists ty, M.get var Gamma = Some ty <-> exists val, M.get var rho = Some val /\ type_of_val val ty) . *)

Theorem step_deterministic: forall s s' s'',
                         step s s' -> step s s'' -> s' = s''.     
  intros.  inversion H; inversion H0; subst;
           repeat match goal with
                    | [ |- ?P = ?P] => reflexivity
                    | [H: ( Some _ = Some _ ) |- _ ] => inversion H; subst      
                    | [H1: (?P = Some _), H2:(?P = Some _) |- _ ] => rewrite H1 in H2; inversion H2; subst
                    | [H: ((?rho0, _) = (?rho, _)) |- _ ] => inversion H; subst
                  end.


         +  rewrite H6 in H2.  inversion H2; subst. reflexivity.
         + rewrite H6 in H2; inversion H2; subst. reflexivity.
         + rewrite H9 in H3; inversion H3; subst. rewrite H2 in H8; inversion H8; subst. rewrite H10 in H4; inversion H4. reflexivity.
         +  rewrite H2 in H8; inversion H8; subst. rewrite H9 in H3; inversion H3; subst; reflexivity.
Qed.  

Theorem cant_step_terminal: forall s s',
                          valid_term_state s -> 
                          step s s' ->
                          False.
 intros. unfold valid_term_state in H. 
 destruct s. destruct e0; try inversion H. inversion H0; subst. destruct (M.get v e); try inversion H. destruct v0; try inversion H. inversion H4. inversion H4. 
  Qed.

Theorem state_equiv_step_l: forall s1 s2 s1', step s1 s1' -> (state_equiv s1 s2 <-> state_equiv s1' s2).
  intros s1 s2 s1' H0. split; intro.
 + unfold state_equiv in H. destruct H as [sv1 ?]. destruct H as [sv2 ?]. do 4 ( destruct H as [?V H]). inversion V; subst.  assert (s3 = s1'). eapply step_deterministic. apply H1. apply H0. subst. unfold state_equiv. exists sv1. exists sv2. split. assumption. split. assumption. split. assumption. split. assumption. assumption. apply (cant_step_terminal _ _ V2) in H0. inversion H0.
+  unfold state_equiv in H. destruct H as [sv1 ?]. destruct H as [sv2 ?]. do 4 (destruct H as [?V H]). assert (mstep s1 sv1). eapply s_step. apply H0. apply V. unfold state_equiv. exists sv1. exists sv2. split. assumption. split. assumption. split. assumption. split. assumption. assumption.
Qed.

Theorem state_equiv_step_r: forall s1 s2 s2', step s2 s2' -> (state_equiv s1 s2  <-> state_equiv s1 s2').
intros s1 s2 s2' H0. split; intro.
+   unfold state_equiv in H. destruct H as [sv1 ?]. destruct H as [sv2 ?]. do 4 (destruct H as [?V H]). inversion V0; subst. assert (s3 = s2'). eapply step_deterministic. apply H1. assumption. subst. unfold state_equiv. exists sv1. exists sv2. split. assumption. split. assumption. split. assumption. split. assumption. assumption.
apply (cant_step_terminal _ _ V1) in H0. inversion H0.
+ unfold state_equiv in H. destruct H as [sv1 ?]. destruct H as [sv2 ?]. do 4 (destruct H as [?V H]). assert (mstep  s2 sv2). eapply s_step; eauto. unfold state_equiv. exists sv1. exists sv2. split. assumption. split. assumption. split. assumption. split. assumption. assumption.
Qed.
 

(* 
Theorem progress: forall TD Gamma e rho,
                    welltyped TD Gamma e -> env_of_tenv rho Gamma -> valid_term_state (rho, e) \/  (exists rho' e', step (rho, e) (rho', e')).
admit.
Qed.
 
Theorem preservation: forall TD Gamma Gamma' rho rho' e e',
   welltyped TD Gamma e -> env_of_tenv rho Gamma -> step (rho, e) (rho', e') -> env_of_tenv rho' Gamma' -> welltyped TD Gamma' e'.
admit.
Qed.
*)



(* theorems about mstep *)

(* can't prove this, can assume it for terms I receive *)
(* Theorem termination: forall TD Gamma e rho,
     welltyped TD Gamma e -> env_of_tenv rho Gamma -> (exists rho' ev, mstep (rho,e) (rho', ev) /\ valid_term_state (rho', ev)).
admit.
Qed. *)

Theorem church_rosser: forall s sv1 sv2,
                         mstep s sv1 ->
                         mstep s sv2 ->
                         (exists s',
                            mstep sv1 s' /\ mstep sv2 s').
  intro s. intros. generalize dependent sv2. induction H.
  + intros.  destruct H1.
     -  assert (s2 = s0). eapply step_deterministic. apply H. apply H1. subst. apply IHmstep in H2.  destruct H2. exists x. assumption.
     -  assert ( exists s' : state, mstep s3 s' /\ mstep s3 s'). apply (IHmstep _ H0). destruct H1. destruct H1. exists s3. split. constructor. eapply s_step. apply H. apply H0.
   + intros. exists sv2. split. assumption. constructor.
Qed.


Theorem mstep_terminal_to_itself: forall s s',
                          valid_term_state s -> 
                          mstep s s' ->
                          s = s'.
  intros.  inversion H0; subst.
 assert False. eapply cant_step_terminal. apply H. apply H1. inversion H3.
reflexivity.
Qed.


     
Theorem forall2_varequiv_transitive:
  forall e1 e2 e3 l1 l2 l3,
  Forall2 (var_equiv e1 e2) l1 l2
       ->   Forall2 (var_equiv e2 e3) l2 l3
       ->   Forall2 (var_equiv e1 e3) l1 l3.
intros. generalize dependent l2. generalize dependent l3. induction l1; intros.
inversion H; subst. inversion H0; subst. constructor.
inversion H; subst. inversion H0; subst. constructor.
   red. red in H3. red in H4. clear H0. clear H7. clear H. clear IHl1. destruct (M.get a e1); try inversion H3. destruct (M.get y e2); try inversion H3. destruct (M.get y0 e3); try inversion H4. reflexivity.
   eapply IHl1. apply H5. apply H7.
Qed.


Definition state_proper :=
fun st => exists sv, mstep st sv /\ valid_term_state sv.

(* small step state equivalence *)
Definition type_state : T.type (state) :=
  {| T.equal := state_equiv
     ; T.proper := state_proper
  |}.

Instance typeOk_state : T.typeOk (type_state). 
constructor.  
intros.

(* only proper *)
inversion H. destruct H0. destruct H0. destruct H1. destruct H2. destruct H3. split; do 2 red. exists x0; split; assumption.
         exists x1; split; assumption.

(* Reflective for proper state *)         
red. intros. inversion H. destruct H0. red. red. red. exists x0. exists x0. split. assumption. split. assumption. split. assumption. split. assumption. unfold valid_term_state in H1. destruct x0. destruct e0; try inversion H1. destruct (M.get v e); try inversion H1. split. red. reflexivity. clear H0. induction l. constructor. constructor. red.    destruct v0; try inversion H1; subst.  destruct (M.get a e). reflexivity. inversion H3. apply (IHl). destruct v0; try inversion H1. inversion H1; subst. assumption.

(* symmetric *)
red. intros. red. red. red. destruct H. destruct H. destruct H. destruct H0. destruct H1. destruct H2. exists x1. exists x0. split. assumption. split. assumption. split. assumption. split. assumption. destruct x0. destruct x1. destruct e0; try inversion H3. destruct e2; try inversion H3. split. clear H. clear H0. destruct (M.get v e); try inversion H3. destruct (M.get v0 e1); try inversion H4. reflexivity. inversion H. clear H. clear H0. clear H1. clear H2. clear H3. generalize dependent l0. induction l.  intros. inversion H5. subst. constructor. intros. inversion H5. constructor.
              (* var_equiv is quasi-symmetric*) unfold var_equiv. unfold var_equiv in H1. destruct (M.get a e); try inversion H1. destruct (M.get y0 e1); try inversion H1. reflexivity.  apply IHl. assumption.

(* Transitive *)
red. intros. do 3 red. do 3 red in H.  do 3 red in H0. destruct H. destruct H. destruct H0. destruct H0. destruct H. destruct H1. destruct H2. destruct H3. destruct H0. destruct H5. destruct H6. destruct H7. assert (exists s', mstep x1 s' /\ mstep x2 s').  apply (church_rosser y x1 x2 H1 H0). destruct H9. destruct H9. apply (mstep_terminal_to_itself _ _ H7) in H10; subst. apply (mstep_terminal_to_itself _ _ H2) in H9; subst. exists x0. exists x3. split.
assumption. split. assumption. split. assumption. split. assumption. destruct x0. destruct e0; try inversion H4. destruct x3. destruct x4. destruct e3; try inversion H4. destruct e1; try inversion H8. destruct (M.get v e); try inversion H9. split. destruct (M.get v0 e2); try inversion H8. destruct (M.get v1 e0); try inversion H11. eapply transitivity. apply H9. apply H11. inversion H11.
eapply forall2_varequiv_transitive. destruct H4. apply f. apply H12. 
Qed.
(* proofs of semantics preservation for P will look like 
   forall rho, proper (rho, e) -> equal (rho, e) (rho, P e). *)



(* small step exp equivalence *)
Definition exp_equiv: relation exp :=
  fun e1 e2 =>     (forall rho1, state_proper(rho1, e1) ->  state_equiv (rho1, e1) (rho1, e2)) /\
                   (forall rho2, state_proper (rho2, e2) -> state_equiv (rho2, e1) (rho2, e2)). 



Definition exp_proper := fun e:exp => True.

Definition type_exp : T.type (exp) :=
  {| T.equal := exp_equiv 
     ; T.proper := exp_proper
  |}.

Ltac tci := eauto with typeclass_instances.

Instance typeOk_exp : T.typeOk (type_exp).
  Proof.
constructor.
intros. split; do 3 red; constructor.
(* PRefl *)
+ red. intros. do 3 red. split; intros; apply typeOk_state; tci.

(* Symmetric *)    
+ red. intros. do 3 red in H. destruct H. do 3 red. split; intros.
  - apply H0 in H1. generalize H1. apply typeOk_state; tci.
  - apply H in H1. generalize H1. apply typeOk_state; tci.
 (* Transitive *)
    + do 3 red. intros. do 3 red in H. destruct H. do 3 red in H0. destruct H0. red. split; intros.
      - apply H in H3. assert (H4 := H3). apply typeOk_state in H3. destruct H3. apply H0 in H5. generalize H5. generalize H4. apply typeOk_state; tci.
     - apply H2 in H3. assert (H4 := H3). apply typeOk_state in H3; destruct H3. apply H1 in H3. generalize H4. generalize H3. apply typeOk_state; tci.
  Qed.

(* fun equivalence *)
Definition fun_equiv: forall e1 e2, exp_equiv e1 e2 -> relation fundefs :=
  fun e1 e2 => fun equiv_e1e2 =>  fun fds1 fds2 =>
        (forall rho1, state_proper (def_funs fds1 fds1 rho1 rho1, e1) -> state_equiv (def_funs fds1 fds1 rho1 rho1, e1) (def_funs fds2 fds2 rho1 rho1, e2)) /\
                    (forall rho2, state_proper (def_funs fds2 fds2 rho2 rho2, e2) ->  state_equiv (def_funs fds1 fds1 rho2 rho2, e1) (def_funs fds2 fds2 rho2 rho2, e2)).

                             

Definition fun_proper := fun f:fundefs => True.

Definition etype_fun :  forall e1 e2, exp_equiv e1 e2 -> T.type fundefs  :=
  fun e1 e2 => fun equiv_e1e2 => 
  {| T.equal := fun_equiv e1 e2 equiv_e1e2
     ; T.proper := fun_proper
  |}.

Instance etypeOk_fun : forall e1 e2, forall equiv_e1e2: exp_equiv e1 e2, T.typeOk (etype_fun e1 e2 equiv_e1e2).
intros. constructor.
(* only *)
+ intros. split; do 3 red; constructor.
(* Prefl *)
+ red. intros. do 3 red. split; intros.
  - red in equiv_e1e2. destruct equiv_e1e2.
    apply s in H0. assumption.  
  - red in equiv_e1e2. destruct equiv_e1e2. apply s0 in H0. assumption. 
 (* symmetric *)
    + red. intros. do 3 red in H. do 3 red. destruct H. red in equiv_e1e2. destruct equiv_e1e2. split; intros.
  - assert (H4 := H3). apply H1 in H4.  assert (H5 := H4). apply typeOk_state in H4; destruct H4.  apply H0 in H6. assert (H7 := H6). apply typeOk_state in H6; destruct H6. apply H1 in H6. eapply (@T.equiv_trans _ type_state typeOk_state). eapply (@T.equiv_trans _ type_state typeOk_state). apply H5. apply (T.equiv_sym type_state _ _) in H7. apply H7. assumption.
  - apply H2 in H3. assert (H4 := H3). apply typeOk_state in H4; destruct H4. apply H in H4. assert (H6 := H4). apply typeOk_state in H4; destruct H4. apply H2 in H7. eapply (@T.equiv_trans _ type_state typeOk_state). eapply (@T.equiv_trans _ type_state typeOk_state). apply H7. apply (T.equiv_sym type_state _ _) in H6. apply H6. assumption.    
    (* transitive *)

+ red. intros. do 3 red in H. do 3 red in H0. do 3 red. destruct H. destruct H0. red in equiv_e1e2. destruct equiv_e1e2. split; intros.
   - apply H in H5. assert (Hfin1 := H5). apply typeOk_state in H5; destruct H5.  apply H4 in H6. assert (Hfin2 := H6). apply typeOk_state in H6; destruct H6. apply H0 in H6. Print T. About T.equiv_sym. eapply (T.equiv_sym type_state _ _) in Hfin2. About T.equiv_trans. eapply (@T.equiv_trans _ type_state typeOk_state).  eapply (@T.equiv_trans _ type_state typeOk_state). apply Hfin1. apply Hfin2. apply H6.
   - apply H2 in H5. assert (Hfin1 := H5). apply typeOk_state in H5; destruct H5. apply H3 in H5. assert (Hfin2 := H5). apply typeOk_state in H5; destruct H5. apply H1 in H7.  eapply (@T.equiv_trans _ type_state typeOk_state). eapply (@T.equiv_trans _ type_state typeOk_state). apply H7. apply (T.equiv_sym type_state _ _) in Hfin2. apply Hfin2. assumption.
Qed.




  
  (* big step exp equivalence *)
Definition  bs_exp_proper := fun _:exp => True (* fun e:exp => exists rho v, bstep_e rho e v. *).



Definition bs_exp_equiv : relation exp :=
  fun e1 e2 =>  (forall rho, forall v, bstep_e rho e1 v -> exists v', bstep_e rho e2 v' /\ obs_val_equiv v v') /\ (forall rho, forall v, bstep_e rho e2 v -> exists v', bstep_e rho e1 v' /\ obs_val_equiv v v').

Definition type_bs_exp : T.type (exp) :=
  {| T.equal := bs_exp_equiv
     ;T.proper := bs_exp_proper |}.

Instance typeOk_bs_exp : T.typeOk (type_bs_exp).
Proof.
  constructor.
 intros. split; do 3 red; constructor.
 + do 3 red.  intros. unfold bs_exp_equiv. split; intros. exists v. split. assumption. apply obs_val_equiv_eq_rel. exists v. split. assumption. apply typeOk_obs_val. auto.
+ red. intros. do 3 red in H.  destruct H. do 3 red. split; intros.  apply H0 in H1. destruct H1. destruct H1. exists x0. split. assumption. assumption.
   apply H in H1. destruct H1. destruct H1. exists x0. split; assumption.
 + do 3 red. intros. do 3 red in H. destruct H. do 3 red in H0. destruct H0. red. split. intros. apply H in H3. destruct H3. destruct H3. apply H0 in H3. destruct H3. exists x1. destruct H3. split. assumption. revert H5. revert H4. apply typeOk_obs_val.
     intros. apply H2 in H3. destruct H3. destruct H3. apply H1 in H3. destruct H3. exists x1. destruct H3. split. assumption. revert H5. revert H4. apply typeOk_obs_val.
Qed.


 
End PRIMS.

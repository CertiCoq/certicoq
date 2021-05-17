(** Implements an uncurrying pass for the L6 CPS language, based on the same
    approach used in SML/NJ.  The following issues need to be addressed:
    * This doesn't do all of the uncurrying at once -- you have to iterate until
      there's no change.  But...
    * DONE - We need to tag the eta-expansions so that they don't get uncurried again, and
    * We need to tag the uncurried function so that it doesn't get inlined into
      the eta expansion (thereby undoing the uncurrying.)
 *)
Require Import Coq.Strings.String.
Require Import Libraries.CpdtTactics Common.compM.
Require Import L6.cps.
Require Import ExtLib.Structures.Monad.
Require Import ExtLib.Structures.MonadState.
Require Import ExtLib.Data.Monads.StateMonad.
Require Import ExtLib.Data.List.
Require Import ExtLib.Structures.Traversable.
Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Data.Positive.
Require Import Coq.Bool.Bool.
Require Import identifiers.  (* for max_var *)
Require Import AltBinNotations.
Require Import L6.List_util L6.cps_util L6.state.
Require Import Lia.
Require Equations.Equations.

Open Scope monad_scope.

Section UNCURRY.
  Import MonadNotation.


  Definition eq_var := Pos.eqb.
  
  (** We need to determine whether variables occur free in some terms.  We
      over-approximate by determining whether the variable occurs at all. *)
  
  (* Returns true iff [k] is in [xs]. *)
  Fixpoint occurs_in_vars (k:var) (xs:list var) : bool :=
    match xs with
    | nil => false
    | x::xs1 => eq_var k x || occurs_in_vars k xs1
    end.

  (* Returns true iff [k] occurs (at all) within the expression [e] *)
  (* TODO: move to identifier utils *)
  Definition occurs_in_arms' (occurs_in_exp : var -> exp -> bool) k : list (ctor_tag * exp) -> bool :=
    fix go arms :=
      match arms with
      | nil => false
      | (_, e) :: arms1 => occurs_in_exp k e || go arms1
      end.
  Fixpoint occurs_in_exp (k:var) (e:exp) : bool :=
    match e with
    | Econstr z _ xs e1 =>
      eq_var z k || occurs_in_vars k xs || occurs_in_exp k e1
    | Ecase x arms =>
      eq_var k x || occurs_in_arms' occurs_in_exp k arms
    | Eproj z _ _ x e1 =>
      eq_var z k || eq_var k x || occurs_in_exp k e1
    | Eletapp z f _ xs e1 =>
      eq_var z k || eq_var f k || occurs_in_vars k xs || occurs_in_exp k e1
    | Efun fds e =>
      occurs_in_fundefs k fds || occurs_in_exp k e
    | Eapp x _ xs => eq_var k x || occurs_in_vars k xs
    | Eprim z _ xs e1 =>
      eq_var z k || occurs_in_vars k xs || occurs_in_exp k e1
    | Ehalt x => eq_var x k
    end
  (* Returns true iff [k] occurs within the function definitions [fds] *)
  with occurs_in_fundefs (k:var) (fds:fundefs) : bool :=
         match fds with
         | Fnil => false
         | Fcons z _ zs e fds1 =>
           eq_var z k || occurs_in_vars k zs || occurs_in_exp k e ||
                   occurs_in_fundefs k fds1
         end.
  Definition occurs_in_arms := occurs_in_arms' occurs_in_exp.


  (* pair of 
     1- max number of arguments 
     2- encoding of inlining decision for beta-contraction phase *)
  Definition St := (nat * (M.t nat))%type. (* 0 -> Do not inline, 1 -> outermost function, 2 -> inner function *)

  (* Maps (arity+1) to the right fun_tag *)
  Definition arityMap:Type := M.t fun_tag.
  Definition localMap:Type := M.t bool.
   
  (* The state for this includes 
     1 - a boolean for tracking whether or not a reduction happens
     2 - Map recording the (new) fun_tag associated to each arity
     3 - local map from var to if function has already been uncurried
     4 - Map for uncurried functions for a 2version of inlining *)
  Definition stateType:Type := (bool * arityMap * localMap * St). 
  Definition uncurryM := @compM' stateType.


  (* f is a function to inline [i.e. uncurry shell], k is its local continuation *)
  Definition markToInline (n:nat) (f:var) (k:var) : uncurryM unit :=
    st <- get_state tt ;;  
    let '(b, aenv, lm, s) := st in
    @put_state stateType (b, aenv, lm, (max (fst s) n, (M.set f 1 (M.set k 2 (snd s))))).
        
  
  (* Mark variable as uncurried *)
  Definition mark_as_uncurried (x:var): uncurryM unit :=
    st <- get_state tt ;;
    let '(b, aenv, lm, s) := st in
    put_state (b, aenv, (M.set x true lm), s).
      

  Definition click : uncurryM unit :=
    st <- get_state tt ;;
    let '(b, aenv, lm, s) := st in
    put_state (true, aenv, lm, s).

  Definition unclick : uncurryM unit :=
    st <- get_state tt ;;
    let '(b, aenv, lm, s) := st in
    put_state (false, aenv, lm, s).
  
  Definition has_clicked : uncurryM bool :=
    st <- get_state tt ;;
    let '(b, aenv, lm, s) := st in ret b.


  Definition already_uncurried (f:var) : uncurryM bool :=
    st <- get_state tt ;;
    let '(b, aenv, lm, s) := st in
    match M.get f lm with
    | Some true => ret true
    | _ => ret false
    end.

  (* get the fun_tag at arity N. If there isn't one already, create it *)
  Definition get_fun_tag (n:N): uncurryM fun_tag :=
    st <- get_state tt ;;
    let '(b, aenv, lm, s) := st in
    let p3 := (BinNat.N.succ_pos n) in
    match M.get p3  aenv with
    | Some t3 => ret t3
    | None =>
      ft <- get_ftag n ;;
      put_state (b, (M.set p3 ft aenv), lm, s);;
      ret ft
    end.                       
  
  (* I'm following the same algorithm as in Andrew's book, or more 
     appropriately, in the SML/NJ code base.  In essence, we look for
     code that looks like this:
     let rec f (k,v1,...,vn) = 
           let rec g (u1,...,um) = e in k(g)
      in ...
     and replace it with:
     let rec f (k',v1',...,vn') = 
           let rec g' (u1',...,um') = f'(u1',...,um',v1',...,vn') in k'(g')
         and f' (k,u1,...,um,v1,...,vn) = e
     in ...
     where all of the primed variables are fresh. 
     One difference with SML/NJ is that this won't get all of the uncurrying
     done in a single pass.  In particular, if f gets uncurried, but the 
     resulting function can be further uncurried, we won't pick this up.  So
     really, we should iterate this until there's no change.  But, doing so
     will try to uncurry f yet again.  So we need to either fix this so that
     we tag f as something that should no longer be uncurried, or else 
     do all of the uncurrying in one pass.  The latter would be preferable
     but makes a structural termination argument harder.  
   *)

  Section Uncurry_prog.

    Import Equations.

    Fixpoint sizeof_exp e : nat :=
      match e with
        (Econstr x _ ys e) => 1 + length ys + sizeof_exp e
      | (Ecase x l) =>
        1 + (fix sizeof_l l :=
                match l with
                  nil => 0
                | (t, e) :: l => 1 + sizeof_exp e + sizeof_l l
                end) l
      | (Eproj x _ _ y e) => 1 + sizeof_exp e
      | (Eletapp _ _ _ xs e) => 1 + length xs + sizeof_exp e
      | (Efun fds e) => 1 + sizeof_fundefs fds + sizeof_exp e
      | (Eapp x _ ys) => 1 + length ys
      | (Eprim x _ ys e) => 1 + length ys + sizeof_exp e
      | (Ehalt x) => 1
      end
    with sizeof_fundefs f : nat := 
      match f with
      | Fcons f t v e fds => 1 + sizeof_exp e + sizeof_fundefs fds
      | Fnil => 0
      end.
    Fixpoint sizeof_cases (ces : list (ctor_tag * exp)) : nat :=
      match ces with
      | nil => 0
      | (c, e) :: ces => 1 + sizeof_exp e + sizeof_cases ces
      end.

    Inductive rec_item :=
    | Exp (e : exp)
    | Cases (ces : list (ctor_tag * exp))
    | Fundefs (fds : fundefs).
    
    Definition sizeof (a : rec_item) : nat :=
      match a with
      | Exp e => sizeof_exp e
      | Cases ces => sizeof_cases ces
      | Fundefs fds => sizeof_fundefs fds
      end.

    Obligation Tactic :=
      try abstract (
        Tactics.program_simplify;
        CoreTactics.equations_simpl;
        try Tactics.program_solve_wf;
        lia).
    Equations uncurry_rec_item (cps : bool) (item : rec_item)
      : uncurryM (match item with
                  | Exp _ => exp
                  | Fundefs _ => fundefs
                  | Cases _ => list (ctor_tag * exp)
                  end)
        by wf (sizeof item) lt :=
    { uncurry_rec_item cps (Exp (Econstr x ct vs e1)) :=
        e1' <- uncurry_rec_item cps (Exp e1) ;; 
        ret (Econstr x ct vs e1') ;
      uncurry_rec_item cps (Exp (Ecase x arms)) :=
        arms' <- uncurry_rec_item cps (Cases arms) ;;
        ret (Ecase x arms') ;
      uncurry_rec_item cps (Exp (Eproj x ct n y e1)) :=
        e1' <- uncurry_rec_item cps (Exp e1) ;;
        ret (Eproj x ct n y e1') ;
      uncurry_rec_item cps (Exp (Eletapp x f ft ys e1)) :=
        e1' <- uncurry_rec_item cps (Exp e1) ;;
        ret (Eletapp x f ft ys e1') ;
      uncurry_rec_item cps (Exp (Eapp x ft xs)) := ret (Eapp x ft xs) ;
      uncurry_rec_item cps (Exp (Eprim x p xs e1)) :=
        e1' <- uncurry_rec_item cps (Exp e1) ;;
        ret (Eprim x p xs e1') ;
      uncurry_rec_item cps (Exp (Efun fds e1)) :=
        fds' <- uncurry_rec_item cps (Fundefs fds) ;;
        e1' <- uncurry_rec_item cps (Exp e1) ;;
        ret (Efun fds' e1') ;
      uncurry_rec_item cps (Exp (Ehalt x)) := ret (Ehalt x) ;
      uncurry_rec_item cps (Cases nil) := ret nil ;
      uncurry_rec_item cps (Cases ((c, e) :: ces)) :=
        e <- uncurry_rec_item cps (Exp e) ;;
        ces <- uncurry_rec_item cps (Cases ces) ;;
        ret ((c, e) :: ces) ;
      uncurry_rec_item cps (Fundefs Fnil) := ret Fnil ;
      uncurry_rec_item cps (Fundefs (Fcons f f_ft fvs fe fds1)) with cps :=
      { uncurry_rec_item cps (Fundefs (Fcons f f_ft fvs fe fds1)) true with fe, fvs :=
        { uncurry_rec_item cps (Fundefs (Fcons f f_ft fvs fe fds1)) true
            (Efun (Fcons g gt gvs ge Fnil) (Eapp fk' fk_ft (g'::nil))) (fk :: fvs) :=
            (* XXX CHANGED *) (* ge' <- uncurry_rec_item cps ge ;; *)
            (* Zoe : Nested carried arguments should be handled one-at-a-time,
                   so that functions with > 2 arguments get uncurried properly.
                   Therefore the body of g will be uncurried at the next iteration
                   of the transformat ion.
             *)
            g_unc <- already_uncurried g ;;
            if eq_var fk fk' && eq_var g g' &&
               negb (occurs_in_exp g ge) &&
               negb (occurs_in_exp fk ge) &&
               negb g_unc
            then
              (* log_msg (f_str ++ " is uncurried" ) ;; *)
              gvs' <- get_names_lst gvs "" ;;
              fvs' <- get_names_lst fvs "" ;;
              f' <- get_name f "_uncurried" ;;
              _ <- mark_as_uncurried g ;;
              let fp_numargs := length (gvs' ++ fvs')  in
              _ <- markToInline fp_numargs f g;;
              fp_ft <- get_fun_tag (BinNat.N.of_nat fp_numargs);;
              fds1' <- uncurry_rec_item cps (Fundefs (Fcons f' fp_ft (gvs ++ fvs) ge fds1)) ;;
              ret (Fcons f f_ft (fk::fvs')
                         (* Note: tag given for arity |fvs| + |gvs|  *)
                         (Efun (Fcons g gt gvs' (Eapp f' fp_ft (gvs' ++ fvs')) Fnil)
                               (Eapp fk fk_ft (g::nil)))
                         fds1')
            else
              (* log_msg (f_str ++ " is not uncurried (candidate)" ) ;; *)
              fds1' <- uncurry_rec_item cps (Fundefs fds1) ;;
              fe' <- uncurry_rec_item cps (Exp (Efun (Fcons g gt gvs ge Fnil) (Eapp fk' fk_ft (g'::nil)))) ;;
              ret (Fcons f f_ft (fk::fvs) fe' fds1') ;
          uncurry_rec_item cps (Fundefs (Fcons f f_ft fvs fe fds1)) true fe fvs :=
            (* log_msg (f_str ++ " is not uncurried" ) ;; *)
            fds1' <- uncurry_rec_item cps (Fundefs fds1) ;;
            fe' <- uncurry_rec_item cps (Exp fe) ;;
            ret (Fcons f f_ft fvs fe' fds1') } ;
        uncurry_rec_item cps (Fundefs (Fcons f f_ft fvs fe fds1)) false with fe :=
        { uncurry_rec_item cps (Fundefs (Fcons f f_ft fvs fe fds1)) false
                           (Efun (Fcons g gt gvs ge Fnil) (Ehalt g')) :=
            g_unc <- already_uncurried g ;;
            if eq_var g g' && negb g_unc && negb (occurs_in_exp g ge)
            then               
              gvs' <- get_names_lst gvs "" ;;
              fvs' <- get_names_lst fvs "" ;;
              f' <- get_name f "_uncurried" ;;
              let fp_numargs := length (gvs' ++ fvs') in
              _ <- mark_as_uncurried g ;;
              _ <- markToInline fp_numargs f g;;
              fp_ft <- get_fun_tag (BinNat.N.of_nat fp_numargs);;
              fds1' <- uncurry_rec_item cps (Fundefs (Fcons f' fp_ft (gvs ++ fvs) ge fds1)) ;;
              ret (Fcons f f_ft fvs'
                         (Efun (Fcons g gt gvs' (Eapp f' fp_ft (gvs' ++ fvs')) Fnil)
                               (Ehalt g))
                         fds1')
            else
              fds1' <- uncurry_rec_item cps (Fundefs fds1) ;;
              fe' <- uncurry_rec_item cps (Exp (Efun (Fcons g gt gvs ge Fnil) (Ehalt g'))) ;;
              ret (Fcons f f_ft fvs fe' fds1') ;
          uncurry_rec_item cps (Fundefs (Fcons f f_ft fvs fe fds1)) false fe :=
            fds1' <- uncurry_rec_item cps (Fundefs fds1) ;;
            fe' <- uncurry_rec_item cps (Exp fe) ;;
            ret (Fcons f f_ft fvs fe' fds1') } } }.

    Definition uncurry_exp cps e := uncurry_rec_item cps (Exp e).
    Definition uncurry_fundefs cps fds := uncurry_rec_item cps (Fundefs fds).

    (* Zoe : The above for ANF  misses some opportunities for uncurrying when the recursion is
     * "nested" in some inner argument. Example from Coq:
       Definition filter (A : Type) (P : A -> bool) := fix aux (l : list A) := ...
     
       For this we need to lift the constraint that negb (occurs_in_exp g ge) by 
       redefining the g wrapper inside f'. This however messes up the uncurring
       pattern for the inner args, so we need to do this in two stages. *)

  End Uncurry_prog.

  Definition uncurry_top cps e c : error exp * comp_data :=
    let local_st := (false, M.empty _, M.empty _, (0%nat, (M.empty _))) in
    let '(e_err, (c', (_, _, _ , (_, inline_map)))) := run_compM (uncurry_exp cps e) c local_st in
    (e_err, put_inline_map inline_map c').

End UNCURRY.

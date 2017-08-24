(* Generic beta-contraction phase for (stateful) heuristics based on function definitions and call sites, with bounded inlining depth
   *)
Require Import L6.cps.
Require Import Coq.ZArith.ZArith Coq.Lists.List.
Import ListNotations.
Require Import identifiers.
Require Import L6.shrink_cps.
 Require Import L6.alpha_fresh. 
Require Import ExtLib.Structures.Monad.
Require Import ExtLib.Structures.MonadState.
Require Import ExtLib.Data.Monads.StateMonad.
Require Import L6.size_cps.
Require Coq.Program.Wf.
Require Import Program.
Require Import Coq.Structures.OrdersEx.

(* St is the type of the [scoped] state used by the  heuristic *)
Record InlineHeuristic (St:Type) := { 
                     update_funDef:(fundefs -> r_map -> St -> (St * St)); (* update inlining decision at functions declaraction. First state is used for the body of the program, second for the function definitions *)
                     update_inFun:(var -> tag -> list var -> exp -> r_map -> St -> St); (* update inlining decisions when converting a function within a bundle *)
                     update_App:(var -> tag -> list var -> St -> (St*bool)) (* update and return inlining decision for f on function application *) }.


  
Section Beta.
  Import MonadNotation.

  Definition freshM := state positive.

  Definition r_map := M.t var.
  
  Definition freshen_exp (e:exp) : freshM exp  :=
     curr <- get;; 
    let '(e', n, l) := freshen_term e (M.empty positive) curr nil in
    _ <- put n;; 
      ret e'.
  
 
  
  Variable St:Type.
  Variable IH : InlineHeuristic St.
  



  Fixpoint add_fundefs (fds:fundefs) (del:M.t (tag * list var * exp)):M.t (tag * list var * exp) :=
    match fds with
    | Fnil => del
    | Fcons f t xs e fds => M.set f (t, xs, e) (add_fundefs fds del)
    end.


  Definition term_size_le: exp -> exp -> Prop :=
    fun e1 e2 => (term_size e1 < term_size e2).


  Theorem term_size_wf: well_founded term_size_le.
  Proof.
    apply well_founded_lt_compat with (f:= term_size).
    intros. unfold term_size_le in *. auto.
  Defined.

Definition term_size_lex :  nat * exp -> nat * exp -> Prop :=
  fun p1 p2 =>
    or (lt (fst p1) (fst p2)) (and (eq (fst p1) (fst p2)) (term_size_le (snd p1) (snd p2))).


  
  Theorem term_size_Pair_wf: well_founded (Coqlib.lex_ord lt term_size_le).
  Proof.
    apply Coqlib.wf_lex_ord; [apply lt_wf |apply term_size_wf].
  Defined.


  Lemma beta_contract_fds_1:
    forall {f t xs e fdc' fds} , 
      cps_util.subfds_or_eq (Fcons f t xs e fdc') fds ->
  term_size e < funs_size fds.
  Proof.
    intros.
    apply subfds_or_eq_size in H.
    simpl in H; omega.
  Defined.

Lemma beta_contract_fds_2:
    forall {f t xs e fdc' fds}, 
  cps_util.subfds_or_eq (Fcons f t xs e fdc') fds ->
  cps_util.subfds_or_eq fdc' fds.
Proof.
  intros. inversion H.
  apply cps_util.subfds_rebase in H0. left. auto.
  subst. left. constructor 2.
Defined.




Function beta_contract_fds (fds:fundefs) (fcon: St -> forall e:exp, (term_size e < funs_size fds)%nat -> freshM exp)  (fdc:fundefs) (sig:r_map) (s:St) (p:  cps_util.subfds_or_eq fdc fds): freshM fundefs :=
    (match fdc as x return x = fdc -> _ with
    | Fcons f t xs e fdc' =>
      fun Heq_fdc =>
        let s' := update_inFun _ IH f t xs e sig s in
         e' <- fcon s' e (beta_contract_fds_1 (eq_ind_r (fun a => cps_util.subfds_or_eq a fds) p Heq_fdc));;
         fds' <- beta_contract_fds fds fcon fdc' sig s (beta_contract_fds_2 (eq_ind_r (fun a => cps_util.subfds_or_eq a fds) p Heq_fdc));;
         ret (Fcons f t xs e' fds')
    | Fnil => fun _ => ret Fnil
    end) (eq_refl fdc).






  
  (* Lexicographic on (d, e) *)
  (* del only hold well-scoped functions, and functions can only be inlined up to d depth *)
  Program Fixpoint beta_contract (de:nat * exp) (sig:M.t var) (del:M.t (tag * list var * exp)) (s:St) {wf (Coqlib.lex_ord lt term_size_le) de} : freshM exp :=
    match de with
    | (d, e) =>
      (match e with
       | Econstr x t ys e =>
         let ys' := apply_r_list sig ys in
          e' <- beta_contract (d, e) sig del s;;
         ret (Econstr x t ys' e')
       | Ecase v cl =>
         let v' := apply_r sig v in
         cl' <- (fix beta_list (br: list (cTag*exp)) (s:St) (p:incl br cl):
                       freshM (list (cTag*exp)) :=
                       (match br with
                        | nil => ret ( nil)
                        | h::br' =>
                          (match h with
                             (t, e) =>
                             e' <- beta_contract (d,e) sig del s;;
                             br'' <- beta_list br' s _ ;;
                             ret ((t, e')::br'')
                           end)
                        end)) cl s (incl_refl _);;
         ret (Ecase v' cl')
       | Eproj x t n y e =>
         let y' := apply_r sig y in
         e' <- beta_contract (d, e) sig del s;;
         ret (Eproj x t n y' e')
       | Efun fds e =>
         let del' := add_fundefs fds del in
         let (s1, s2) := update_funDef _ IH fds sig s in
         e' <- beta_contract (d, e) sig del' s1;;
         fds' <- beta_contract_fds fds (fun s e p => beta_contract (d,e) sig del' s) fds sig s2 _  ;;
         (* would want just this but fails at last QED (wrong number of arguments), even though it works for case... *)
         (*(fix beta_contract_fds (fdc:fundefs) (s:St) (p:  cps_util.subfds_or_eq fdc fds) :fundefs :=
                        match fdc with
                        | Fcons f t xs e fdc' =>
                          let s' := update_inFun f t xs e s in
                          e' <- beta_contract (d, e) sig del' s;;
                          let fds' := beta_contract_fds fdc' s _ in
                          ret (Fcons f t xs e' fds')
                        | Fnil => ret Fnil
                        end)*)

         ret (Efun fds' e')
       | Eapp f t ys =>
         let f' := apply_r sig f in
         let ys' := apply_r_list sig ys in
         let (s, inl) := update_App _ IH f' t ys' s in
         (match (inl, M.get f' del, d) with
          | (true, Some (t, xs, e), S d') =>
            let sig' := set_list (combine xs ys') sig  in
            e' <- freshen_exp e;;
            beta_contract (d',e') sig' del  s 
          | _ => ret (Eapp f' t ys')
          end)
       | Eprim x t ys e =>
         e' <- beta_contract (d, e) sig del s;;
         let ys' := (apply_r_list sig ys) in
         ret (Eprim x t ys' e')
       | Ehalt x =>
         let x' := apply_r sig x in
         ret (Ehalt x')
       end)
    end.

      Solve Obligations with (program_simpl ; right; unfold term_size_le; simpl; omega).
      Next Obligation.
        right.
        unfold term_size_le.
        eapply case_size.
        apply p. constructor. reflexivity.
      Defined.
      Next Obligation.
        eapply Coqlib.incl_cons_inv. eauto.
      Defined.
      Next Obligation.
        right. auto.
      Defined.
      Next Obligation.
        left; omega.
      Defined.
      Next Obligation.
        apply Wf.measure_wf.
        apply term_size_Pair_wf.
      Defined.

      Definition beta_contract_top (e:exp) (d:nat) (s:St): exp :=
        let n :=((max_var e 1) + 1)%positive in
        match (runState (beta_contract (d, e) (M.empty var) (M.empty _) s) n) with
        | (e', n') => e'
        end.
        

      
End Beta.


Definition CombineInlineHeuristic {St1 St2:Type} (deci:bool -> bool -> bool) (IH1:InlineHeuristic St1) (IH2:InlineHeuristic St2):InlineHeuristic (prod St1 St2) :=
  {|
    update_funDef :=
      fun fds sigma (s:(prod St1 St2)) => 
        let (s1, s2) := s in
        let (s11, s12) := update_funDef _ IH1 fds sigma s1 in
        let (s21, s22) := update_funDef _ IH2 fds sigma s2 in
        ((s11, s21) , (s12, s22));
    update_inFun  :=
      fun (f:var) (t:tag) (xs:list var) (e:exp) (sigma:r_map) (s:_) =>
        let (s1, s2) := s in
        let s1' := update_inFun _ IH1 f t xs e sigma s1 in
        let s2' := update_inFun _ IH2 f t xs e sigma s2 in    
        (s1', s2');
    update_App  :=
      fun (f:var) (t:tag) (ys:list var) (s:_) =>
       let (s1, s2) := s in
       let (s1', b1) := update_App _ IH1 f t ys s1 in
       let (s2', b2) := update_App _ IH2 f t ys s2 in
       ((s1', s2'), deci b1 b2 )|}.



Definition PostUncurryIH : InlineHeuristic (M.t nat) :=
  (* at the start, uncurry shell (i.e. not the outermost) all maps to 1 *)
(* 0 -> Do not inline, 1 -> uncurried function, 2 -> continuation of uncurried function *)
  {|  
    update_funDef  := fun (fds:fundefs) (sigma:r_map) (s:_) => (s, s);
    update_inFun := fun (f:var) (t:tag) (xs:list var) (e:exp) (sigma:r_map) (s:_) => s;
    update_App := fun (f:var) (t:tag) (ys:list var) (s:_) =>
    match (M.get f s, ys) with
    | (Some 1, k::ys') =>
      (M.set f 0 (M.set k 2 s), true)
    | (Some 2, _ ) =>
      (s, true)
    | _ => (s, false)
    end |}.

  

  (* d should be max argument size, perhaps passed through by uncurry *)
Definition postuncurry_contract (e:exp) (s:M.t nat) (d:nat) :=
    beta_contract_top _ PostUncurryIH e d s.

  
  
Definition InlineSmallIH (bound:nat): InlineHeuristic (M.t bool) :=
  {|
    (* Add small, [todo: non-recursive] functions to s *)
    update_funDef  := (fun (fds:fundefs) (sigma:r_map) (s:_) => let s' := 
                                   (fix upd (fds:fundefs) (sigma:r_map) (s:_) :=
                                      match fds with
                                      | Fcons f t xs e fdc' => if (Init.Nat.ltb (term_size e) bound) then
                                                                 upd fdc' sigma (M.set f true s)
                                                               else  upd fdc' sigma s
                                      | Fnil => s
                                      end) fds sigma s in (s', s'));
    update_inFun := fun (f:var) (t:tag) (xs:list var) (e:exp) (sigma:r_map) (s:_) => (M.remove f s);
    update_App := fun (f:var) (t:tag) (ys:list var) (s:_) =>
                    match M.get f s with
                    | Some true => (M.remove f s, true)
                    | _ => (s, false)
                    end
  |}.


  Definition inlinesmall_contract (e:exp) (bound:nat)  (d:nat) :=
    beta_contract_top _ (InlineSmallIH bound) e d (M.empty _).


  Definition InlineSmallOrUncurried (bound:nat): InlineHeuristic (prod (M.t bool) (M.t nat)) :=
    CombineInlineHeuristic orb (InlineSmallIH bound) (PostUncurryIH).


  
    Definition inline_uncurry_contract (e:exp) (s:M.t nat) (bound:nat)  (d:nat) :=
    beta_contract_top _ (InlineSmallOrUncurried bound) e d (M.empty bool, s).

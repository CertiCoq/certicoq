(* Generic beta-contraction phase for (stateful) heuristics based on function definitions and call sites, with bounded inlining depth
   *)
Require Import L6.cps.
Require Import Coq.ZArith.ZArith Coq.Lists.List.
Import ListNotations.
Require Import identifiers.
Require Import L6.shrink_cps L6.alpha_fresh
        L6.size_cps L6.cps_util.
Require Import ExtLib.Structures.Monad.
Require Import ExtLib.Structures.MonadState.
Require Import ExtLib.Data.Monads.StateMonad.
Require Coq.Program.Wf.
Require Import Program.
Require Import Coq.Structures.OrdersEx.

(* St is the type of the [scoped] state used by the  heuristic *)
Record InlineHeuristic (St:Type) :=
  { update_funDef:(fundefs -> r_map -> St -> (St * St)); (* update inlining decision at functions declaraction. First state is used for the body of the program, second for the function definitions *)
    update_inFun:(var -> tag -> list var -> exp -> r_map -> St -> St); (* update inlining decisions when converting a function within a bundle *)
    update_App:(var -> tag -> list var -> St -> (St*bool)) (* update and return inlining decision for f on function application *) }.

  
Section Beta.

  Import MonadNotation.
  Open Scope monad_scope.
  
  Definition fun_map := M.t (tag * list var * exp).
  
  Definition freshen_exp (e:exp) : freshM exp  :=
    freshen_term e (M.empty _).
  
  Variable St:Type.
  Variable IH : InlineHeuristic St.

  
  (* Construct known-functions map *)
  Fixpoint add_fundefs (fds:fundefs) (fm: fun_map) : fun_map :=
    match fds with
    | Fnil => fm
    | Fcons f t xs e fds => M.set f (t, xs, e) (add_fundefs fds fm)
    end.

  Fixpoint beta_contract_fds (fds:fundefs) (fcon: St -> exp -> freshM exp) (sig:r_map) (s:St) : freshM fundefs :=
    match fds with 
    | Fcons f t xs e fds' =>
      let s' := update_inFun _ IH f t xs e sig s in (* ??? *)
      e' <- fcon s' e ;;
      fds'' <- beta_contract_fds fds' fcon sig s ;;
      ret (Fcons f t xs e' fds'')
    | Fnil => ret Fnil
    end.

  
  Fixpoint beta_contract (d : nat) {struct d} :=
    let fix beta_contract_aux (e : exp) (sig : r_map) (fm:fun_map) (s:St) {struct e} : freshM exp :=
        match e with
        | Econstr x t ys e =>
          let ys' := apply_r_list sig ys in
          e' <- beta_contract_aux e sig fm s;;
          ret (Econstr x t ys' e')
        | Ecase v cl =>
          let v' := apply_r sig v in
          cl' <- (fix beta_list (br: list (cTag*exp)) : freshM (list (cTag*exp)) :=
                   match br with
                   | nil => ret ( nil)
                   | (t, e)::br' =>
                     e' <- beta_contract_aux e sig fm s;;
                     br'' <- beta_list br';;
                     ret ((t, e')::br'')
                   end) cl;;
          ret (Ecase v' cl')
       | Eproj x t n y e =>
         let y' := apply_r sig y in
         e' <- beta_contract_aux e sig fm s;;
         ret (Eproj x t n y' e')
       | Efun fds e =>
         let fm' := add_fundefs fds fm in
         let (s1, s2) := update_funDef _ IH fds sig s in (* ??? *)
         e' <- beta_contract_aux e sig fm' s1;;
         fds' <- (fix beta_contract_fds (fds:fundefs) (sf:St) : freshM fundefs :=
                   match fds with 
                   | Fcons f t xs e fds' =>
                     let s' := update_inFun _ IH f t xs e sig s in (* ??? *)
                     e' <- beta_contract_aux e sig fm' s' ;;
                     fds'' <- beta_contract_fds fds' s ;;
                     ret (Fcons f t xs e' fds'')
                   | Fnil => ret Fnil
                   end) fds s2 ;;
         ret (Efun fds' e')
       | Eapp f t ys =>
         let f' := apply_r sig f in
         let ys' := apply_r_list sig ys in
         let (s, inl) := update_App _ IH f' t ys' s in
         (match (inl, M.get f' fm, d) with
          | (true, Some (t, xs, e), S d') =>
            let sig' := set_list (combine xs ys') sig  in
            e' <- freshen_exp e;;
            beta_contract d' e' sig' fm  s
          | _ => ret (Eapp f' t ys')
          end)
       | Eprim x t ys e =>
         let ys' := apply_r_list sig ys in
         e' <- beta_contract_aux e sig fm s;;
         ret (Eprim x t ys' e')
       | Ehalt x =>
         let x' := apply_r sig x in
         ret (Ehalt x')
        end
    in beta_contract_aux.
                 

  (* Old fds for reference *)
  (* Function beta_contract_fds (fds:fundefs) (fcon: St -> forall e:exp, (term_size e < funs_size fds)%nat -> freshM exp)  (fdc:fundefs) (sig:r_map) (s:St) (p:  cps_util.subfds_or_eq fdc fds): freshM fundefs := *)
  (*   (match fdc as x return x = fdc -> _ with *)
  (*    | Fcons f t xs e fdc' => *)
  (*      fun Heq_fdc => *)
  (*        let s' := update_inFun _ IH f t xs e sig s in *)
  (*       e' <- fcon s' e (beta_contract_fds_1 (eq_ind_r (fun a => cps_util.subfds_or_eq a fds) p Heq_fdc));; *)
  (*       fds' <- beta_contract_fds fds fcon fdc' sig s (beta_contract_fds_2 (eq_ind_r (fun a => cps_util.subfds_or_eq a fds) p Heq_fdc));; *)
  (*        ret (Fcons f t xs e' fds') *)
  (*   | Fnil => fun _ => ret Fnil *)
  (*   end) (eq_refl fdc). *)

  Definition beta_contract_top (e:exp) (d:nat) (s:St) (names:nEnv) : exp * nEnv :=
    let n :=((max_var e 1) + 1)%positive in
    match runState (beta_contract d e (M.empty var) (M.empty _) s) (n, names) with
    | (e', (_, names')) => (e', names)
    end.
  
End Beta.


Definition CombineInlineHeuristic {St1 St2:Type} (deci:bool -> bool -> bool) (IH1:InlineHeuristic St1) (IH2:InlineHeuristic St2) : InlineHeuristic (prod St1 St2) :=
  {| update_funDef :=
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
  {| update_funDef := fun (fds:fundefs) (sigma:r_map) (s:_) => (s, s);
     update_inFun := fun (f:var) (t:tag) (xs:list var) (e:exp) (sigma:r_map) (s:_) => s;
     update_App := fun (f:var) (t:tag) (ys:list var) (s:_) =>
                    match (M.get f s, ys) with
                    | (Some 1, k::ys') =>
                      (M.set f 0 (M.set k 2 s), true)
                    | (Some 2, _ ) =>
                      (s, true)
                    | _ => (s, false)
                    end
  |}.

Definition InlineSmallIH (bound:nat): InlineHeuristic (M.t bool) :=
  {| (* Add small, [todo: non-recursive] functions to s *)
    update_funDef  := (fun (fds:fundefs) (sigma:r_map) (s:_) =>
                         let s' := 
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

Definition InlineSmallOrUncurried (bound:nat): InlineHeuristic (prod (M.t bool) (M.t nat)) :=
  CombineInlineHeuristic orb (InlineSmallIH bound) (PostUncurryIH).


(* d should be max argument size, perhaps passed through by uncurry *)
Definition postuncurry_contract (e:exp) (s:M.t nat) (d:nat) :=
  beta_contract_top _ PostUncurryIH e d s.

Definition inlinesmall_contract (e:exp) (bound:nat)  (d:nat) :=
  beta_contract_top _ (InlineSmallIH bound) e d (M.empty _).

Definition inline_uncurry_contract (e:exp) (s:M.t nat) (bound:nat)  (d:nat) :=
  beta_contract_top _ (InlineSmallOrUncurried bound) e d (M.empty bool, s).

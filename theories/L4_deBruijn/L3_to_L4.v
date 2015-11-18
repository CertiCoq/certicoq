(** Naive conversion to continuation-passing style for a core language including
    mutually recursive functions, data constructors, and pattern matching.
*)
Require Import Arith BinNat String List Omega Program Psatz.
Require Export Common.Common.  (* shared namespace *)
Open Scope N_scope.
Opaque N.add.
Opaque N.sub.

Require Import L3.program.

Require L3.
Module L3eval := L3.wndEval.
Module L3t := L3.term.
Module L3U := L3.unaryApplications.
Require Import L4.expression.

Definition dcon_of_con (i : inductive) (n : nat) := N.of_nat n.

(** Unit type single constructor *)
Definition dummy := Con_e 0 enil.

(** Definition environment *)
Definition env := list (string * exp).

Fixpoint cst_offset (e : env) (s : string) : N :=
  match e with
  | [] => 0%N
  | (c, e) :: tl => if string_eq_bool s c then 0 else cst_offset tl s + 1
  end.

(** Inductive environment: disappears at this stage *)
Definition ienv := list (string * itypPack).

Section TermTranslation.
  Variable ie : ienv.
  Variable e : env.
    
  Fixpoint strip_lam (k : nat) (e : exp) : exp :=
    match k, e with
    | 0%nat, _ => e
    | S n, Lam_e e => strip_lam n e
    | S n, _ => e
    end.
  
  Fixpoint trans (k : N) (t : L3t.Term) : exp :=
    match t with
    | L3t.TRel n => Var_e (N.of_nat n)
    | L3t.TSort s => (* Erase *) dummy
    | L3t.TProd n t => (* Erase *) dummy
    | L3t.TLambda n t => Lam_e (trans (k+1) t)
    | L3t.TLetIn n t u => Let_e (trans k t) (trans (k+1) u)
    | L3t.TApp t u => App_e (trans k t) (trans k u)
    | L3t.TConst s => (* Transform to let-binding *)
      Var_e (cst_offset e s + k)
    | L3t.TInd i => (* Erase *) dummy
    | L3t.TConstruct ind c args =>
      let fix args' l :=
        match l with
        | L3t.tnil => enil
        | L3t.tcons t ts => econs (trans k t) (args' ts)
        end
      in Con_e (dcon_of_con ind c) (args' args)
    | L3t.TCase ann t brs =>
      let fix brs' n l :=
          match l with
          | L3t.tnil => brnil_e
          | L3t.tcons t ts =>
            let nargs := List.nth (N.to_nat n) (snd ann) 0%nat in
            brcons_e n (N.of_nat nargs) (strip_lam nargs (trans k t))
                 (brs' (n + 1)%N ts)
          end
      in Match_e (trans k t) (brs' (0%N) brs)
    | L3t.TFix d n =>
      let fix defs' l :=
          match l with
          | L3t.dnil => eflnil
          | L3t.dcons na t _ l' =>
            let t' := trans (k + 1) t in
              eflcons (strip_lam 1 t') (defs' l')
          end
      in      
      Fix_e (defs' d) (N.of_nat n)
    end.

End TermTranslation.

Definition translate (e : env) t :=
  trans e 0 t.

Definition translate_env (e : environ) : env :=
  fold_right
    (fun x acc => match x with
               | (s, ecTrm t) =>
                 let t' := translate acc t in
                   (s, t') :: acc
               | (s, ecTyp _) => acc
               end) [] e.

Definition mkLets (e : env) (t : exp) :=
  fold_left (fun acc (x : string * exp) => let (s, t) := x in Let_e t acc) e t.

Definition translate_program (e : environ) (t : L3t.Term) : exp :=
  let e' := translate_env e in
    mkLets e' (translate e' t).
              
Theorem translate_correct (e : environ) (t t' : L3t.Term) :
  L3eval.wndEval e t t' -> (* small step non-deterministic *)
  eval (translate_program e t) (translate_program e t') (* big-step deterministic *).
Proof.
  induction 1. simpl. red in H.
Admitted.

(** start-to-L4 translations **)

Definition myprogram_Program (pgm : program) :=
  do pgm0 <- malecha_L1.program_Program pgm (Ret nil);
    let e' := stripEvalCommute.stripEnv (program.env pgm0) in
    match L3U.stripEnv e' with
    | Some senv => 
      match L3U.strip e' (stripEvalCommute.strip (program.main pgm0)) with
      | Some smain => Ret {| main := smain; L3.program.env := senv |}
      | None => Exc "Error in stripping"
      end
    | None => Exc "Error while stripping environment"
    end.

Definition program_exp (pgm:program) : exception exp :=
  do prg <- myprogram_Program pgm;
      let (main, env) := prg in
      Ret (translate_program env main).

Definition term_exp (e:program.environ) (t:term) : exception exp :=
  let e' := stripEvalCommute.stripEnv e in
  match L3U.term_Term e' t with
  | None => Exc "Error while translating term to L3"
  | Some trm =>
    match L3U.stripEnv e' with
    | None => Exc "Error while stripping environment"
    | Some e => Ret (translate_program e trm)
    end
  end.

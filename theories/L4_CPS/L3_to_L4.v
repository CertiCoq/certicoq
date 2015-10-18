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
Require Import simple_cps.

Definition dcon_of_con (i : inductive) (n : nat) := N.of_nat n.

(** Unit type single constructor *)
Definition dummy := Con_e 0 [].

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

  (* Fixpoint fix_subst (n : nat) := *)
  (*   match n with *)
  (*   | 0%nat => [Proj_e (Var_e 0%N) 0%N] *)
  (*   | S n' => *)
  (*     (Proj_e (Var_e 0%N) (N.of_nat n)) :: fix_subst n' *)
  (*   end. *)

  Fixpoint fix_subst (n : nat) (k : N) (t : exp) :=
    match n with
    | 0%nat => (* Go over the tuple binder *) shift 1 k t
    | S n' =>
      Let_e (Proj_e (Var_e k) (N.of_nat n')) (fix_subst n' (k + 1) t) 
    end.

  Definition reloc n := Var_e n.
  Definition reloc_lam (r : N -> exp) :=
    fun n => match n with N0 => Var_e 0 | Npos n' => shift 1 0 (r (N.pred n)) end.
  
  Definition reloc_fix k (r : N -> exp) i :=
    fun n => if n <? k then Proj_e (Var_e 0) i else Var_e (N.sub n (N.pred k)).
    
  Fixpoint strip_lam (k : nat) (e : exp) : exp :=
    match k, e with
    | 0%nat, _ => e
    | S n, Lam_e e => strip_lam n e
    | S n, _ => e
    end.
  
  Fixpoint trans (k : N) (reloc : N -> exp) (t : L3t.Term) : exp :=
    match t with
    | L3t.TRel n => reloc (N.of_nat n)
    | L3t.TSort s => (* Erase *) dummy
    | L3t.TProd n t => (* Erase *) dummy
    | L3t.TLambda n t => Lam_e (trans (k+1) (reloc_lam reloc) t)
    | L3t.TLetIn n t u => Let_e (trans k reloc t)
                               (trans (k+1) (reloc_lam reloc) u)
    | L3t.TApp t u => App_e (trans k reloc t) (trans k reloc u)
    | L3t.TConst s => (* Transform to let-binding *)
      Var_e (cst_offset e s + k)
    | L3t.TInd i => (* Erase *) dummy
    | L3t.TConstruct ind c args =>
      let fix args' l :=
        match l with
        | L3t.tnil => nil
        | L3t.tcons t ts => cons (trans k reloc t) (args' ts)
        end
      in Con_e (dcon_of_con ind c) (args' args)
    | L3t.TCase ann t brs =>
      let fix brs' n l :=
          match l with
          | L3t.tnil => nil
          | L3t.tcons t ts =>
            let nargs := List.nth (N.to_nat n) (snd ann) 0%nat in
            cons (n, N.of_nat nargs, strip_lam nargs (trans k reloc t))
                 (brs' (n + 1)%N ts)
          end
      in Match_e (trans k reloc t) (brs' (0%N) brs)
    | L3t.TFix d n =>
      (** Discuss with Olivier how to change cps for that *)
      let len := N.of_nat (L3t.dlength d) in
      let fix defs' l i :=
          match l with
          | L3t.dnil => nil
          | L3t.dcons na t _ l' =>
            let t' := trans (k + 1) (reloc_fix len reloc i) t in
              cons t' (defs' l' (i + 1))
          end
      in      
      Proj_e (Fix_e (defs' d 0)) (N.of_nat n)
    end.

  (** The [TFix d n] block assumes that recursive calls to [di] in [d] are of the 
      form [TRel ki], while in the cps exp encoding, this becomes a projection
      of a tuple, we hence have to substitute these rels in [t] by the right
      projections. Actually, we have no substitution operation on L3 terms, so
      we have to use let-bindings instead. *)

End TermTranslation.

Definition translate (e : env) t :=
  trans e 0 reloc t.

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

(** Testing the compiler *)

Require Import Template.Template.
Definition Nat := nat.
Definition typedef := ((fun (A:Type) (a:A) => a) Nat 1%nat).

Quote Definition q_typedef := Eval compute in typedef.
Quote Recursively Definition p_typedef := typedef.
Definition L1_typedef :=
  Eval compute in malecha_L1.program_Program p_typedef (Ret nil).

Definition P_typedef := Eval compute in program_exp p_typedef.

Fixpoint slowFib (n:nat) : nat :=
  match n with
    | 0%nat => 0
    | S m => match m with
               | 0%nat => 1
               | S p => slowFib p + slowFib m
             end
  end.
Eval compute in (slowFib 0).
Eval compute in (slowFib 1).
Eval compute in (slowFib 2).
Eval compute in (slowFib 3).
Eval compute in (slowFib 4).

Fixpoint idn (n : nat) : nat :=
  match n with 0%nat => 0 | S n => S (idn n) end.

Definition matchn (n : nat) : nat :=
  match n with 0%nat => 0 | S n => n end.

Quote Recursively Definition p_0 := 0.
Quote Recursively Definition p_idn := idn.
Quote Recursively Definition p_idn1 := (idn 1).

Quote Recursively Definition p_slowFib1 := (slowFib 1).
Quote Recursively Definition p_matchn := (matchn 1).

Quote Recursively Definition p_add := Nat.add.
Quote Recursively Definition p_add01 := (Nat.add 0%nat 1).
Transparent N.add.
Eval compute in program_exp p_add.

Definition compile (p : program) : exception cps :=
  do e <- program_exp p; Ret (cps_cvt_prog e).

Definition paddexp := Eval compute in compile p_add.

Definition padd01 := Eval compute in compile p_add01.

Definition run (p : program) : exception ans :=
  do c <- compile p; Ret (eval_c_n 1000 c).
Eval compute in run p_0.

Eval compute in program_exp p_add01.
Eval compute in run p_add01.
Eval compute in program_exp p_matchn.
Eval compute in run p_matchn.

Eval compute in program_exp p_idn.

Eval compute in program_exp p_idn1.
Eval compute in run p_idn1.

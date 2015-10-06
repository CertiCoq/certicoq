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
  
  Fixpoint translate (k : N) (t : L3t.Term) : exp :=
    match t with
    | L3t.TRel n => Var_e (N.of_nat n)
    | L3t.TSort s => (* Erase *) dummy
    | L3t.TProd n t => (* Erase *) dummy
    | L3t.TLambda n t => Lam_e (translate (k+1) t)
    | L3t.TLetIn n t u => Let_e (translate k t) (translate (k+1) u)
    | L3t.TApp t u => App_e (translate k t) (translate k u)
    | L3t.TConst s => (* Transform to let-binding *)
      Var_e (cst_offset e s + k)
    | L3t.TInd i => (* Erase *) dummy
    | L3t.TConstruct ind c args =>
      let fix args' l :=
        match l with
        | L3t.tnil => nil
        | L3t.tcons t ts => cons (translate k t) (args' ts)
        end
      in Con_e (dcon_of_con ind c) (args' args)
    | L3t.TCase n t brs =>
      let fix brs' n l :=
          match l with
          | L3t.tnil => nil
          | L3t.tcons t ts =>
            cons (n, 0 (* Number of args of n, impossible to infer here *),
                  translate k t) (brs' (n + 1)%N ts)
          end
      in Match_e (translate k t) (brs' (0%N) brs)
    | L3t.TFix d n =>
      let len := L3t.dlength d in
      let subst := fix_subst len 0 in
      let fix defs' l :=
          match l with
          | L3t.dnil => nil
          | L3t.dcons na t _ l' =>
            let t' := translate (k + N.of_nat len) t in
              cons (subst t') (defs' l')
          end
      in      
      Proj_e (Fix_e (defs' d)) (N.of_nat n)
    end.

  (** The [TFix d n] block assumes that recursive calls to [di] in [d] are of the 
      form [TRel ki], while in the cps exp encoding, this becomes a projection
      of a tuple, we hence have to substitute these rels in [t] by the right
      projections. Actually, we have no substitution operation on L3 terms, so
      we have to use let-bindings instead. *)
  
End TermTranslation.

Definition translate_env (e : environ) : env :=
  fold_right
    (fun x acc => match x with
               | (s, ecTrm t) =>
                 let t' := translate acc 0%N t in
                   (s, t') :: acc
               | (s, ecTyp _) => acc
               end) [] e.

Definition mkLets (e : env) (t : exp) :=
  fold_left (fun acc (x : string * exp) => let (s, t) := x in Let_e t acc) e t.

Definition translate_program (e : environ) (t : L3t.Term) : exp :=
  let e' := translate_env e in
    mkLets e' (translate e' 0 t).
              
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

Quote Recursively Definition p_0 := 0.
Quote Recursively Definition p_idn := idn.
Quote Recursively Definition p_idn1 := (idn 1).

Quote Recursively Definition p_slowFib1 := (slowFib 1).

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

Eval compute in program_exp p_idn.

Eval compute in program_exp p_idn1.
Eval compute in run p_idn1.

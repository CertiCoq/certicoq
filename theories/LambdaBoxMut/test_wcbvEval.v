
Require Import Recdef.
Require Import Coq.micromega.Lia.
Require Import Coq.Arith.PeanoNat.
Require Import Common.Common.
Require Import LambdaBoxMut.compile.
Require Import LambdaBoxMut.term.
Require Import LambdaBoxMut.wcbvEval.

Require Import TemplateExtraction.EAst Template.kernel.univ.

Local Open Scope string_scope.
Local Open Scope bool.
Local Open Scope list.
Set Implicit Arguments.

Set Printing Width 80.
Set Printing Depth 1000.

#[global] Instance fuel : utils.Fuel := { fuel := 2 ^ 14 }.

Quote Recursively Definition p_Type := Type.
Print p_Type.
Definition P_Type := Eval cbv in (program_Program p_Type).
Print P_Type.

(** test eta expansion: constructor expecting 1 arg and 0 params **)
Inductive etaC01 := EtaC01 : forall b:bool, etaC01.
Quote Recursively Definition p_etaC01 := EtaC01.
Definition P_etaC01 := Eval cbv in (program_Program p_etaC01).
Print P_etaC01.

Inductive DD := D2: bool -> bool -> DD.
Quote Recursively Definition p_etaTst := (D2 true false).
Print p_etaTst.
Definition P_etaTst := Eval cbv in (program_Program p_etaTst).
Print P_etaTst.
Compute
  let env := (env P_etaTst) in
  let main := (main P_etaTst) in
  wcbvEval (env) 10 (main).
Quote Recursively Definition p_LetaTst := (fun (x:bool) => (D2 true x)).
Print p_LetaTst.
Definition P_LetaTst := Eval cbv in (program_Program p_LetaTst).
Print P_LetaTst.
Compute
  let env := (env P_LetaTst) in
  let main := (main P_LetaTst) in
  wcbvEval (env) 10 (main).

(** trivial example **)
Definition one := 1.
Quote Recursively Definition cbv_one := (* [program] of Coq's answer *)
  ltac:(let t:=(eval cbv in (one)) in exact t).
Print cbv_one.
(* [Term] of Coq's answer *)
Definition ans_one := Eval cbv in (main (program_Program cbv_one)).
Print ans_one.
(* [program] of the program *)
Quote Recursively Definition p_one := one.
Print p_one.
Definition P_one := Eval cbv in (program_Program p_one).
Print P_one.
Goal
  let env := (env P_one) in
  let main := (main P_one) in
  wcbvEval (env) 100 (main) = Ret ans_one.
  vm_compute. reflexivity.
Qed.

Definition ten := 10.
Quote Recursively Definition cbv_ten := (* [program] of Coq's answer *)
  ltac:(let t:=(eval cbv in (ten)) in exact t).
Print cbv_ten.
(* [Term] of Coq's answer *)
Definition ans_ten := Eval cbv in (main (program_Program cbv_ten)).
Print ans_ten.
(* [program] of the program *)
Quote Recursively Definition p_ten := ten.
Print p_ten.
Definition P_ten := Eval cbv in (program_Program p_ten).
Print P_ten.
Goal
  let env := (env P_ten) in
  let main := (main P_ten) in
  wcbvEval (env) 100 (main) = Ret ans_ten.
  vm_compute. reflexivity.
Qed.

Definition plus01 := (plus 0 1).
Quote Recursively Definition cbv_plus01 := (* [program] of Coq's answer *)
  ltac:(let t:=(eval cbv in (plus01)) in exact t).
Print cbv_plus01.
(* [Term] of Coq's answer *)
Definition ans_plus01 := Eval cbv in (main (program_Program cbv_plus01)).
Print ans_plus01.
(* [program] of the program *)
Quote Recursively Definition p_plus01 := plus01.
Print p_plus01.
Definition P_plus01 := Eval cbv in (program_Program p_plus01).
Print P_plus01.
Goal
  let env := (env P_plus01) in
  let main := (main P_plus01) in
  wcbvEval (env) 10 (main) = Ret ans_plus01.
Proof.
  cbv. reflexivity.
Qed.

Definition plus10 := (plus 1 0).
Quote Recursively Definition cbv_plus10 := (* [program] of Coq's answer *)
  ltac:(let t:=(eval cbv in (plus10)) in exact t).
Print cbv_plus10.
(* [Term] of Coq's answer *)
Definition ans_plus10 := Eval cbv in (main (program_Program cbv_plus10)).
Print ans_plus10.
(* [program] of the program *)
Quote Recursively Definition p_plus10 := plus10.
Print p_plus10.
Definition P_plus10 := Eval cbv in (program_Program p_plus10).
Print P_plus10.
Goal
  let env := (env P_plus10) in
  let main := (main P_plus10) in
  wcbvEval (env) 100 (main) = Ret ans_plus10.
Proof.
  cbv. reflexivity.
Qed.

(**********
Goal
  let env := (env P_plus10) in
  let main := (main P_plus10) in
  WcbvEval (env) (main) ans_plus10.
Proof.
  intros. unfold main, AstCommon.env, AstCommon.main, P_plus10, ans_plus10.
  eapply wConst.
  - unfold lookupDfn. cbn. reflexivity.
  - eapply wAppLam.
    + eapply wAppFix.
      * eapply wConst.
        -- unfold lookupDfn. cbn. reflexivity.
        -- apply wFix.
      * cbn. reflexivity.
      * eapply wAppLam.
        -- eapply wLam.
        -- eapply wConstruct. eapply wCons.
           ++ eapply wConstruct. eapply wNil.
           ++ eapply wNil.
        -- cbn. eapply wLam.
    + eapply wConstruct. eapply wNil.
    + cbn. eapply wCase.
      * eapply wConstruct. eapply wCons.
        -- eapply wConstruct. eapply wNil.
        -- eapply wNil.
      * unfold whCaseStep.Print bnth. unfold bnth.
      * cbn. reflexivity.

        

          
    + eapply wAppFix.
      * eapply wConst.
        -- unfold lookupDfn. cbn. reflexivity.
        -- apply wFix.
      * cbn. reflexivity.
      * eapply wAppLam.
        -- eapply wLam.
        -- eapply wConstruct. eapply wCons.
           ++ eapply wConstruct. eapply wNil.
           ++ eapply wNil.
        -- unfold whBetaStep, instantiate. eapply wLam.
    + eapply wConstruct. eapply wNil.
    + unfold whBetaStep, instantiate. unfold ans_plus10. eapply wCase.
      * cbn. eapply wConstruct. eapply wCons.
        -- eapply wConstruct. eapply wNil.
        -- eapply wNil.
      * cbn. reflexivity.
      *

        
Goal
  let env := (env P_plus10) in
  let main := (main P_plus10) in
  wcbvEval (env) 100 (main) = Ret ans_plus10.
Proof.
  cbv. reflexivity.
Qed.
 ********************)

Definition plus98 := (plus 9 8).
Quote Recursively Definition cbv_plus98 := (* [program] of Coq's answer *)
  ltac:(let t:=(eval cbv in (plus98)) in exact t).
Print cbv_plus98.
(* [Term] of Coq's answer *)
Definition ans_plus98 := Eval cbv in (main (program_Program cbv_plus98)).
Print ans_plus98.
(* [program] of the program *)
Quote Recursively Definition p_plus98 := plus98.
Print p_plus98.
Definition P_plus98 := Eval cbv in (program_Program p_plus98).
Print P_plus98.
Goal
  let env := (env P_plus98) in
  let main := (main P_plus98) in
  wcbvEval (env) 100 (main) = Ret ans_plus98.
Proof.
  vm_compute. reflexivity.
Qed.

(** nested Let **)
Definition nestedLet := let x := 0 in let y := 1 in x.
Quote Recursively Definition cbv_nestedLet := (* [program] of Coq's answer *)
  ltac:(let t:=(eval cbv in nestedLet) in exact t).
Print cbv_nestedLet.
(* [Term] of Coq's answer *)
Definition ans_nestedLet := Eval cbv in (main (program_Program cbv_nestedLet)).
Print ans_nestedLet.
(* [program] of the program *)
Quote Recursively Definition p_nestedLet := nestedLet.
Print p_nestedLet.
Definition P_nestedLet := Eval cbv in (program_Program p_nestedLet).
Print P_nestedLet.
Goal
  let env := (env P_nestedLet) in
  let main := (main P_nestedLet) in
  wcbvEval (env) 100 (main) = Ret ans_nestedLet.
Proof.
  vm_compute. reflexivity.
Qed.
Goal  (* Why does this work? *)
  let env := (env P_nestedLet) in
  let main := (main P_nestedLet) in
  WcbvEval env main ans_nestedLet.
Proof.
  intros. unfold main, AstCommon.main, P_nestedLet.
  eapply wConst.
  - reflexivity.
  - eapply wLetIn.
    + eapply wConstruct. eapply wNil.
    + cbn. eapply wLetIn.
      * eapply wConstruct. eapply wCons.
        -- eapply wConstruct. eapply wNil.
        -- eapply wNil.
      * cbn. eapply wConstruct. eapply wNil.
Qed.

(** vector addition **)
Require Coq.Vectors.Vector.
Print Fin.t.
Print Vector.t.

Definition vplus (n:nat) :
  Vector.t nat n -> Vector.t nat n -> Vector.t nat n := (Vector.map2 plus).
Definition v01 : Vector.t nat 2 :=
  (Vector.cons nat 0 1 (Vector.cons nat 1 0 (Vector.nil nat))).
Definition v23 : Vector.t nat 2 :=
  (Vector.cons nat 2 1 (Vector.cons nat 3 0 (Vector.nil nat))).
Definition vplus0123 := (vplus v01 v23).
Quote Recursively Definition cbv_vplus0123 := (* [program] of Coq's answer *)
  ltac:(let t:=(eval cbv in (vplus0123)) in exact t).
Print cbv_vplus0123.
(* [Term] of Coq's answer *)
Definition ans_vplus0123 := Eval cbv in (main (program_Program cbv_vplus0123)).
(* [program] of the program *)
Quote Recursively Definition p_vplus0123 := vplus0123.
Print p_vplus0123.
Definition P_vplus0123 := Eval cbv in (program_Program p_vplus0123).
Print P_vplus0123.
Goal
  let env := (env P_vplus0123) in
  let main := (main P_vplus0123) in
  wcbvEval (env) 100 (main) = Ret ans_vplus0123.
  vm_compute. reflexivity.
Qed.

(** Ackermann **)
Fixpoint ack (n m:nat) {struct n} : nat :=
  match n with
    | 0 => S m
    | S p => let fix ackn (m:nat) {struct m} :=
                 match m with
                   | 0 => ack p 1
                   | S q => ack p (ackn q)
                 end
             in ackn m
  end.
Definition ack35 := (ack 3 5).
Quote Recursively Definition cbv_ack35 :=
  ltac:(let t:=(eval cbv in ack35) in exact t).
Print cbv_ack35.
Definition ans_ack35 :=
  Eval cbv in (main (program_Program cbv_ack35)).
Print ans_ack35.
(* [program] of the program *)
Quote Recursively Definition p_ack35 := ack35.
Print p_ack35.
Definition P_ack35 := Eval cbv in (program_Program p_ack35).
Print P_ack35.
Goal
  let env := (env P_ack35) in
  let main := (main P_ack35) in
  wcbvEval (env) 2000 (main) = Ret ans_ack35.
  vm_compute. reflexivity.
Qed.

(** mutual recursion **)
Inductive tree (A:Set) : Set :=
  node : A -> forest A -> tree A
with forest (A:Set) : Set :=
     | leaf : A -> forest A
     | fcons : tree A -> forest A -> forest A.

Definition sf: forest bool := (fcons (node true (leaf false)) (leaf true)).
Quote Recursively Definition p_sf := sf.
Eval cbv in (program_Program p_sf).

Fixpoint tree_size (t:tree bool) : nat :=
  match t with
    | node a f => S (forest_size f)
  end
with forest_size (f:forest bool) : nat :=
       match f with
         | leaf b => 1
         | fcons t f1 => (tree_size t + forest_size f1)
       end.

Definition arden: forest bool :=
  fcons (node true (fcons (node true (leaf false)) (leaf true)))
        (fcons (node true (fcons (node true (leaf false)) (leaf true)))
               (leaf false)).
Quote Recursively Definition p_arden := arden.
Definition arden_size := (forest_size arden).
Quote Recursively Definition cbv_arden_size :=
  ltac:(let t:=(eval cbv in arden_size) in exact t).
Definition ans_arden_size :=
  Eval cbv in (main (program_Program cbv_arden_size)).
(* [program] of the program *)
Quote Recursively Definition p_arden_size := arden_size.
Print p_arden_size.
Definition P_arden_size := Eval cbv in (program_Program p_arden_size).
Print P_arden_size.
Eval cbv in (env P_arden_size).
Goal
  let env := (env P_arden_size) in
  let main := (main P_arden_size) in
  wcbvEval env 50 main = Ret ans_arden_size.
  vm_compute. reflexivity.
Qed.

(** SASL tautology function: variable arity **)
Fixpoint tautArg (n:nat) : Type :=
  match n with
    | 0 => bool
    | S n => bool -> tautArg n
  end.
Fixpoint taut (n:nat) : tautArg n -> bool :=
  match n with
    | 0 => (fun x => x)
    | S n => fun x => taut n (x true) && taut n (x false)
  end.
(* Pierce *)
Definition pierce := taut 2 (fun x y => implb (implb (implb x y) x) x).
Quote Recursively Definition cbv_pierce :=
  ltac:(let t:=(eval cbv in pierce) in exact t).
Print cbv_pierce.
Definition ans_pierce :=
  Eval cbv in (main (program_Program cbv_pierce)).
Print ans_pierce.
(* [program] of the program *)
Quote Recursively Definition p_pierce := pierce.
Print p_pierce.
Definition P_pierce := Eval cbv in (program_Program p_pierce).
Print P_pierce.
Goal
  let env := (env P_pierce) in
  let main := (main P_pierce) in
  wcbvEval (env) 200 (main) = Ret ans_pierce.
  vm_compute. reflexivity.
Qed.
(* S combinator *)
Definition Scomb := taut 3
         (fun x y z => implb (implb x (implb y z))
                             (implb (implb x y) (implb x z))).
Quote Recursively Definition cbv_Scomb :=
  ltac:(let t:=(eval cbv in Scomb) in exact t).
Print cbv_Scomb.
Definition ans_Scomb :=
  Eval cbv in (main (program_Program cbv_Scomb)).
Print ans_Scomb.
(* [program] of the program *)
Quote Recursively Definition p_Scomb := Scomb.
Print p_Scomb.
Definition P_Scomb := Eval cbv in (program_Program p_Scomb).
Print P_Scomb.
Goal
  let env := (env P_Scomb) in
  let main := (main P_Scomb) in
  wcbvEval (env) 200 (main) = Ret ans_pierce.
  vm_compute. reflexivity.
Qed.

(** Fibonacci **)
Fixpoint slowFib (n:nat) : nat :=
  match n with
    | 0 => 0
    | S m => match m with
               | 0 => 1
               | S p => slowFib p + slowFib m
             end
  end.
Definition slowFib3 := (slowFib 3).
Quote Recursively Definition cbv_slowFib3 :=
  ltac:(let t:=(eval cbv in slowFib3) in exact t).
Definition ans_slowFib3 :=
  Eval cbv in (main (program_Program cbv_slowFib3)).
(* [program] of the program *)
Quote Recursively Definition p_slowFib3 := slowFib3.
Definition P_slowFib3 := Eval cbv in (program_Program p_slowFib3).
Goal
  let env := (env P_slowFib3) in
  let main := (main P_slowFib3) in
  wcbvEval (env) 30 (main) = Ret ans_slowFib3.
  vm_compute. reflexivity.
Qed.

(* fast Fib *)
Fixpoint fibrec (n:nat) (fs:nat * nat) {struct n} : nat :=
  match n with
    | 0 => fst fs
    | (S n) => fibrec n (pair ((fst fs) + (snd fs)) (fst fs))
  end.
Definition fib : nat -> nat := fun n => fibrec n (pair 0 1).
Definition fib9 := fib 9.
Quote Recursively Definition cbv_fib9 :=
  ltac:(let t:=(eval cbv in fib9) in exact t).
Definition ans_fib9 :=
  Eval cbv in (main (program_Program cbv_fib9)).
(* [program] of the program *)
Quote Recursively Definition p_fib9 := fib9.
Definition P_fib9 := Eval cbv in (program_Program p_fib9).
Goal
  let env := (env P_fib9) in
  let main := (main P_fib9) in
  wcbvEval (env) 1000 (main) = Ret ans_fib9.
  vm_compute. reflexivity.
Qed.

(** Heterogenous datatypes, a la Matthes **)
Inductive PList : Set->Type:=  (* powerlists *)
| zero : forall A:Set, A -> PList A
| succ : forall A:Set, PList (A * A)%type -> PList A.

Definition myPList : PList nat :=
  succ (succ (succ (zero (((1,2),(3,4)),((5,6),(7,8)))))).

Fixpoint unzip (A:Set) (l:list (A*A)) {struct l} : list A :=
  match l return list A with
    | nil => nil
    | cons (a1,a2) l' => cons a1 (cons a2 (unzip l'))
  end.
Fixpoint PListToList (A:Set) (l:PList A) {struct l} : list A :=
  match l in PList A return list A with
    | zero a => cons a (nil )
    | succ l' => unzip (PListToList l')
  end.

Eval compute in PListToList myPList.

Fixpoint gen_sumPList (A:Set) (l:PList A) {struct l} : (A->nat)->nat :=
  match l in PList A return (A->nat)->nat with
    | zero a => fun f => f a
    | succ l' =>
      fun f => gen_sumPList l' (fun a => let (a1,a2) := a in f a1 + f a2)
  end.
Definition sumPList l := gen_sumPList l (fun x => x).
Definition sumPL_myPL := (sumPList myPList).
Quote Recursively Definition cbv_sumPL_myPL :=
  ltac:(let t:=(eval cbv in sumPL_myPL) in exact t).
Definition ans_sumPL_myPL :=
  Eval cbv in (main (program_Program cbv_sumPL_myPL)).
(* [program] of the program *)
Quote Recursively Definition p_sumPL_myPL := sumPL_myPL.
Definition P_sumPL_myPL := Eval cbv in (program_Program p_sumPL_myPL).
Goal
  let env := (env P_sumPL_myPL) in
  let main := (main P_sumPL_myPL) in
  wcbvEval (env) 1000 (main) = Ret ans_sumPL_myPL.
  vm_compute. reflexivity.
Qed.

Set Implicit Arguments.
Section List.
Variables X Y : Type.
Variable f : X -> Y -> Y.
Fixpoint fold (y : Y) (xs : list X) : Y :=
  match xs with
    | nil => y
    | cons x xr => fold (f x y) xr
  end.
End List.
Inductive Tree := T : list Tree -> Tree.
Fixpoint size (t : Tree) : nat :=
  match t with
    | T ts => S (fold (fun t a => size t + a) 0 ts)
  end.
Definition myTree :=
  (T (cons (T (unit (T nil))) (cons (T (unit (T nil))) nil))).
Eval cbv in size myTree.
Definition size_myTree := size myTree.
Quote Recursively Definition cbv_size_myTree :=
  ltac:(let t:=(eval cbv in size_myTree) in exact t).
Definition ans_size_myTree :=
  Eval cbv in (main (program_Program cbv_size_myTree)).
(* [program] of the program *)
Quote Recursively Definition p_size_myTree := size_myTree.
Definition P_size_myTree := Eval cbv in (program_Program p_size_myTree).
Goal
  let env := (env P_size_myTree) in
  let main := (main P_size_myTree) in
  wcbvEval (env) 100 (main) = Ret ans_size_myTree.
  vm_compute. reflexivity.
Qed.


Function provedCopy (n:nat) {wf lt n} :=
  match n with 0 => 0 | S k => S (provedCopy k) end.
Proof.
  - intros. constructor.
  - apply lt_wf.
Defined.
Print Assumptions provedCopy_tcc.
Quote Recursively Definition pCopy := provedCopy. (* program *)
Print provedCopy_tcc.
Definition x := 3.
Definition provedCopyx := provedCopy x.
Compute provedCopyx.  (** evals correctly in Coq **)
Quote Recursively Definition cbv_provedCopyx :=
  ltac:(let t:=(eval cbv in provedCopyx) in exact t).
Definition ans_provedCopyx :=
  Eval cbv in (main (program_Program cbv_provedCopyx)).
Quote Recursively Definition p_provedCopyx := provedCopyx. (* program *)
Definition P_provedCopyx :=                            (* Program *)
  Eval cbv in (program_Program p_provedCopyx).
Goal
  let env := (env P_provedCopyx) in
  let main := (main P_provedCopyx) in
  wcbvEval (env) 100 (main) = Ret ans_provedCopyx.
  vm_compute. reflexivity.
Qed.


Definition plusx := (plus 0).
Compute plusx.
Quote Recursively Definition cbv_plusx :=
  ltac:(let t:=(eval cbv in plusx) in exact t).
Definition ans_plusx :=
  Eval cbv in (main (program_Program cbv_plusx)).
Print ans_plusx.
(* [program] of the program *)
Quote Recursively Definition p_plusx := plusx.
Print plusx.
Definition P_plusx := Eval cbv in (program_Program p_plusx).
Goal
  let env := (env P_plusx) in
  let main := (main P_plusx) in
  wcbvEval (env) 90 (main) = Ret ans_plusx.
Proof.
  cbv. (** Coq cbv goes under lambda, but we don't **)
Admitted.


Section myplus.
  Variables (A:Type).
  Inductive myNat : Type :=
  | myZ: forall a:A, myNat.
  Definition myplus (m n: myNat) : A :=
    match m with
    | myZ a => a
    end.
End myplus.
Print myplus.
Definition myplusx := (myplus (myZ 0) (myZ 0)).
Compute myplusx.
Quote Recursively Definition cbv_myplusx :=
  ltac:(let t:=(eval cbv in myplusx) in exact t).
Definition ans_myplusx :=
  Eval cbv in (main (program_Program cbv_myplusx)).
Print ans_myplusx.
(* [program] of the program *)
Quote Recursively Definition p_myplusx := myplusx.
Print myplusx.
Definition P_myplusx := Eval cbv in (program_Program p_myplusx).
Goal  (** works in L1g **)
  let env := (env P_myplusx) in
  let main := (main P_myplusx) in
  wcbvEval (env) 90 (main) = Ret ans_myplusx.
Proof.
  vm_compute. reflexivity.
Qed.

Quote Recursively Definition p_and_rect := and_rect.
Eval cbv in (program_Program p_and_rect).
Definition and_rect_x :=
  (and_rect (fun (a:1=1) (b:True) => conj b a) (conj (eq_refl 1) I)).
Quote Recursively Definition p_and_rect_x := and_rect_x.
Print p_and_rect_x.
Definition P_and_rect_x := Eval cbv in (program_Program p_and_rect_x).
Print P_and_rect_x.
Quote Recursively Definition cbv_and_rect_x :=
  ltac:(let t:=(eval cbv in and_rect_x) in exact t).
Print cbv_and_rect_x.
Eval cbv in (main (program_Program cbv_and_rect_x)).
Definition ans_and_rect_x :=
  Eval cbv in (main (program_Program cbv_and_rect_x)).
Print ans_and_rect_x.
Goal
  let envx := env P_and_rect_x in
  let mainx := main P_and_rect_x in
  wcbvEval envx 25 mainx = Ret ans_and_rect_x.
  vm_compute. reflexivity. 
Qed.

(****** veriStar benchmark **************)
Require Import Benchmarks.vs.
Quote Recursively Definition p_Valid := vs.VeriStar.Valid.
Definition valid := (AstCommon.main (program_Program p_Valid)).

Time Quote Recursively Definition p_ce_example_myent := vs.ce_example_myent.
Time Definition P_ce_example_myent :=
  Eval vm_compute in (program_Program p_ce_example_myent).
Definition P_env_ce_example_myent :=
  Eval vm_compute in (env P_ce_example_myent).
Definition P_main_ce_example_myent :=
  Eval vm_compute in (AstCommon.main P_ce_example_myent).
Time Definition eval_ce_example_myent :=
  Eval vm_compute in
    (wcbvEval P_env_ce_example_myent 400 P_main_ce_example_myent).
Print eval_ce_example_myent.
Goal eval_ce_example_myent = ret valid.
  vm_compute. reflexivity. 
Qed.

Time Quote Recursively Definition p_ce_example_ent := vs.ce_example_ent.
Time Definition P_ce_example_ent :=
  Eval vm_compute in (program_Program p_ce_example_ent).
Definition P_env_ce_example_ent :=
  Eval vm_compute in (env P_ce_example_ent).
Definition P_main_ce_example_ent :=
  Eval vm_compute in (AstCommon.main P_ce_example_ent).
Time Definition eval_ce_example_ent :=
  Eval vm_compute in
    (wcbvEval P_env_ce_example_ent 2000 P_main_ce_example_ent).
Print eval_ce_example_ent.
Goal eval_ce_example_ent = ret valid.
  vm_compute. reflexivity. 
Qed.

Time Quote Recursively Definition p_ce_example1_myent := vs.ce_example1_myent.
Time Definition P_ce_example1_myent :=
  Eval vm_compute in (program_Program p_ce_example1_myent).
Definition P_env_ce_example1_myent :=
  Eval vm_compute in (env P_ce_example1_myent).
Definition P_main_ce_example1_myent :=
  Eval vm_compute in (AstCommon.main P_ce_example1_myent).
Time Definition eval_ce_example1_myent :=
  Eval vm_compute in
    (wcbvEval P_env_ce_example1_myent 400 P_main_ce_example1_myent).
Print eval_ce_example1_myent.
Goal eval_ce_example1_myent = ret valid.
  vm_compute. reflexivity. 
Qed.

Time Quote Recursively Definition p_ce_example2_myent := vs.ce_example2_myent.
Time Definition P_ce_example2_myent :=
  Eval vm_compute in (program_Program p_ce_example2_myent).
Definition P_env_ce_example2_myent :=
  Eval vm_compute in (env P_ce_example2_myent).
Definition P_main_ce_example2_myent :=
  Eval vm_compute in (AstCommon.main P_ce_example2_myent).
Time Definition eval_ce_example2_myent :=
  Eval vm_compute in
    (wcbvEval P_env_ce_example2_myent 1000 P_main_ce_example2_myent).
Print eval_ce_example2_myent.
Goal eval_ce_example2_myent = ret valid.
  vm_compute. reflexivity. 
Qed.

Time Quote Recursively Definition p_ce_example1_myfail := vs.ce_example1_myfail.
Time Definition P_ce_example1_myfail :=
  Eval vm_compute in (program_Program p_ce_example1_myfail).
Definition P_env_ce_example1_myfail :=
  Eval vm_compute in (env P_ce_example1_myfail).
Definition P_main_ce_example1_myfail :=
  Eval vm_compute in (AstCommon.main P_ce_example1_myfail).
Time Definition eval_ce_example1_myfail :=
  Eval vm_compute in
    (wcbvEval P_env_ce_example1_myfail 400 P_main_ce_example1_myfail).
Print eval_ce_example1_myfail.

Time Quote Recursively Definition p_ce_example2_myfail := vs.ce_example2_myfail.
Time Definition P_ce_example2_myfail :=
  Eval vm_compute in (program_Program p_ce_example2_myfail).
Definition P_env_ce_example2_myfail :=
  Eval vm_compute in (env P_ce_example2_myfail).
Definition P_main_ce_example2_myfail :=
  Eval vm_compute in (AstCommon.main P_ce_example2_myfail).
Time Definition eval_ce_example2_myfail :=
  Eval vm_compute in
    (wcbvEval P_env_ce_example2_myfail 1000 P_main_ce_example2_myfail).
Print eval_ce_example1_myfail.

(**** cannot do in memory and time *****
Time Quote Recursively Definition p_ce_harder_ent := vs.ce_harder_ent.
Time Definition P_ce_harder_ent :=
  Eval vm_compute in (program_Program p_ce_harder_ent).
Definition P_env_ce_harder_ent :=
  Eval vm_compute in (env P_ce_harder_ent).
Definition P_main_ce_harder_ent :=
  Eval vm_compute in (AstCommon.main P_ce_harder_ent).
Time Definition eval_ce_harder_ent :=
  Eval vm_compute in
    (wcbvEval P_env_ce_harder_ent 5000 P_main_ce_harder_ent).
Print eval_ce_harder_ent.

Time Quote Recursively Definition p_myMain := vs.myMain.
Time Definition P_myMain :=
  Eval vm_compute in (program_Program p_myMain).
Definition P_env_myMain := env P_myMain.
Definition P_main_myMain := (AstCommon.main P_myMain).
Time Definition eval_myMain :=
  Eval vm_compute in (wcbvEval P_env_myMain 5000 P_main_myMain).
Print eval_myMain.
*************)



(***
Notation NN := (mkInd "Coq.Init.Datatypes.nat" 0).
Notation SS := (TConstruct NN 1 0).
Notation ZZ := (TConstruct NN 0 0).
Notation LL := (mkInd "Coq.Init.Datatypes.list" 0).
Notation CONS := (TConstruct LL 1 1).
Notation NIL := (TConstruct LL 0 1).
Notation VSR := (mkInd "Benchmarks.vs.VeriStar.veristar_result" 0).
Notation VSR_Val := (TConstruct VSR 0).
Notation VSR_Modl := (TConstruct VSR 1).
Notation VSR_Abrt := (TConstruct VSR 2).
Notation Lam := (TLambda).
Notation tLam := (tLambda).
Notation tPi := (tProd).
Notation tPROP := (tSort sProp).
Notation AND := (mkInd "Coq.Init.Logic.and" 0).
Notation CONJ := (TConstruct AND 0 4).
Notation TRUE := (mkInd "Coq.Init.Logic.True" 0).
Notation II := (TConstruct TRUE 0 0).
Notation EQ := (mkInd "Coq.Init.Logic.eq" 0).
Notation RFL := (TConstruct EQ 0 1).
Notation PROD := (mkInd "Coq.Init.Datatypes.prod" 0).
Notation PAIR := (TConstruct PROD 0 2).
Notation "^ x" := (nNamed x)  (at level 85).
Notation "^" := (nAnon).
Infix ":t:" := tcons  (at level 87, right associativity).
Notation "fn [| arg @ args |]" :=
  (TApp fn arg args)  (at level 90, left associativity).
Notation IND := (compile.TInd).
 ***)

Definition tstx := true.
Quote Recursively Definition cbv_tstx :=
  ltac:(let t:=(eval cbv in tstx) in exact t).
Definition ans_tstx :=
  Eval cbv in (main (program_Program cbv_tstx)).
(* [program] of the program *)
Quote Recursively Definition p_tstx := tstx.
Definition P_tstx := Eval cbv in (program_Program p_tstx).
Goal
  let env := (env P_tstx) in
  let main := (main P_tstx) in
  wcbvEval (env) 90 (main) = Ret ans_tstx.
  vm_compute. reflexivity.
Qed.

Fixpoint Plus1 (n : nat): nat :=
  match n with
    | 0 => 1
    | S p => S (Plus1 p)
  end.
Definition Plus1x := (Plus1 2).
Compute Plus1x.
Quote Recursively Definition cbv_Plus1x :=
  ltac:(let t:=(eval cbv in Plus1x) in exact t).
Print cbv_Plus1x.
Definition ans_Plus1x :=
  Eval cbv in (main (program_Program cbv_Plus1x)).
Print ans_Plus1x.
(* [program] of the program *)
Quote Recursively Definition p_Plus1x := Plus1x.
Definition P_Plus1x := Eval cbv in (program_Program p_Plus1x).
Print P_Plus1x.
Goal
  let env := (env P_Plus1x) in
  let main := (main P_Plus1x) in
  wcbvEval env 90 main = Ret ans_Plus1x.
  vm_compute. reflexivity.
Qed.

(**** very simple polymorphic match  **)
Section myplus.
  Variables (A:Type).
  Inductive myNat : Type :=
  | myZ: forall a:A, myNat.
  Definition myplus (m: myNat) : A :=
    match m with
    | myZ a => a
    end.
End myplus.
Print myplus.
Definition myplusx := (myplus (myZ true)).
Compute myplusx.
Quote Recursively Definition cbv_myplusx :=
  ltac:(let t:=(eval cbv in myplusx) in exact t).
Definition ans_myplusx :=
  Eval cbv in (main (program_Program cbv_myplusx)).
Print ans_myplusx.
(* [program] of the program *)
Quote Recursively Definition p_myplusx := myplusx.
Definition P_myplusx := Eval cbv in (program_Program p_myplusx).
Goal
  let env := (env P_myplusx) in
  let main := (main P_myplusx) in
  wcbvEval (env) 90 (main) = Ret ans_myplusx.
  vm_compute. reflexivity.
Qed.
 
(** list apprend **)
Fixpoint myapp (ls ts: list nat): list nat :=
  match ls with
  | nil => ts
  | cons b bs => cons b (myapp bs ts)
  end.
Definition myappx := (myapp (cons 0 nil) nil).
Compute myappx.
Quote Recursively Definition cbv_myappx :=
  ltac:(let t:=(eval cbv in myappx) in exact t).
Definition ans_myappx :=
  Eval cbv in (main (program_Program cbv_myappx)).
Print ans_myappx.
(* [program] of the program *)
Quote Recursively Definition p_myappx := myappx.
Definition P_myappx := Eval cbv in (program_Program p_myappx).
Goal
  let env := (env P_myappx) in
  let main := (main P_myappx) in
  wcbvEval (env) 90 (main) = Ret ans_myappx.
  vm_compute. reflexivity.
Qed.

(** list reverse **)
Fixpoint myrev (ls: list nat): list nat :=
  match ls with
  | nil => nil
  | cons b bs => (myrev bs) ++ (cons b nil)
  end.
Definition myrevx := (myrev (cons 0 nil)).
Compute myrevx.
Quote Recursively Definition cbv_myrevx :=
  ltac:(let t:=(eval cbv in myrevx) in exact t).
Definition ans_myrevx :=
  Eval cbv in (main (program_Program cbv_myrevx)).
Print ans_myrevx.
(* [program] of the program *)
Quote Recursively Definition p_myrevx := myrevx.
Definition P_myrevx := Eval cbv in (program_Program p_myrevx).
Goal
  let env := (env P_myrevx) in
  let main := (main P_myrevx) in
  wcbvEval (env) 90 (main) = Ret ans_myrevx.
  vm_compute. reflexivity.
Qed.


(*** testing eta and params ****)
Set Printing Width 80.
Quote Recursively Definition p_0 := 0.
Definition oldP_0 := Eval cbv in (main (L2d.compile.program_Program p_0)).
Print oldP_0.
Definition P_0 := Eval cbv in (main (program_Program p_0)).
Print P_0.

Quote Recursively Definition p_1 := 1.
Definition oldP_1 := Eval cbv in (main (L2d.compile.program_Program p_1)).
Print oldP_1.
Definition P_1 := Eval cbv in (main (program_Program p_1)).
Print P_1.
                                      
Quote Recursively Definition p_nil := @nil.
Definition oldP_nil := Eval cbv in (main (L2d.compile.program_Program p_nil)).
Print oldP_nil.
Definition P_nil := Eval cbv in (main (program_Program p_nil)).
Print P_nil.

Quote Recursively Definition p_nilb := (@nil bool).
Definition oldP_nilb :=
  Eval cbv in (main (L2d.compile.program_Program p_nilb)).
Print oldP_nilb.
Definition P_nilb := Eval cbv in (main (program_Program p_nilb)).
Print P_nilb.

Quote Recursively Definition p_cons := @cons.
Definition oldP_cons :=
  Eval cbv in (main (L2d.compile.program_Program p_cons)).
Print oldP_cons.
Definition P_cons := Eval cbv in (main (program_Program p_cons)).
Print P_cons.

Quote Recursively Definition p_lcons := (fun x => @cons x).
Definition P_lcons := Eval cbv in (main (program_Program p_lcons)).
Print P_lcons.

Quote Recursively Definition p_llcons := (fun x => fun y => @cons x y).
Definition P_llcons := Eval cbv in (main (program_Program p_llcons)).
Print P_llcons.

Quote Recursively Definition p_xx :=
  (fun (y:bool) => fun (z:list bool -> bool) => z (@cons bool y nil)).
Definition P_xx := Eval cbv in (main (program_Program p_xx)).
Print P_xx.

Quote Recursively Definition p_consb := (@cons bool).
Definition oldP_consb :=
  Eval cbv in (main (L2d.compile.program_Program p_consb)).
Print oldP_consb.
Definition P_consb := Eval cbv in (main (program_Program p_consb)).
Print P_consb.

Quote Recursively Definition p_consbt := (cons true).
Definition oldP_consbt :=
  Eval cbv in (main (L2d.compile.program_Program p_consbt)).
Print oldP_consbt.
Definition P_consbt := Eval cbv in (main (program_Program p_consbt)).
Print P_consbt.

Quote Recursively Definition p_underLam := (fun (x:bool) => (cons x)).
Definition P_underLam := Eval cbv in (main (program_Program p_underLam)).
Print P_underLam.


Quote Recursively Definition p_consbtbs := (cons true nil).
Definition oldP_consbtbs :=
  Eval cbv in (main (L2d.compile.program_Program p_consbtbs)).
Print oldP_consbtbs.
Definition P_consbtbs := Eval cbv in (main (program_Program p_consbtbs)).
Print P_consbtbs.



Fixpoint testEtaNA (l:nat) : nat :=
  match l with
  | 0 => 0
  | S x => S (testEtaNA x)
  end.
Quote Recursively Definition p_testEtaNAAns :=
    ltac:(let t:=(eval cbv in (testEtaNA 0)) in exact t).
Definition P_testEtaNAAns :=
  Eval cbv in (main (LambdaBoxMut.compile.program_Program p_testEtaNAAns)).
Print P_testEtaNAAns.
Quote Recursively Definition p_texNA := (testEtaNA 0).
Definition P_texNA := Eval cbv in (LambdaBoxMut.compile.program_Program p_texNA).
Print P_texNA.
Goal
  let envx := @env Term P_texNA in
  let mainx := main P_texNA in
  wcbvEval envx 90 mainx = Ret P_testEtaNAAns.
Proof.
  vm_compute. reflexivity.
Qed.

Goal
  let envx := env P_texNA in
  let mainx := main P_texNA in
  WcbvEval envx mainx P_testEtaNAAns.
Proof.
  intros. unfold envx, mainx, P_testEtaNAAns. 
  unfold P_texNA at 2. unfold main.
  eapply wAppFix.
  - eapply wConst.
    + cbn. reflexivity.
    + eapply wFix.
  - unfold dnthBody. reflexivity.
  - unfold pre_whFixStep, dlength, list_to_zero, List.fold_left.
    unfold instantiate. unfold nat_compare. unfold mkApp.
    eapply wAppLam.
    + eapply wLam.
    + eapply wConstruct. eapply wNil.
    + unfold whBetaStep, instantiate, nat_compare, mkApp.
      eapply wCase.
      * eapply wConstruct. eapply wNil.
      * cbn. reflexivity.
      * unfold whCaseStep, bnth. reflexivity.
      * unfold mkApp. eapply wConstruct. eapply wNil.
Qed.

  
Fixpoint testEta (l:list bool) : list bool :=   (** copy **)
  match l with
  | nil => nil
  | x :: xs => x :: testEta xs
  end.
Quote Recursively Definition p_testEtaAns :=
    ltac:(let t:=(eval cbv in (testEta (true::nil))) in exact t).
Definition P_testEtaAns :=
  Eval cbv in (main (LambdaBoxMut.compile.program_Program p_testEtaAns)).
Print P_testEtaAns.
Quote Recursively Definition p_tex := (testEta (true::nil)).
Definition P_tex := Eval cbv in (LambdaBoxMut.compile.program_Program p_tex).
Print P_tex.

Goal
  let envx := env P_tex in
  let mainx := main P_tex in
  wcbvEval envx 90 mainx = Ret P_testEtaAns.
Proof.
  vm_compute. reflexivity.
Qed.
            
        
Definition testEta1 (bs:list nat) cs := bs ++ cs.
Definition testEta1x := testEta1 (0::nil) nil.
Quote Recursively Definition p_testEta1Ans :=
    ltac:(let t:=(eval cbv in testEta1x) in exact t).
Definition P_testEta1Ans := Eval cbv in (main (program_Program p_testEta1Ans)).
Print P_testEta1Ans.
Quote Recursively Definition p_tex1 := testEta1x.
Definition P_tex1:= Eval cbv in (program_Program p_tex1).
Print P_tex1.

Goal
  let envx := env P_tex1 in
  let mainx := main P_tex1 in
  wcbvEval envx 90 mainx = Ret P_testEta1Ans.
  vm_compute.  reflexivity.
Qed.


Definition testEta2 := Eval cbv in  (1 :: nil).
Quote Recursively Definition p_testEta2Ans :=
  ltac:(let t:=(eval cbv in testEta2) in exact t).
Definition P_testEta2Ans := Eval cbv in (main (program_Program p_testEta2Ans)).
Quote Recursively Definition p_testEta2 := testEta2.
Definition P_testEta2 := Eval cbv in (program_Program p_testEta2).
Goal
  let envx := env P_testEta2 in
  let mainx := main P_testEta2 in
  wcbvEval envx 90 mainx = Ret P_testEta2Ans.
  vm_compute. reflexivity. 
Qed.


(** Abhishek's example of looping: in L2 we don't test the guard **)
Require Import Arith.
Axiom AAax: Acc gt 0.
Fixpoint loop (n:nat) (x:nat) (a:Acc gt n) {struct a} : nat :=
  match n with
  | _ => @loop (S n) x (Acc_inv a (S n) (gt_Sn_n n))
  end.
Fixpoint pool (n:nat) (a:Acc gt n) {struct a} : nat -> nat :=
  match n with
  | _ => @pool (S n) (Acc_inv a (S n) (gt_Sn_n n))
  end.
Definition loop02 := @loop O 2.
Eval vm_compute in loop02.    (** Coq does not loop **)
Recursive Extraction loop02.
Definition pool0AAax := @pool O AAax.
Eval vm_compute in pool0AAax.    (** Coq does not loop **)
Recursive Extraction pool0AAax.

Definition loop02AAax := @loop O 2 AAax.
Eval vm_compute in loop02AAax.
Recursive Extraction loop02AAax.
Definition pool0AAax2 := @pool O AAax 2.
Eval vm_compute in pool0AAax2.
Recursive Extraction pool0AAax2.

(***********
Inductive mlt (n:nat) : nat -> Prop := mlt_n: mlt n (S n).
Inductive Acc (y: nat) : Prop :=
  Acc_intro : (forall x: nat, mlt y x -> Acc x) -> Acc y.
Definition Acc_inv: forall (x:nat) (H:Acc x) (y:nat), mlt x y -> Acc y.
  intros. destruct H. apply H. apply H0.
  Defined.
Fixpoint loop (n:nat) (a:Acc n) {struct a} : nat :=
  match n with
    | _ => @loop (S n) (@Acc_inv _ a (S n) (mlt_n n))
  end.
Axiom Acc0Ax : Acc 0.
Definition loop0 := (@loop O Acc0Ax).
Eval vm_compute in loop0.   (** Coq does not loop **)

Quote Recursively Definition p_loop0 := loop0.
Definition P_loop0 := Eval vm_compute in (program_Program p_loop0).
Definition P_env := Eval vm_compute in (env P_loop0).
Definition P_main := Eval vm_compute in (main P_loop0).
(** wcbvEval raises exception "out of time": non-terminating **)
Eval vm_compute in wcbvEval P_env 1000 P_main.
*****************************)                      

Inductive P0: Prop := p0.
Inductive P1: Prop := p1.
Notation PP0 := (mkInd "P0" 0).
Notation pp0 := (TConstruct PP0 0 0).
Notation PP1 := (mkInd "P1" 0).
Notation pp1 := (TConstruct PP1 0 0).


Quote Recursively Definition p_and_rect := and_rect.
Print p_and_rect.
Eval cbv in (program_Program p_and_rect).

Definition and_rect_x :=
  (and_rect (fun (a:2=2) (b:True) => conj b a) (conj (eq_refl 2) I)).
Quote Recursively Definition p_and_rect_x := and_rect_x.
Definition P_and_rect_x := Eval cbv in (program_Program p_and_rect_x).
Print P_and_rect_x.
Quote Recursively Definition cbv_and_rect_x :=
  ltac:(let t:=(eval cbv in and_rect_x) in exact t).
Definition ans_and_rect_x :=
  Eval cbv in (main (program_Program cbv_and_rect_x)).
Definition envx := env P_and_rect_x.
Definition mainx := main P_and_rect_x.
Goal
  wcbvEval envx 90 mainx = Ret ans_and_rect_x.
  vm_compute. (******** fails HERE because of TProof
  reflexivity.
Qed.
               *****************)
Abort.

Definition and_rectx :=
  and_rect (fun (x0:P0) (x1:P1) => pair (conj x1 x0) 0) (conj p0 p1).
Eval cbv in and_rectx.
Quote Recursively Definition ans_and_rectx := (* [program] of Coq's answer *)
  ltac:(let t:=(eval cbv in and_rectx) in exact t).
Definition Ans_and_rectx :=
  Eval cbv in (wcbvEval (env (program_Program ans_and_rectx)) 1000
                        (main (program_Program ans_and_rectx))).
Print Ans_and_rectx.
Quote Recursively Definition p_and_rectx := and_rectx.
Print p_and_rectx.
Definition P_and_rectx := Eval cbv in (program_Program p_and_rectx).
Print P_and_rectx.
Definition P_envx := env P_and_rectx.
Definition P_mainx := main P_and_rectx.
Goal wcbvEval P_envx 100 P_mainx = Ans_and_rectx.
  vm_compute. reflexivity. 
Qed.

Definition my_and_rect := 
  fun (A B : Prop) (P : Type) (f : A -> B -> P) (a : A /\ B) =>
    match a with conj x x0 => f x x0 end.
Quote Recursively Definition p_my_and_rect := my_and_rect.
Print p_my_and_rect.
Eval cbv in (program_Program p_my_and_rect).
Quote Recursively Definition p_my_and_rectx :=
  (and_rect (fun (x0:P0) (x1:P1) => pair (conj x1 x0) 0) (conj p0 p1)).
Definition P_my_and_rectx := Eval cbv in (program_Program p_and_rectx).
Definition P_my_envx := env P_my_and_rectx.
Definition P_my_mainx := main P_my_and_rectx.
Eval cbv in (wcbvEval P_my_envx 100 P_my_mainx).


Definition my_and_rect_x :=
  (my_and_rect (fun (a:2=2) (b:True) => conj b a) (conj (eq_refl 2) I)).
Quote Recursively Definition p_my_and_rect_x := my_and_rect_x.
Definition P_my_and_rect_x := Eval cbv in (program_Program p_my_and_rect_x).
Quote Recursively Definition cbv_my_and_rect_x :=
  ltac:(let t:=(eval cbv in my_and_rect_x) in exact t).
Definition ans_my_and_rect_x :=
  Eval cbv in (main (program_Program cbv_my_and_rect_x)).
Definition my_envx := env P_my_and_rect_x.
Definition my_mainx := main P_my_and_rect_x.
Eval cbv in (wcbvEval my_envx 30 my_mainx).

(** Fibonacci **)
Fixpoint slowFib (n:nat) : nat :=
  match n with
    | 0 => 0
    | S m => match m with
               | 0 => 1
               | S p => slowFib p + slowFib m
             end
  end.
Definition slowFib3 := (slowFib 3).
Compute slowFib3.
Quote Recursively Definition cbv_slowFib3 :=
  ltac:(let t:=(eval cbv in slowFib3) in exact t).
Eval cbv in (program_Program cbv_slowFib3).
Definition ans_slowFib3 :=
  Eval cbv in (main (program_Program cbv_slowFib3)).
Print ans_slowFib3.
(* [program] of the program *)
Quote Recursively Definition p_slowFib3 := slowFib3.
Print p_slowFib3.
Definition P_slowFib3 := Eval cbv in (program_Program p_slowFib3).
Print P_slowFib3.
Goal
  let env := (env P_slowFib3) in
  let main := (main P_slowFib3) in
  wcbvEval env 30 main = Ret ans_slowFib3.
  vm_compute. reflexivity.
Qed.

Definition div : forall x y, y > 0 -> { z | z*y <= x < (S z)*y }.
Proof.
  induction x as [x Hrec] using (well_founded_induction lt_wf).
  intros y Hy.
  case_eq (y <=? x); intros.  (* do we have y≤x or x<y ? *)
  (* first case: y≤x *)
  - pose proof (leb_complete _ _ H) as j1.
    assert (Hxy : x-y < x) by omega.
    destruct (Hrec (x-y) Hxy y Hy) as [z Hz]. (* ie: let z = div (x-y) y *)
    exists (S z); simpl in *; omega. (* ie: z+1 fits as (div x y) *)
  (* second case: x<y *)
  - pose proof (leb_complete_conv _ _ H).
    exists 0; omega.
Defined.
Print div.
Extraction div.

Definition funnyDiv: forall x y, { z | z*(S y) <= x < (S z)*(S y) }.
Proof.
  induction x as [x Hrec] using (well_founded_induction lt_wf).
  intros y.
  case_eq (S y <=? x); intros.
  - pose proof (leb_complete _ _ H) as j1.
    assert (Hxy : x-(S y) < x) by omega.
    destruct (Hrec (x- S y) Hxy y) as [z Hz]. (* ie: let z = div (x-y) y *)
    exists (S z); simpl in *; omega. (* ie: z+1 fits as (div x y) *)
  - pose proof (leb_complete_conv _ _ H).
    exists 0. cbn. omega.
Defined.
Print funnyDiv.
Extraction funnyDiv.

  
Function copy (n : nat) {wf lt n} : nat :=
  match n with
    | 0 => 0
    | S p => S (copy p)
  end.
Admitted.
Print Assumptions copy.

Compute (copy 2).
Print copy_terminate.
Check forall n : nat,
       {v : nat |
       exists p : nat,
         forall k : nat,
         p < k -> forall def : nat -> nat, Recdef.iter (nat -> nat) k copy_F def n = v}.
(* Transparent copy_terminate. *)
(****
- intros. constructor. 
- apply lt_wf.
Defined.  
Print copy_tcc.

Print copy.
Definition x := 2.
Definition copyx := copy x.
Set Printing Width 200.
Compute copyx.
Print copy_terminate.   (* Opaque, but printable *)
Check (forall n:nat, {v:nat | exists p:nat, forall k:nat, p < k -> forall def:nat -> nat, Recdef.iter (nat -> nat) k copy_F def n = v}:Set).

Definition cp_term :=    (* Transparent *)
  (fun h:(forall n p:nat, n = S p -> p < S p) /\ well_founded lt =>
 let H := h:(forall n p:nat, n = S p -> p < S p) /\ well_founded lt in
 (fun _TmpHyp:(forall n p:nat, n = S p -> p < S p) /\ well_founded lt =>
  and_rec
    (fun (H0:forall n p:nat, n = S p -> p < S p) (H1:well_founded lt) (n:nat) =>
     let Acc_n := (let wf_R := H1:well_founded lt in wf_R n):Acc lt n in
     (fix hrec (n0:nat) (Acc_n0:Acc lt n0) {struct Acc_n0}:{v:nat | exists p:nat, forall k:nat, p < k -> forall def:nat -> nat, Recdef.iter (nat -> nat) k copy_F def n0 = v} :=
        match n0 as n1 return (n0 = n1 -> {v:nat | exists p:nat, forall k:nat, p < k -> forall def:nat -> nat, Recdef.iter (nat -> nat) k copy_F def n1 = v}) with
        | 0 =>
            fun _:n0 = 0 =>
            exist (fun v:nat => exists p:nat, forall k:nat, p < k -> forall def:nat -> nat, Recdef.iter (nat -> nat) k copy_F def 0 = v) 0
              (ex_intro (fun p:nat => forall k:nat, p < k -> forall def:nat -> nat, Recdef.iter (nat -> nat) k copy_F def 0 = 0) 1
                 (fun k:nat =>
                  match k as n1 return (1 < n1 -> forall def:nat -> nat, Recdef.iter (nat -> nat) n1 copy_F def 0 = 0) with
                  | 0 => fun h0:1 < 0 => False_ind (forall def:nat -> nat, Recdef.iter (nat -> nat) 0 copy_F def 0 = 0) (Nat.nlt_0_r 1 h0)
                  | S k0 => fun (_:1 < S k0) (def:nat -> nat) => eq_refl
                  end))
        | S p =>
            fun teq:n0 = S p =>
            sig_rec
              (fun _:{v:nat | exists p0:nat, forall k:nat, p0 < k -> forall def:nat -> nat, Recdef.iter (nat -> nat) k copy_F def p = v} =>
               {v:nat | exists p0:nat, forall k:nat, p0 < k -> forall def:nat -> nat, Recdef.iter (nat -> nat) k copy_F def (S p) = v})
              (fun (rec_res:nat) (p2:exists p0:nat, forall k:nat, p0 < k -> forall def:nat -> nat, Recdef.iter (nat -> nat) k copy_F def p = rec_res) =>
               exist (fun v:nat => exists p0:nat, forall k:nat, p0 < k -> forall def:nat -> nat, Recdef.iter (nat -> nat) k copy_F def (S p) = v) (S rec_res)
                 (ex_ind
                    (fun (x:nat) (H2:forall k:nat, x < k -> forall def:nat -> nat, Recdef.iter (nat -> nat) k copy_F def p = rec_res) =>
                     max_type_ind 0 x (fun _:max_type 0 x => exists p0:nat, forall k:nat, p0 < k -> forall def:nat -> nat, Recdef.iter (nat -> nat) k copy_F def (S p) = S rec_res)
                       (fun (v:nat) (_:0 <= v) (l0:x <= v) =>
                        ex_intro (fun p0:nat => forall k:nat, p0 < k -> forall def:nat -> nat, Recdef.iter (nat -> nat) k copy_F def (S p) = S rec_res) (S v)
                          (fun k:nat =>
                           match k as n1 return (S v < n1 -> forall def:nat -> nat, Recdef.iter (nat -> nat) n1 copy_F def (S p) = S rec_res) with
                           | 0 => fun h0:S v < 0 => False_ind (forall def:nat -> nat, Recdef.iter (nat -> nat) 0 copy_F def (S p) = S rec_res) (Nat.nlt_0_r (S v) h0)
                           | S k0 => fun (h':S v < S k0) (def:nat -> nat) => eq_ind_r (fun n1:nat => S n1 = S rec_res) eq_refl (H2 k0 (Nat.le_lt_trans x v k0 l0 (Nat.succ_lt_mono v k0 h')) def)
                           end)) (max 0 x)) p2)) (hrec p (Acc_inv Acc_n0 (eq_ind_r (fun n1:nat => p < n1) (H0 n0 p teq) teq)))
        end eq_refl) n Acc_n) _TmpHyp) H) copy_tcc.

Compute (let (x, _) := cp_term 2 in x).

Time Quote Recursively Definition pcopyx := copyx.
Time Definition Pcopyx :=
  Eval vm_compute in (LambdaBoxMut.compile.program_Program pcopyx).
Time Definition Penv_copyx := env Pcopyx.
Time Definition Pmain_copyx := main Pcopyx.
Time Definition ans_copyx :=
 Eval vm_compute in (wcbvEval Penv_copyx 1000 Pmain_copyx).
Print ans_copyx.
*****************)

Function Gcd (a b:nat) {wf lt a}:nat :=
match a with
 | O => b 
 | S k => Gcd (b mod S k) (S k)
end.
Proof.
  - intros m n k Heq. subst. apply Nat.mod_upper_bound.
    intros h. discriminate.
  - exact lt_wf.
Defined.
Print Gcd_tcc.
Definition Gcdx := (Gcd 4 2).
Eval cbv in Gcdx.
(***** runs out of memory here  ****
Time Quote Recursively Definition pGcdx := Gcdx.
Time Definition PGcdx :=
  Eval vm_compute in (LambdaBoxMut.compile.program_Program pGcdx).
Time Definition Penv_Gcdx := env PGcdx.
Time Definition Pmain_Gcdx := main PGcdx.
Time Definition ans_Gcdx :=
 Eval vm_compute in (wcbvEval Penv_Gcdx 1000 Pmain_Gcdx).
Print ans_Gcdx.
***)



(***
(** Andrew's example **)
Function sqrt' (n x0 x diff: Z) {measure Z.to_nat diff}:Z :=
  (if diff =? 0 then x
   else let y := Z.div2 (x + Z.div n x)
        in if y =? x0 then Z.min x0 x
           else sqrt' n x y (y-x0))%Z.
Proof.
Admitted.

Quote Recursively Definition psqrt := sqrt'.
Definition Psqrt := Eval cbv in (program_Program psqrt).
****)

(** vector addition **)
Require Coq.Vectors.Vector.
Print Fin.t.
Print Vector.t.

Definition vplus (n:nat) :
  Vector.t nat n -> Vector.t nat n -> Vector.t nat n := (Vector.map2 plus).
Definition v01:Vector.t nat 2 :=
  (Vector.cons nat 0 1 (Vector.cons nat 1 0 (Vector.nil nat))).
Definition v23:Vector.t nat 2 :=
  (Vector.cons nat 2 1 (Vector.cons nat 3 0 (Vector.nil nat))).
Definition vplus0123 := (vplus v01 v23).
Quote Recursively Definition cbv_vplus0123 := (* [program] of Coq's answer *)
  ltac:(let t:=(eval cbv in (vplus0123)) in exact t).
Print cbv_vplus0123.
(* [Term] of Coq's answer *)
Definition ans_vplus0123 := Eval cbv in (main (program_Program cbv_vplus0123)).
(* [program] of the program *)
Quote Recursively Definition p_vplus0123 := vplus0123.
Print p_vplus0123.
Definition P_vplus0123 := Eval cbv in (program_Program p_vplus0123).
Print P_vplus0123.
Goal
  let env := (env P_vplus0123) in
  let main := (main P_vplus0123) in
  wcbvEval (env) 100 (main) = Ret ans_vplus0123.
  vm_compute. reflexivity.
Qed.

Inductive pack (A:Prop):Prop := Pack: A -> A -> A -> A -> pack A.
Axiom packax: forall A, pack A -> pack A.
Definition pack_nat (A:Prop) (a:pack A):nat :=
  match packax a with
    | Pack b1 b2 b3 b4 => 0
  end.
Quote Recursively Definition p_pack_nat := (pack_nat (Pack I I I I)).
Check p_pack_nat.
Definition P_pack_nat := Eval cbv in (program_Program p_pack_nat).
Print P_pack_nat.

Inductive xxxx:Prop :=
| xxxxl: forall n:nat, n = 0 -> xxxx
| xxxxr: forall n:nat, n = 1 -> xxxx.
Axiom Xxxx:xxxx.
Definition yyyy (f:xxxx) := match f with xxxxl q => f | xxxxr q => f end.
Definition yyyyX := (yyyy Xxxx).
Quote Recursively Definition cbv_yyyyX := (* [program] of Coq's answer *)
  ltac:(let t:=(eval cbv in (yyyyX)) in exact t).
Print cbv_yyyyX.
(* [Term] of Coq's answer *)
Definition ans_yyyyX := Eval cbv in (main (program_Program cbv_yyyyX)).
Print ans_yyyyX.
(* [program] of the program *)
Quote Recursively Definition p_yyyyX := yyyyX.
Print p_yyyyX.
Definition P_yyyyX := Eval cbv in (program_Program p_yyyyX).
Print P_yyyyX.
(*********** what is the problem? 
** axiom inside proof, but proofs haven't been stripped yet at LambdaBoxMut
 ***********
Goal WcbvEval xxxx_env xxxx_main ans_yyyyX.
Proof.
  unfold main. eapply wProof. eapply wConst.
  - unfold env. cbn. reflexivity.
  - eapply wProof. eapply wAppLam.  
    + eapply wConst. cbn. reflexivity. eapply wProof. eapply wLam.
****************)
Goal
  let xxxx_env := (env P_yyyyX) in
  let xxxx_main := (main P_yyyyX) in
  wcbvEval xxxx_env 10 xxxx_main = Ret ans_yyyyX.
  vm_compute.
  (**********
reflexivity.
Qed.
   *************)
Abort.

(** mutual recursion **)
Set Implicit Arguments.
Inductive tree (A:Set):Set :=
  node:A -> forest A -> tree A
with forest (A:Set):Set :=
     | leaf:A -> forest A
     | fcons:tree A -> forest A -> forest A.

Fixpoint tree_size (t:tree bool):nat :=
  match t with
    | node a f => S (forest_size f)
  end
with forest_size (f:forest bool):nat :=
       match f with
         | leaf b => 1
         | fcons t f1 => (tree_size t + forest_size f1)
       end.

Definition arden: forest bool :=
  fcons (node true (fcons (node true (leaf false)) (leaf true)))
        (fcons (node true (fcons (node true (leaf false)) (leaf true)))
               (leaf false)).
Definition arden_size := (forest_size arden).
Quote Recursively Definition cbv_arden_size :=
  ltac:(let t:=(eval cbv in arden_size) in exact t).
Definition ans_arden_size :=
  Eval cbv in (main (program_Program cbv_arden_size)).
(* [program] of the program *)
Quote Recursively Definition p_arden_size := arden_size.
Print p_arden_size.
Definition P_arden_size := Eval cbv in (program_Program p_arden_size).
Print P_arden_size.
Goal
  let env := (env P_arden_size) in
  let main := (main P_arden_size) in
  wcbvEval (env) 100 (main) = Ret ans_arden_size.
  vm_compute. reflexivity.
Qed.

(** Ackermann **)
Fixpoint ackn (Ack:nat -> nat) (m:nat) {struct m}:nat :=
  match m with
  | 0 => Ack 1
  | S q => Ack (ackn Ack q)
  end.
Fixpoint Ack (n:nat) {struct n}:nat -> nat :=
  match n with
    | 0 => S
    | S p => ackn (Ack p)
  end.
Quote Recursively Definition p_Ack := Ack.
Print p_Ack.
Definition P_Ack := Eval cbv in (program_Program p_Ack).
Print P_Ack.
Time Compute Ack 3 7.

Fixpoint ACK (n:nat) {struct n}:nat -> nat :=
  match n with
    | 0 => S
    | S p => let fix ackn (m:nat) {struct m} :=
                 match m with
                   | 0 => ACK p 1
                   | S q => ACK p (ackn q)
                 end
             in ackn
  end.
Quote Recursively Definition p_ACK := ACK.
Print p_ACK.
Definition P_ACK := Eval cbv in (program_Program p_ACK).
Print P_ACK.
Compute ACK 3 7.


Fixpoint ack (n m:nat) {struct n}:nat :=
  match n with
    | 0 => S m
    | S p => let fix ackn (m:nat) {struct m} :=
                 match m with
                   | 0 => ack p 1
                   | S q => ack p (ackn q)
                 end
             in ackn m
  end.
Compute ack 3 7.
Definition ack35 := (ack 3 5).
Quote Recursively Definition cbv_ack35 :=
  ltac:(let t:=(eval cbv in ack35) in exact t).
Print cbv_ack35.
Definition ans_ack35 :=
  Eval cbv in (main (program_Program cbv_ack35)).
Print ans_ack35.
(* [program] of the program *)
Quote Recursively Definition p_ack35 := ack35.
Print p_ack35.
Definition P_ack35 := Eval cbv in (program_Program p_ack35).
Print P_ack35.
Goal
  let env := (env P_ack35) in
  let main := (main P_ack35) in
  wcbvEval (env) 2000 (main) = Ret ans_ack35.
  vm_compute. reflexivity.
Qed.

(** SASL tautology function: variable arity **)
Fixpoint tautArg (n:nat):Type :=
  match n with
    | 0 => bool
    | S n => bool -> tautArg n
  end.
Fixpoint taut (n:nat):tautArg n -> bool :=
  match n with
    | 0 => (fun x => x)
    | S n => fun x => taut n (x true) && taut n (x false)
  end.
(* Pierce *)
Definition pierce := taut 2 (fun x y => implb (implb (implb x y) x) x).
Quote Recursively Definition cbv_pierce :=
  ltac:(let t:=(eval cbv in pierce) in exact t).
Print cbv_pierce.
Definition ans_pierce :=
  Eval cbv in (main (program_Program cbv_pierce)).
Print ans_pierce.
(* [program] of the program *)
Quote Recursively Definition p_pierce := pierce.
Print p_pierce.
Definition P_pierce := Eval cbv in (program_Program p_pierce).
Print P_pierce.
Goal
  let env := (env P_pierce) in
  let main := (main P_pierce) in
  wcbvEval (env) 2000 (main) = Ret ans_pierce.
  vm_compute. reflexivity.
Qed.
(* S combinator *)
Definition Scomb := taut 3
         (fun x y z => implb (implb x (implb y z))
                             (implb (implb x y) (implb x z))).
Quote Recursively Definition cbv_Scomb :=
  ltac:(let t:=(eval cbv in Scomb) in exact t).
Print cbv_Scomb.
Definition ans_Scomb :=
  Eval cbv in (main (program_Program cbv_Scomb)).
Print ans_Scomb.
(* [program] of the program *)
Quote Recursively Definition p_Scomb := Scomb.
Print p_Scomb.
Definition P_Scomb := Eval cbv in (program_Program p_Scomb).
Print P_Scomb.
Goal
  let env := (env P_Scomb) in
  let main := (main P_Scomb) in
  wcbvEval (env) 2000 (main) = Ret ans_pierce.
  vm_compute. reflexivity.
Qed.

Inductive uuyy: Set := uu | yy.
Inductive wwzz: Set := ww (_:uuyy)| zz (_:nat) (_:uuyy) (_:bool).
Definition Foo:nat -> bool -> wwzz -> wwzz := 
  fun (n:nat) (b:bool) (x:wwzz) =>
    match n,x,b with
      | 0, _, true => ww uu
      | 0, _, false => ww yy
      | S m, ww x, b => zz m x b
      | S m, zz n x c, b => zz m x b
    end.
Definition Foo0ty := (Foo 0 true (ww uu)).
Quote Recursively Definition cbv_Foo0ty :=
  ltac:(let t:=(eval cbv in Foo0ty) in exact t).
Definition ans_Foo0ty :=
  Eval cbv in (main (program_Program cbv_Foo0ty)).
(* [program] of the program *)
Quote Recursively Definition p_Foo0ty := Foo0ty.
Definition P_Foo0ty := Eval cbv in (program_Program p_Foo0ty).
Goal
  let env := (env P_Foo0ty) in
  let main := (main P_Foo0ty) in
  wcbvEval (env) 30 (main) = Ret ans_Foo0ty.
  vm_compute. reflexivity.
Qed.


(* fast Fib *)
Fixpoint fibrec (n:nat) (fs:nat * nat) {struct n}:nat :=
  match n with
    | 0 => fst fs
    | (S n) => fibrec n (pair ((fst fs) + (snd fs)) (fst fs))
  end.
Definition fib:nat -> nat := fun n => fibrec n (pair 0 1).
Definition fib9 := fib 9.
Quote Recursively Definition cbv_fib9 :=
  ltac:(let t:=(eval cbv in fib9) in exact t).
Definition ans_fib9 :=
  Eval cbv in (main (program_Program cbv_fib9)).
(* [program] of the program *)
Quote Recursively Definition p_fib9 := fib9.
Definition P_fib9 := Eval cbv in (program_Program p_fib9).
Goal
  let env := (env P_fib9) in
  let main := (main P_fib9) in
  wcbvEval (env) 1000 (main) = Ret ans_fib9.
  vm_compute. reflexivity.
Qed.

(** Heterogenous datatypes, a la Matthes **)
Inductive PList:Set->Type:=  (* powerlists *)
| zero:forall A:Set, A -> PList A
| succ:forall A:Set, PList (A * A)%type -> PList A.

Definition myPList : PList nat := (succ (zero (0,1))).
(********
Definition myPList : PList nat :=
  succ (succ (succ (zero (((1,2),(3,4)),((5,6),(7,8)))))).
 **********)

Fixpoint unzip (A:Set) (l:list (A*A)) {struct l}:list A :=
  match l return list A with
    | nil => nil
    | cons (a1,a2) l' => cons a1 (cons a2 (unzip l'))
  end.
Fixpoint PListToList (A:Set) (l:PList A) {struct l}:list A :=
  match l in PList A return list A with
    | zero a => cons a (nil )
    | succ l' => unzip (PListToList l')
  end.

Eval compute in PListToList myPList.

Set printing width 150.
Fixpoint gen_sumPList (A:Set) (l:PList A) {struct l}:(A->nat)->nat :=
  match l in PList A return (A->nat)->nat with
    | zero a => fun f => f a
    | succ l' =>
      fun f => gen_sumPList l' (fun a => let (a1,a2) := a in f a1 + f a2)
  end.
Definition sumPList l := gen_sumPList l (fun x => x).
Definition sumPL_myPL := (sumPList myPList).
Quote Recursively Definition cbv_sumPL_myPL :=
  ltac:(let t:=(eval cbv in sumPL_myPL) in exact t).
Definition ans_sumPL_myPL :=
  Eval cbv in (main (program_Program cbv_sumPL_myPL)).
(* [program] of the program *)
Quote Recursively Definition p_sumPL_myPL := sumPL_myPL.
Definition P_sumPL_myPL := Eval cbv in (program_Program p_sumPL_myPL).
Goal
  let env := (env P_sumPL_myPL) in
  let main := (main P_sumPL_myPL) in
  wcbvEval (env) 1000 (main) = Ret ans_sumPL_myPL.
  vm_compute. reflexivity.
Qed.

Set Implicit Arguments.
Section List.
Variables X Y:Type.
Variable f:X -> Y -> Y.
Fixpoint fold (y:Y) (xs:list X):Y :=
  match xs with
    | nil => y
    | cons x xr => fold (f x y) xr
  end.
End List.
Inductive Tree := T:list Tree -> Tree.
Fixpoint size (t:Tree):nat :=
  match t with
    | T ts => S (fold (fun t a => size t + a) 0 ts)
  end.
Definition myTree := (T (cons (T (unit (T nil)))
                              (cons (T (unit (T nil))) nil))).
Eval cbv in size myTree.
Definition size_myTree := size myTree.
Quote Recursively Definition cbv_size_myTree :=
  ltac:(let t:=(eval cbv in size_myTree) in exact t).
Definition ans_size_myTree :=
  Eval cbv in (main (program_Program cbv_size_myTree)).
(* [program] of the program *)
Quote Recursively Definition p_size_myTree := size_myTree.
Definition P_size_myTree := Eval cbv in (program_Program p_size_myTree).
Goal
  let env := (env P_size_myTree) in
  let main := (main P_size_myTree) in
  wcbvEval (env) 1000 (main) = Ret ans_size_myTree.
  vm_compute. reflexivity.
Qed.

Require Import Benchmarks.vs.
Print Assumptions main.

(*** Exc: contains an axiom which is a proof, not stripped yet ******
Time Quote Recursively Definition p_ce_example_myent := vs.ce_example_myent.
Time Definition P_ce_example_myent :=
  Eval vm_compute in (program_Program p_ce_example_myent).
Definition P_env_ce_example_myent := env P_ce_example_myent.
Definition P_main_ce_example_myent := AstCommon.main P_ce_example_myent.
Time Definition eval_ce_example_myent :=
  Eval vm_compute in
    (wcbvEval P_env_ce_example_myent 500 P_main_ce_example_myent).
Set Printing Width 100.
Print eval_ce_example_myent.
**********************)

(********************
Time Quote Recursively Definition p_myMain := vs.myMain.
Time Definition P_myMain :=
  Eval vm_compute in (LambdaBoxMut.compile.program_Program p_myMain).
Definition P_env_myMain := env P_myMain.
Definition P_main_myMain := AstCommon.main P_myMain.
Time Definition eval_myMain :=
  Eval vm_compute in (wcbvEval P_env_myMain 7000 P_main_myMain).
Set Printing Width 100.
Print eval_myMain.
************)

(********************
Print Assumptions vs.main.
Time Quote Recursively Definition p_ce_example_ent := vs.ce_example_ent.
Time Definition P_ce_example_ent :=
  Eval vm_compute in (program_Program p_ce_example_ent).
Time Definition P_env_ce_example_ent := env P_ce_example_ent.
Time Definition P_main_ce_example_ent := AstCommon.main P_ce_example_ent.
Time Definition eval_ce_example_ent :=
  Eval vm_compute in (wcbvEval P_env_ce_example_ent 1000 P_main_ce_example_ent).
Print eval_ce_example_ent.
**********************)

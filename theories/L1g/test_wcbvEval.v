
Require Import Coq.Arith.Compare_dec.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Arith.Peano_dec.
Require Import Recdef.
Require Import Coq.Lists.List.
Require Import Coq.Lists.ListSet.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Bool.Bool.
Require Import Coq.omega.Omega.
Require Import Template.Template.
Require Import Common.Common.
Require Import L1g.compile.
Require Import L1g.term.
Require Import L1g.wcbvEval.
Local Open Scope string_scope.
Local Open Scope bool.
Local Open Scope list.
Set Implicit Arguments.
Set Template Cast Propositions.

(*** raises exception *****
Require Import Benchmarks.vs.
Time Quote Recursively Definition p_ce_example_myent := vs.ce_example_myent.
Time Definition P_ce_example_myent :=
  Eval vm_compute in (program_Program p_ce_example_myent).
Definition P_env_ce_example_myent := env P_ce_example_myent.
Definition P_main_ce_example_myent := AstCommon.main P_ce_example_myent.
Time Definition eval_ce_example_myent :=
  Eval vm_compute in
    (wcbvEval P_env_ce_example_myent 4000 P_main_ce_example_myent).
Print eval_ce_example_myent.
**********************)


Set Printing Width 60.
Print and_rect.
Quote Recursively Definition p_and_rect := and_rect.
Print p_and_rect.

Set Template Cast Propositions.
Set Printing Width 80.
Set Printing Depth 1000.


(** example from Coq club 
"Question about the formal definition of the guard condition"
Here we check the unrolling guard
**)
Fixpoint diverge (n : nat) := let x := diverge n in 0.  (* well-typed *)
Definition diverge0 : nat := diverge 0.
Eval cbn in diverge0.  (* converges *)
(* Eval cbv in diverge0.   DIVERGES! *)
Quote Recursively Definition p_diverge0 := diverge0.
Print p_diverge0.
Definition P_diverge0 := Eval vm_compute in (program_Program p_diverge0).
Definition P_div_env := Eval vm_compute in (env P_diverge0).
Definition P_div_main := Eval vm_compute in (main P_diverge0).
Eval vm_compute in wcbvEval P_div_env 1000 P_div_main.  (* also diverges! *)
Goal
  WcbvEval P_div_env P_div_main prop.
Proof.
  unfold P_div_main. eapply wConst.
  - cbn. reflexivity.
  - eapply wAppFix.
    + eapply wConst.
      * cbn. reflexivity.
      * eapply wFix.
Abort.


Notation NN := (mkInd "Coq.Init.Datatypes.nat" 0).
Notation NNN := (TInd NN).
Notation SS := (TConstruct NN 1 1).
Notation ZZ := (TConstruct NN 0 0).
Notation LL := (mkInd "Coq.Init.Datatypes.list" 0).
Notation LLL := (TInd LL).
Notation CONS := (TConstruct LL 1 3).
Notation NIL := (TConstruct LL 0 1).
Notation Lam := (TLambda).
Notation tLam := (tLambda).
Notation Pi := (TProd).
Notation tPi := (tProd).
Notation PROP := (TSort sProp).
Notation tPROP := (tSort sProp).
Notation AND := (mkInd "Coq.Init.Logic.and" 0).
Notation CONJ := (TConstruct AND 0 4).
Notation TRUE := (mkInd "Coq.Init.Logic.True" 0).
Notation II := (TConstruct TRUE 0 0).
Notation EQ := (mkInd "Coq.Init.Logic.eq" 0).
Notation RFL := (TConstruct EQ 0 2).
Notation PROD := (mkInd "Coq.Init.Datatypes.prod" 0).
Notation PAIR := (TConstruct PROD 0 4).
Notation "^ x" := (nNamed x)  (at level 85).
Notation "^" := (nAnon).
Infix ":t:" := tcons  (at level 87, right associativity).


Inductive P0: Prop := p0.
Inductive P1: Prop := p1.
Notation PP0 := (mkInd "P0" 0).
Notation pp0 := (TConstruct PP0 0 0).
Notation PP1 := (mkInd "P1" 0).
Notation pp1 := (TConstruct PP1 0 0).


Definition and_rect_x :=
  (and_rect (fun (a:2=2) (b:True) => conj b a) (conj (eq_refl 2) I)).
Quote Recursively Definition p_and_rect_x := and_rect_x.
Definition P_and_rect_x := Eval cbv in (program_Program p_and_rect_x).
Print P_and_rect_x.
Quote Recursively Definition cbv_and_rect_x :=
  ltac:(let t:=(eval cbv in and_rect_x) in exact t).
Definition ans_and_rect_x :=
  Eval cbv in (main (program_Program cbv_and_rect_x)).
Definition env_x := env P_and_rect_x.
Definition main_x := main P_and_rect_x.
Goal
  wcbvEval env_x 25 main_x = Ret ans_and_rect_x.
  vm_compute. (* reflexivity. *)
Abort.


Definition and_rectx :=
  and_rect (fun (x0:P0) (x1:P1) => pair (conj x1 x0) 0) (conj p0 p1).
Eval cbv in and_rectx.
Quote Recursively Definition ans_and_rectx := (* [program] of Coq's answer *)
  ltac:(let t:=(eval cbv in and_rectx) in exact t).
Definition pP_ans_and_rectx := program_Program ans_and_rectx.
Definition Ans_and_rectx :=
  Eval cbv in (wcbvEval (env pP_ans_and_rectx) 100
                        (main pP_ans_and_rectx)).
Print Ans_and_rectx.
Quote Recursively Definition p_and_rectx := and_rectx.
Print p_and_rectx.
Definition P_and_rectx := Eval cbv in (program_Program p_and_rectx).
Print P_and_rectx.
Definition P_envx := env P_and_rectx.
Definition P_mainx := main P_and_rectx.
Goal wcbvEval P_envx 1000 P_mainx = Ans_and_rectx.
vm_compute. reflexivity.
Qed.


Definition my_and_rect := 
  fun (A B : Prop) (P : Type) (f : A -> B -> P) (a : A /\ B) =>
    match a with conj x x0 => f x x0 end.
Definition my_and_rect_x :=
  (@my_and_rect (2=2) (True)
                (True /\ (2=2))
                (fun (a:2=2) (b:True) => conj b a)
                (conj (eq_refl 2) I)).
Print my_and_rect_x.
Definition eval_my_and_rect_x := Eval cbv in my_and_rect_x.
Print eval_my_and_rect_x.
Quote Recursively Definition p_eval_my_and_rect_x := eval_my_and_rect_x.
Eval vm_compute in (program_Program p_eval_my_and_rect_x).

Quote Recursively Definition p_my_and_rect_x := my_and_rect_x.
Print p_my_and_rect_x.
Definition P_my_and_rect_x := Eval cbv in (program_Program p_my_and_rect_x).
Print P_my_and_rect_x.
Quote Recursively Definition cbv_my_and_rect_x :=
  ltac:(let t:=(eval vm_compute in my_and_rect_x) in exact t).
Print cbv_my_and_rect_x.
Definition ans_my_and_rect_x :=
  Eval cbv in (main (program_Program cbv_my_and_rect_x)).
Print ans_my_and_rect_x.
Definition my_envx := env P_my_and_rect_x.
Eval vm_compute in my_envx.
Definition my_mainx := main P_my_and_rect_x.
Eval vm_compute in my_mainx.
Eval vm_compute in (wcbvEval my_envx 30 my_mainx).
Goal
  wcbvEval my_envx 30 my_mainx = Ret ans_my_and_rect_x.
  cbv. 
Abort.  (** LHS in has nested [Proof]. **)



(** Abhishek's example of looping: we don't test fixpoint guard **)
Inductive Lt (n:nat) : nat -> Prop := Lt_n: Lt n (S n).
Inductive Acc (y: nat) : Prop :=
  Acc_intro : (forall x: nat, Lt y x -> Acc x) -> Acc y.
Definition Acc_inv: forall (x:nat) (H:Acc x) (y:nat), Lt x y -> Acc y.
  intros. destruct H. apply H. apply H0.
  Defined.
Fixpoint loop (n:nat) (a:Acc n) {struct a} : nat :=
  match n with
    | _ => @loop (S n) (@Acc_inv _ a (S n) (Lt_n n))
  end.
Axiom Acc0Ax : Acc 0.
Eval vm_compute in (@loop (O + 0)).
Eval vm_compute in (@loop (O + 0) Acc0Ax).   (** Coq does not loop **)
Extraction "loop" loop.

Quote Recursively Definition p_loop0 := (@loop (O + 0) Acc0Ax).
Definition P_loop0 := Eval vm_compute in (program_Program p_loop0).
Definition P_env := Eval vm_compute in (env P_loop0).
Definition P_main := Eval vm_compute in (main P_loop0).
Eval vm_compute in wcbvEval P_env 100 P_main.


(** axioms in arguments to a data constructor **)
Axiom anat:nat.
Fixpoint double n := match n with
                       | 0 => 0
                       | S m => S (S (double m))
                     end.
Definition doubleX := (double (S (S anat))).
Eval cbv in doubleX.
Quote Recursively Definition p_doubleX := doubleX.
Definition P_doubleX := Eval vm_compute in (program_Program p_doubleX).
Definition P_doubleXenv := Eval vm_compute in (env P_doubleX).
Definition P_doubleXmain := Eval vm_compute in (main P_doubleX).
Eval vm_compute in wcbvEval P_doubleXenv 1000 P_doubleXmain.

Fixpoint listDouble (ls:list nat) :=
  match ls with
    | nil => nil
    | cons _ us => cons 0 (cons 0 (listDouble us))
  end.
Definition listDoubleX := (listDouble (cons anat (cons anat nil))).
Eval cbv in listDoubleX.
Quote Recursively Definition p_listDoubleX := listDoubleX.
Definition P_listDoubleX := Eval vm_compute in (program_Program p_listDoubleX).
Definition P_listDoubleXenv := Eval vm_compute in (env P_listDoubleX).
Definition P_listDoubleXmain := Eval vm_compute in (main P_listDoubleX).
Eval vm_compute in wcbvEval P_listDoubleXenv 1000 P_listDoubleXmain.


(****  try a singleton match  ****)
Fixpoint kjhhgfk (n:nat) (p:n = n) :=
  match p with
    | eq_refl _  => n
  end.
Quote Recursively Definition p_kjhhgfk := kjhhgfk.
Print p_kjhhgfk.
Definition kjhhgfkX := (kjhhgfk (eq_refl anat)).
Eval cbv in kjhhgfkX.
(******
(fix kjhhgfk (n : nat) (p : n = n) {struct n} : nat :=
          match p with
          | eq_refl => n
          end) anat eq_refl
***********)
Quote Recursively Definition p_kjhhgfkX := kjhhgfkX.
Definition P_kjhhgfkX := Eval vm_compute in (program_Program p_kjhhgfkX).
Definition P_kjhhgfkXenv := Eval vm_compute in (env P_kjhhgfkX).
Definition P_kjhhgfkXmain := Eval vm_compute in (main P_kjhhgfkX).
Eval vm_compute in wcbvEval P_kjhhgfkXenv 1000 P_kjhhgfkXmain.
(**************
TApp
            (TFix
               (dcons (^ "kjhhgfk")
                  (Pi (^ "n") NNN
                     (Pi (^ "p")
                        (TApp (TInd (mkInd "Coq.Init.Logic.eq" 0)) NNN
                           (tcons (TRel 0) (tunit (TRel 0)))) NNN))
                  (Lam (^ "n") NNN
                     (Lam (^ "p")
                        (TApp (TInd (mkInd "Coq.Init.Logic.eq" 0)) NNN
                           (tcons (TRel 0) (tunit (TRel 0))))
                        (TCase (mkInd "Coq.Init.Logic.eq" 0, 2, 0 :: nil)
                           (Lam (^ "n") NNN
                              (Lam (^ "p")
                                 (TApp (TInd (mkInd "Coq.Init.Logic.eq" 0)) NNN
                                    (tcons (TRel 2) (tunit (TRel 0)))) NNN))
                           (TProof (TRel 0)) (tunit (TRel 1))))) 0 dnil) 0) TAx
            (tunit
               (TApp (TConstruct (mkInd "Coq.Init.Logic.eq" 0) 0 2) NNN
                  (tunit TAx)))
********************)


(*****************************
Goal
  WcbvEval P_env P_main prop.
Proof.
  unfold P_main. eapply wConst. cbn. reflexivity.
  eapply wAppFix.
  - eapply wConst. cbn. reflexivity. eapply wFix.
  - cbn. reflexivity.
  - cbn. reflexivity.
  - eapply wPrf. eapply wAx.
  - cbn. (** stuck here **)
******************)


Function Plus1 (n : nat) {wf lt n} : nat :=
  match n with
    | 0 => 1
    | S p => S (Plus1 p)
  end.
- intros. omega.
- apply lt_wf.
Defined.
Definition x := 1.
Definition Plus1x := Plus1 x.
Eval vm_compute in Plus1x.


(** evaluation of [Function]s defined with measure or wf **
Time Quote Recursively Definition p_Plus1x := Plus1x.
Time Definition P_Plus1x : Program Term :=
  Eval vm_compute in program_Program p_Plus1x.
Time Definition P_ans :=
  Eval vm_compute in match P_Plus1x with
                       | mkPgm P_main P_env => wcbvEval P_env 1000 P_main
                     end.
Print P_ans.
(**********************)
Time Definition P_env := Eval vm_compute in (env P_Plus1x).
Time Definition P_main := Eval vm_compute in (main P_Plus1x).
Time Definition P_ans := Eval vm_compute in (wcbvEval P_env 1000 P_main).
************************)


(** does Coq eval match branches ? **)
Variable (y:nat).
Definition mbt :=
  match y with
    | 0 => (fun x:nat => x) 1
    | S n => (fun x:nat => x) 0
  end.
Eval cbv in mbt.

Quote Recursively Definition p_mbt := 
  match y with
    | 0 => (fun x:nat => x) 1
    | S n => (fun x:nat => x) 0
  end.
Definition L1g_mbt := Eval cbv in (program_Program p_mbt).
Definition mbt_env := env L1g_mbt.  (* L1g environ *)
Definition mbt_main := main L1g_mbt. (* L1g main function *)
Eval cbv in (wcbvEval mbt_env 10 mbt_main).


Set Implicit Arguments.

(** non-recursive fixpoint has non-null Defs **)
Fixpoint tst (b:bool) : bool := true.
Print tst.
Quote Recursively Definition p_tst := tst.
Print p_tst.



Inductive foo (A:Set) : Set :=
| nilf: foo A
| consf: (fun (Y W:Set) => Y -> foo Y -> foo ((fun X Z => X) A nat)) A bool.
Quote Recursively Definition foo_nat_cons := (@consf nat 0 (nilf nat)).
Print foo_nat_cons.

Fixpoint foo_list (A:Set) (fs:foo A) : list A :=
  match fs with
    | nilf _ => nil
    | consf b bs => cons b (foo_list bs)
  end.
Fixpoint list_foo (A:Set) (fs:list A) : foo A :=
  match fs with
    | nil => nilf A
    | cons b bs => consf b (list_foo bs)
  end.
Goal forall (A:Set) (fs:list A), foo_list (list_foo fs) = fs.
induction fs; try reflexivity.
- simpl. rewrite IHfs. reflexivity.
Qed.
Goal forall (A:Set) (fs:foo A), list_foo (foo_list fs) = fs.
induction fs; try reflexivity.
- simpl. rewrite IHfs. reflexivity.
Qed.

(** indexed datatypes **)
Inductive fin : nat -> Set :=
| f0: fin 0
| fS: forall (n:nat) (f:fin n), fin (S n).

Definition fiszero (n:nat) (f:fin n) : bool :=
  match f with
    | f0 => true
    | fS _ => false
  end.
Quote Recursively Definition p_fiszero := fiszero.
Print p_fiszero.

Definition blist := (@list ((fun x:Set => x) bool)).
Quote Recursively Definition clist := blist.
Print clist.
Quote Recursively Definition bcons := (@cons bool).
Print bcons.

Definition xlist := (@list (list bool)).
Quote Definition qlist := Eval cbv in xlist.
Print qlist.
Quote Recursively Definition qcons :=
  (@cons (list bool): (list bool) -> xlist -> xlist).
Print qcons.

(** trivial example **)
Definition plus11 := (plus 1 1).
Quote Recursively Definition cbv_plus11 := (* [program] of Coq's answer *)
  ltac:(let t:=(eval cbv in (plus11)) in exact t).
Print cbv_plus11.
(* [Term] of Coq's answer *)
Definition ans_plus11 := Eval cbv in (main (program_Program cbv_plus11)).
Print ans_plus11.
(* [program] of the program *)
Quote Recursively Definition p_plus11 := plus11.
Print p_plus11.
Definition P_plus11 := Eval cbv in (program_Program p_plus11).
Print P_plus11.
Goal
  let env := (env P_plus11) in
  let main := (main P_plus11) in
  wcbvEval (env) 100 (main) = Ret ans_plus11.
  vm_compute. reflexivity.
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


(** mutual recursion **)
Set Implicit Arguments.
Inductive tree (A:Set) : Set :=
  node : A -> forest A -> tree A
with forest (A:Set) : Set :=
     | leaf : A -> forest A
     | fcons : tree A -> forest A -> forest A.

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
Definition Foo : nat -> bool -> wwzz -> wwzz := 
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
Definition myTree := (T (cons (T (unit (T nil))) (cons (T (unit (T nil))) nil))).
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

(****** runs out of space **************
Time Quote Recursively Definition p_myMain := vs.myMain.
Time Definition P_myMain :=
  Eval vm_compute in (L1g.compile.program_Program p_myMain).
Definition P_env_myMain := env P_myMain.
Definition P_main_myMain := AstCommon.main P_myMain.
Time Definition eval_myMain :=
  Eval vm_compute in (wcbvEval P_env_myMain 4000 P_main_myMain).
Set Printing Width 80.
Print eval_myMain.
************************)


(********
(** match with no branches **)
Definition Fdemo (f:False) : False := match f with end.
Print Fdemo.
Quote Recursively Definition p_Fdemo := Fdemo.
Print p_Fdemo.

Axiom FF : False.
Eval compute in (Fdemo FF).


(** match: eval type parts of Defs **)
Definition bb := bool.
Definition demo (t:True) : bb := match t with I => true end.
Print demo.
Eval cbv in demo.
Quote Recursively Definition p_demo := demo.
Print p_demo.
Quote Definition qcbv_demo := Eval native_compute in demo.
Print qcbv_demo.
(*** fails **
Goal exc_wcbvEval 40 p_demo = term_Term qcbv_demo.
native_compute. reflexivity.
Qed.
***)

Definition bb1 := fun (t:True) => bool.
Definition demo1 (t:True) : (bb1 t) := match t with I => true end.
Print demo1.
Eval cbv in demo1.
Quote Recursively Definition p_demo1 := demo1.
Print p_demo1.
Quote Definition qcbv_demo1 := Eval cbv in demo1.
Print qcbv_demo1.


(** Abhishek's example **)
Definition xx := (fun x:nat => x) = (fun x:nat => x+x-x).
Print xx.
Eval cbv in xx.

Print eq.

Inductive mleq (A:Type) : A -> A-> Prop := mleqrfl:forall x:A, mleq x x.
Print mleq.

Axiom mlfeq : mleq 0 0.
Print mlfeq.
Quote Definition q_mlfeq := mlfeq.
Print q_mlfeq.
Eval cbv in (term_Term q_mlfeq).
Quote Recursively Definition p_mlfeq := mlfeq.
Print p_mlfeq.

(*** not accepted because mleqrfl has a non-Prop argument
Definition mlzero : nat :=
  match mlfeq with
    | mleqrfl x => 0
  end.
****)

Inductive NN : Prop := ZZ:NN | SS:NN->NN.
Inductive BB : Prop := tt:BB | ff:BB.

Definition mlbb : BB :=
  match mlfeq with
    | mleqrfl x => match x with O => tt | S _ => ff  end
  end.
Quote Definition q_mlbb := mlbb.
Print q_mlbb.

Axiom feq : 0 = 0.
Definition zero : nat :=
  match feq with
    | eq_refl => 0
  end.
Quote Definition q_0 := Eval cbv in 0.
Quote Recursively Definition p_zero := zero.
Print p_zero.
Eval cbv in program_Program p_zero (ret nil).
Goal exc_wcbvEval 40 p_zero = term_Term q_0.
compute. 
Abort.  (* axiom feq doesn't expand: blocks eval *)

Print and.
Inductive pack (A:Prop) : Prop := Pack: A -> A -> A -> A -> pack A.
Axiom packax: forall A, pack A -> pack A.
Definition pack_nat (A:Prop) (a:pack A) : nat :=
  match packax a with
    | Pack b1 b2 b3 b4 => 0
  end.
Quote Recursively Definition p_pack_nat := (pack_nat (Pack I I I I)).
Goal exc_wcbvEval 40 p_pack_nat = term_Term q_0.
compute. 
Abort.
  
Axiom andax: forall A, A /\ A -> A /\ A.
Definition and_nat (A:Prop) (a:A /\ A) : nat :=
  match andax a with
    | conj b1 b2 => 0
  end.
Quote Recursively Definition p_and_nat := (and_nat (conj I I)).
Print p_and_nat.
Eval cbv in (program_Program p_and_nat (ret nil)).
Goal exc_wcbvEval 40 p_and_nat = term_Term q_0.
compute. 
Abort.


Axiom feq1 : forall (y:bool), (fun x:nat => x) = (fun x:nat => x+2).
Print feq1.
Eval cbv in feq1.
Definition zero1 : nat :=
  match feq1 true with
    | eq_refl => 0
  end.
Eval cbv in zero1.
Quote Definition q_zero1 := Eval cbv in zero1.
Print q_zero1.
Quote Recursively Definition p_zero1 := zero1.
Print p_zero1.
Goal exc_wcbvEval 40 p_zero1 = term_Term q_zero1.
compute. 
Abort.

(** fails because Coq cbv is not weak ***
Axiom feq2 : 0 = 0.
Print feq2.
Eval cbv in feq2.
Definition zero2: nat :=
  match feq2 with
    | eq_refl => 0
  end.
Print zero2.
Eval cbv in zero2.
Quote Definition q_zero2 := Eval cbv in zero2.
Print Template.Ast.
Print q_zero2.
Print IDProp.
Eval cbv in (term_Term, q_zero2).
Quote Recursively Definition p_zero2 := zero2.
Print p_zero2.
Print IDProp.
Goal exc_wcbvEval 40 p_zero2 = term_Term q_zero2.
compute. reflexivity.
***)

Definition Lb (b:bool) : (b = b) := eq_refl b. 
Definition testLb := Lb (orb true true).
Quote Recursively Definition p_testLb := testLb.
Print p_testLb.
Eval cbv in testLb.
Quote Definition q_testLb := Eval cbv in testLb.
Print q_testLb.
Goal exc_wcbvEval 40 p_testLb = term_Term q_testLb.
compute. reflexivity.
Qed.

Definition trivadd := (1 + 0).
Quote Definition q_trivadd := Eval cbv in trivadd.
Print q_trivadd.
Quote Recursively Definition p_trivadd := trivadd.
Print p_trivadd.
Goal exc_wcbvEval 100 p_trivadd = term_Term q_trivadd.
compute. reflexivity.
Qed.

Axiom ax : forall x:nat, x = x.
Definition testAx := ax (1 + 0).
Print testAx.
Eval cbv in testAx.
Quote Definition q_testAx := Eval cbv in testAx.
Print q_testAx.
Quote Recursively Definition p_testAx := testAx.
Print p_testAx.

Eval cbv in (program_Program p_testAx (Ret nil)).
Definition pgm :=
  match  (program_Program p_testAx (Ret nil)) with
    | Ret pgm => env pgm
    | x => nil
  end.
Eval compute in pgm.
Definition main :=
  match  (program_Program p_testAx (Ret nil)) with
    | Ret pgm => main pgm
    | x => prop
  end.
Eval compute in main.

Goal exc_wcbvEval 40 p_testAx = term_Term q_testAx.
compute. reflexivity.
Qed.

Goal exc_wcbvEval 40 p_testAx = term_Term q_testAx.
compute. reflexivity.
Qed.

(** type casting ? **)
Check (cons: forall (A:Set), A -> list A -> list A).
Check ((fun A : Set => cons (A:=A)) : forall (A:Set), A -> list A -> list A).
Quote Definition qconsa := (cons: forall (A:Set), A -> list A -> list A).
Print qconsa.
(**
Goal True.   -- Not equal
constr_eq (cons: forall (A:Set), A -> list A -> list A) cons.
**)
Goal (cons: forall (A:Set), A -> list A -> list A) =
     (cons: forall (A:Set), A -> list A -> list A).
cbv beta.
Abort.

Goal (cons: forall (A:Set), A -> list A -> list A) = cons.
reflexivity.
Qed.

Check cons.
Check (cons: forall (A:Set), A -> list A -> list A).
Check (cons Type).
(* fails
Check ((cons: forall (A:Set), A -> list A -> list A) Type).
*)

Goal (cons: forall (A:Set), A -> list A -> list A) = cons.
simpl. reflexivity.
Qed.
Quote Definition qconsA := (cons: forall (A:Set), (A:Set) -> list A -> list A).
Print qconsA.
Quote Definition qconsb :=
  (cons: forall (A:Type), (A:Type) -> list A -> list A).
Print qconsb.

Unset Implicit Arguments.
Inductive list2 (A B:Type) : Type :=
| nil2 : list2 A B
| cons2 : A -> B -> list2 A B.

Definition cons2' :=
  (cons2: forall (A:Set) (B:Type), A -> B -> list2 A B).
Print cons2'.
Goal (cons2: forall (A:Set) (B:Type), A -> B -> list2 A B ) = cons2.
Abort.

Definition T0 := Type.
Definition T1 := Type.
Check (T0 : Type).
Check (Type : T0).

Check ((fun (A:Type) (a:A) => a)
         (forall (A:Type), A -> A)
         (fun (A:Type) (a:A) => a)).
(****
Definition qconsA := (cons: forall (A:Set), (A:Set) -> list A -> list A).
Print qconsA.
Quote Definition qconsb :=
  (cons: forall (A:Type), (A:Type) -> list A -> list A).
Print qconsb.
Quote Definition qconsc :=
  (cons: forall (A:Set), (A:Type) -> list A -> list A).
Print qconsc.

Quote Definition AppApp1 := ((@cons nat:nat -> list nat -> list nat) 0).
Print AppApp1.
Quote Definition AppApp2 :=
  Eval cbv in ((@cons nat:nat -> list nat -> list nat) 0).
Print AppApp2.
***)

Definition Nat := nat.
Definition typedef := ((fun (A:Type) (a:A) => a) Nat 1).
Quote Definition q_typedef := Eval cbv in typedef.
Quote Recursively Definition p_typedef := typedef.
Goal
  (exc_wcbvEval 200 p_typedef) = term_Term q_typedef.
compute. reflexivity.
Qed.

Definition II := fun (A:Type) (a:A) => a.
Quote Definition q_II := Eval cbv in II.
Quote Recursively Definition p_II := II.
Goal
  (exc_wcbvEval 10 p_II) = term_Term q_II.
reflexivity.
Qed.


(* Must data constructors have fixed arity? It seems the answer is yes. *)
Fixpoint arity (n:nat) (A:Type) : Type :=
  match n with
    | 0 => A
    | S n => A -> arity n A
  end.
Eval cbv in arity 2 bool.
Inductive bar : Type :=
| b0: arity 0 bar
| b1: arity 1 bar.
(** this constructor is not accepted:
| bn: forall n:nat, arity n bar.
***)

Inductive baz : Type :=
| baz1: baz
| baz2: arity 5 bool -> baz.


(** playing with arity of constructors **
Fixpoint Arity (n:nat) (A:Prop) : Prop :=
  match n with
    | 0 => A
    | S n => A -> Arity n A
  end.
Definition aaa : Prop := forall (X:Prop) (n:nat), X -> (Arity n X) -> X.
Definition ZZ: aaa := fun (X:Prop) (n:nat) (z:X) (s:Arity n X) => z.

Variable arb:nat.
Inductive vec1 A : nat -> Type :=
  |v1nil : vec1 A 0
  |v1cons : forall (h:A) (n:nat), vec1 A (n + n) -> vec1 A arb.
Inductive vec2 A (n:nat) : Type :=
  |v2nil : vec2 A n
  |v2cons : forall (h:A), vec2 A (n + n) -> vec2 A n.
***)



Inductive uuyy: Set := uu | yy.
Inductive wwzz: Set := ww (_:uuyy)| zz (_:nat) (_:uuyy) (_:bool).
Definition Foo : nat -> bool -> wwzz -> wwzz := 
  fun (n:nat) (b:bool) (x:wwzz) =>
    match n,x,b with
      | 0, _, true => ww uu
      | 0, _, false => ww yy
      | S m, ww x, b => zz m x b
      | S m, zz n x c, b => zz m x b
    end.
Definition Foo0ty := (Foo 0 true (ww uu)).
Quote Recursively Definition p_Foo0ty := Foo0ty.
Quote Definition q_Foo0ty := Eval cbv in Foo0ty.
Goal (exc_wcbvEval 23 p_Foo0ty) = term_Term q_Foo0ty.
reflexivity.
Qed.

(** destructing a parameterised datatype **)
Inductive lst (A:Set) : Set := 
| nl: lst A
| cns: A -> lst A -> lst A.
Definition hd (A:Set) (ls:lst A) (default:A) : A :=
  match ls with
    | nl _ => default
    | cns a _ => a
  end.
Quote Recursively Definition p_hd :=
 (@hd bool (@cns bool true (nl bool)) false).
Quote Definition q_hd :=
  Eval cbv in (@hd bool (@cns bool true (nl bool)) false).
Goal exc_wcbvEval 100 p_hd = term_Term q_hd.
reflexivity.
Qed.

(** destructing a parameterised datatype **)
Inductive nelst (A:Set) : Set := 
| nenl: A -> nelst A
| necns: A -> nelst A -> nelst A.
Definition nehd (A:Set) (ls:nelst A) : A :=
  match ls with
    | nenl a => a
    | necns a _ => a
  end.
Quote Recursively Definition p_nehd :=
  (@nehd bool (@necns bool true (@nenl bool false))).
Quote Definition q_nehd :=
  Eval cbv in (@nehd bool (@necns bool true (@nenl bool false))).
Goal exc_wcbvEval 100 p_nehd = term_Term q_nehd.
reflexivity.
Qed.


Inductive tm (A:Set) : Set := 
| vv: nat -> tm A 
| cc: A -> tm A.
Definition occIn (A:Set) (t:tm A) : nat :=
  match t with
    | vv _ m => m
    | cc _ => 0
end.
Quote Recursively Definition p_occIn := (occIn (cc true)).
Quote Definition q_occIn := Eval cbv in (occIn (cc true)).
Goal exc_wcbvEval 20 p_occIn = term_Term q_occIn.
reflexivity.
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

Quote Recursively Definition p_slowFib1 := (slowFib 1).
Quote Definition q_slowFib1 := Eval cbv in (slowFib 1).
Goal exc_wcbvEval 10 p_slowFib1 = term_Term q_slowFib1.
reflexivity.
Qed.

Quote Recursively Definition p_slowFib3 := (slowFib 3).
Quote Definition q_slowFib3 := Eval cbv in (slowFib 3).
Goal exc_wcbvEval 100 p_slowFib3 = term_Term q_slowFib3.
compute; reflexivity.
Qed.

Fixpoint fibrec (n:nat) (fs:nat * nat) {struct n} : nat :=
  match n with
    | 0 => fst fs
    | (S n) => fibrec n (pair ((fst fs) + (snd fs)) (fst fs))
  end.
Definition fib : nat -> nat := fun n => fibrec n (pair 0 1).

(*** fails due to wcbv not matching Coq reduction ***
Quote Recursively Definition p_fibrec0 := (fibrec 0).
Quote Definition q_fibrec0 := Eval hnf in (fibrec 0).
Goal exc_wcbvEval 3 p_fibrec0 = term_Term q_fibrec0. simpl. 
reflexivity.
Qed.
***)

Quote Recursively Definition p_fib3 := (fib 3).
Quote Definition q_fib3 := Eval cbv in (fib 3).
Goal exc_wcbvEval 100 p_fib3 = term_Term q_fib3.
vm_compute; reflexivity.
Qed.

Quote Recursively Definition p_fib5 := (fib 5).
Quote Definition q_fib5 := Eval cbv in (fib 5).
Goal exc_wcbvEval 100 p_fib5 = term_Term q_fib5.
vm_compute; reflexivity.
Qed.

Quote Recursively Definition p_fib10 := (fib 10).
Quote Definition q_fib10 := Eval cbv in (fib 10).
Goal exc_wcbvEval 400 p_fib10 = term_Term q_fib10.
vm_compute. reflexivity.
Qed.


(*** instantiate in a branch of a mutual fixpoint ***)
Section S1.
Variable nn:nat.
Fixpoint tree_size1 (t:tree bool) : nat :=
  match t with
    | node a f => S (forest_size1 f)
  end
with forest_size1 (f:forest bool) : nat :=
       match f with
         | leaf b => nn
         | fcons t f1 => (tree_size1 t + forest_size1 f1)
       end.
End S1.

Quote Recursively Definition p_forest_size1 := (forest_size1 1 sherwood).
Quote Definition q_forest_size1 := Eval cbv in (forest_size1 1 sherwood).
Goal (exc_wcbvEval 100 p_forest_size1) = term_Term q_forest_size1.
vm_compute; reflexivity.
Qed.

Quote Recursively Definition p_arden_size1 := (forest_size arden).
Quote Definition q_arden_size1 := Eval cbv in (forest_size arden).
Goal (exc_wcbvEval 100 p_arden_size1) = term_Term q_arden_size1.
vm_compute; reflexivity.
Qed.
 ************)
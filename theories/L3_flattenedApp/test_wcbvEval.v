
Require Import ExtLib.Data.String.
Require Import omega.Omega.
Require Import Template.Template.
Require Import Common.Common.
Require L2_5.L2_5.         (* whole L2_5 library is exported by L2_5.L2_5 *)
Require Import L3.compile. 
Require Import L3.term.
Require Import L3.program.
Require Import L3.wcbvEval.

Local Open Scope bool.
Local Open Scope list.
Local Open Scope string_scope.

Set Template Cast Propositions. 

(*** examples with parameters  *****)
Axiom xxxxxx : Set.
Notation Lam := (TLambda).
Notation "@ x" := (nNamed x)  (at level 85).
Notation LLL := (mkInd "Top.LL" 0).
Notation "^ x" := (TRel x)    (at level 85).
Notation NNN := (TConstruct LLL 0).
Notation CCC := (TConstruct LLL 1).
Notation Bool := (mkInd "Coq.Init.Datatypes.bool" 0).
Notation tt := (TConstruct Bool 0 tnil).
Notation ff := (TConstruct Bool 1 tnil).

Inductive LL (B:Type) : Type := NN: LL B | CC: B -> LL B -> LL B.
Quote Recursively Definition p_CC := CC.
Eval cbv in (program_Program p_CC).
Quote Recursively Definition p_CC_bool := (CC bool).
Eval cbv in (program_Program p_CC_bool).
Quote Recursively Definition p_CC_bool_tt := (CC bool true).
Eval cbv in (program_Program p_CC_bool_tt).
Definition ffs := (CC bool false (NN bool)).
Quote Recursively Definition p_CC_bool_tt_ffs := (CC bool true ffs).
Eval cbv in (program_Program p_CC_bool_tt_ffs).

Set Printing Width 80.
Set Printing Depth 1000.

Fixpoint Map (B A:Type) (f:B -> A) (bs:LL B) : LL A :=
  match bs with
    | NN _ => NN A
    | CC _ x xs => CC A (f x) (Map B A f xs)
  end.

Quote Recursively Definition p_Map := Map.
Eval cbv in (program_Program p_Map).

Arguments nil : clear implicits.
Arguments cons : clear implicits.
Arguments eq_refl : clear implicits.
Inductive vec (A:Type) (n:nat) : Type :=
| vecc : forall (l:list A), length l = n -> vec A n.
Quote Recursively Definition p_vec := vec.
Arguments vecc : clear implicits.

Quote Recursively Definition p_vecc := vecc.
Eval cbv in (program_Program p_vecc).
Quote Recursively Definition p_vecc_bool := (vecc bool).
Eval cbv in (program_Program p_vecc_bool).
Quote Recursively Definition p_vecc_bool_0 := (vecc bool 0).
Eval cbv in (program_Program p_vecc_bool_0).
Quote Recursively Definition p_vecc_bool_0_nil := (vecc bool 0 (nil bool)).
Eval cbv in (program_Program p_vecc_bool_0_nil).
Quote Recursively Definition p_vecc_bool_0_nil_eqr :=
  (vecc bool 0 (nil bool) (eq_refl nat 0)).
Eval cbv in (program_Program p_vecc_bool_0_nil_eqr).

(***
Fixpoint up_to (n:nat) : list nat :=
  match n with
    | 0 => nil nat
    | S m => cons nat m (up_to m)
  end.

Lemma length_up_to:
  forall (n:nat), length (up_to n) = n.
Proof.
  induction n. reflexivity. cbn. rewrite IHn. reflexivity.
Qed.

Check (fun (n:nat) => vecc nat n (up_to n) (length_up_to n)).

Fixpoint foo (n:nat) (v:vec nat n) {struct n} : vec nat :=
  match n with
    | 0 => nil A
    | S m => match v with
               | vecc _ _ (nil _) _ => nil A
               | vecc _ _ (cons _ x xs) _ => xs
             end
  end.
                 cons A x (vec_list
                             A m
                             (vecc A (length xs) xs (eq_refl nat (length xs))))
             end
  end.
                                                                
    | vecc _ _ (nil _) _, _ => nil A
    | vecc _ _ (cons _ x xs) (eq_refl _ _), m =>
      cons A x (vec_list A (pred m) (vecc A (pred m) xs (eq_refl nat _)))
  end.
 ***)

Reset xxxxxx.  (** end examples with paameters **)

Set Printing Width 80.
Set Printing Depth 1000.
Set Implicit Arguments.


Notation NN := (mkInd "Datatypes.nat" 0).
Notation SS := (TConstruct NN 1).
Notation ZZ := (TConstruct NN 0).
Notation Lam := (TLambda).
Notation tLam := (tLambda).
Notation tPi := (tProd).
Notation tPROP := (tSort sProp).
Notation AND := (mkInd "Logic.and" 0).
Notation CONJ := (TConstruct AND 0).
Notation TRUE := (mkInd "Logic.True" 0).
Notation II := (TConstruct TRUE 0).
Notation EQ := (mkInd "Logic.eq" 0).
Notation RFL := (TConstruct EQ 0).
Notation PROD := (mkInd "Datatypes.prod" 0).
Notation PAIR := (TConstruct PROD 0).
Notation "^ x" := (nNamed x)  (at level 85).
Notation "^" := (nAnon).
Infix ":t:" := tcons  (at level 87, right associativity).
Notation "fn [| arg @ args |]" :=
  (TApp fn arg args)  (at level 90, left associativity).


(** Check eta expansion of constructors **)
Quote Recursively Definition pcons := (@cons bool).
Definition Pcons := Eval cbv in (program_Program pcons).
Print Pcons.

Inductive fyy : Set := Fyy: bool -> bool -> bool -> fyy.
Quote Recursively Definition pFyy := Fyy.
Definition PFyy := Eval cbv in (program_Program pFyy).
Print PFyy.
Quote Recursively Definition pFzz := (fun x => Fyy x).
Definition PFzz := Eval cbv in (program_Program pFzz).
Print PFzz.

Function Plus1 (n : nat) {wf lt n} : nat :=
  match n with
    | 0 => 1
    | S p => S (Plus1 p)
  end.
- intros. omega.
- apply lt_wf.
Defined.
Definition x:nat := 0.
Definition Plus1x := Plus1 x.
Eval vm_compute in Plus1x.

(** evaluation of [Function]s defined with measure or wf **)
Time Quote Recursively Definition p_Plus1x := Plus1x.
Time Definition P_Plus1x : Program Term :=
  Eval vm_compute in program_Program p_Plus1x.
Time Definition P_env := Eval vm_compute in (env P_Plus1x).
Time Definition P_main := Eval vm_compute in (main P_Plus1x).
Time Definition P_ans := Eval vm_compute in (wcbvEval P_env 1000 P_main).
Print P_ans.
                             
Variable (y:nat).
Quote Recursively Definition p_mbt := 
  match y with
    | 0 => (fun x:nat => x) 1
    | S n => (fun x:nat => x) 0
  end.
Definition L1g_mbt := Eval cbv in (program_Program p_mbt).
Definition mbt_env := env L1g_mbt.  (* L1g environ *)
Definition mbt_main := main L1g_mbt. (* L1g main function *)
Eval cbv in (wcbvEval mbt_env 10 mbt_main).

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

Inductive pack (A:Prop) : Prop := Pack: A -> A -> A -> A -> pack A.
Axiom packax: forall A, pack A -> pack A.
Definition pack_nat (A:Prop) (a:pack A) : nat :=
  match packax a with
    | Pack b1 b2 b3 b4 => 0
  end.
Quote Recursively Definition p_pack_nat := (pack_nat (Pack I I I I)).
Check p_pack_nat.
Definition P_pack_nat := Eval cbv in (program_Program p_pack_nat).
Print P_pack_nat.

Inductive xxxx : Set :=
| xxxxl: forall n:nat, n = 0 -> xxxx
| xxxxr: forall n:nat, n = 1 -> xxxx.
Print xxxx.
Axiom Xxxx : xxxx.
Definition yyyy (f:xxxx) :=
  match f with xxxxl q => f | xxxxr q => f end.
Definition yyyyX := (yyyy Xxxx).
Print yyyyX.
Quote Recursively Definition cbv_yyyyX := (* [program] of Coq's answer *)
  ltac:(let t:=(eval cbv in (yyyyX)) in exact t).
Print cbv_yyyyX.
(* [Term] of Coq's answer *)
Definition ans_yyyyX := Eval cbv in (main (program_Program cbv_yyyyX)).
(* [program] of the program *)
Quote Recursively Definition p_yyyyX := yyyyX.
Print p_yyyyX.
Definition P_yyyyX := Eval cbv in (program_Program p_yyyyX).
Print P_yyyyX.
Goal
    let env := (env P_yyyyX) in
    let main := (main P_yyyyX) in
    wcbvEval (env) 100 (main) = Ret ans_yyyyX.
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
  wcbvEval (env) 1000 (main) = Ret ans_size_myTree.
  vm_compute. reflexivity.
Qed.

(** well founded definition **)
Function Gcd (a b : nat) {wf lt a} : nat :=
match a with
 | O => b 
 | S k =>  Gcd (b mod S k)  (S k)
end.
Proof.
  - intros m n k Heq. subst. apply Nat.mod_upper_bound.
    omega.
  - exact lt_wf.
Defined.

Definition Gcdx := (Gcd 4 2).
Eval cbv in Gcdx.
Time Quote Recursively Definition pGcdx := Gcdx.
Time Definition PGcdx := Eval cbv in (program_Program pGcdx).
Time Definition Penv_Gcdx := env PGcdx.
Time Definition Pmain_Gcdx := main PGcdx.
Time Definition ans_Gcdx := Eval cbv in (wcbvEval Penv_Gcdx 1000 Pmain_Gcdx).
Print ans_Gcdx.

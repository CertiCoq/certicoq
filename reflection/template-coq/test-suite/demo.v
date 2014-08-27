Add LoadPath "../theories" as Template.
Require Import Template.Template.
Require Import Ast.

Local Open Scope string_scope.

(** This is just printing **)
Test Quote (fun x : nat => x).

Test Quote (fun (f : nat -> nat) (x : nat) => f x).

Test Quote (let x := 2 in x).

Test Quote (let x := 2 in
            match x with
              | 0 => 0
              | S n => n
            end).

Test Quote (fun (A:Prop) => A).
Test Quote (fun (A:Set) => A).

Inductive test:Set := test1 | test2.
Test Quote test.
Test Quote test1.
Test Quote test2.
Eval compute in test_rec.
Quote Definition xxx := Eval compute in test_rec.
Print xxx.
Quote Definition yyy := Eval compute in test_ind.
Print yyy.
(**
Quote Definition xxx := Eval compute in test_rect.
**)

(** Build a definition **)
Definition d : Ast.term.
  let t := constr:(fun x : nat => x) in
  let k x := refine x in
  quote_term t k.
Defined.
Print d.

(** Another way **)
Quote Definition d' := (fun x : nat => x).
Print d'.

(** To quote existing definitions **)
Definition id_nat : nat -> nat := fun x => x.

Quote Definition d'' := Eval compute in id_nat.
Print d''.

(** Fixpoints **)
Fixpoint add (a b : nat) : nat :=
  match a with
    | 0 => b
    | S a => S (add a b)
  end.

Fixpoint add' (a b : nat) : nat :=
  match b with
    | 0 => a
    | S b => S (add' a b)
  end.

Quote Definition add_syntax := Eval compute in add.
Print add_syntax.

Quote Definition add'_syntax := Eval compute in add'.
Print add'_syntax.

(** Reflecting definitions **)

Make Definition zero_from_syntax := (tConstruct (mkInd "Coq.Init.Datatypes.nat" 0) 0).
Print zero_from_syntax.

Make Definition two_from_syntax := (tApp (Ast.tConstruct (mkInd "Coq.Init.Datatypes.nat" 0) 1)
   (tApp (Ast.tConstruct (mkInd "Coq.Init.Datatypes.nat" 0) 1)
      (tConstruct (mkInd "Coq.Init.Datatypes.nat" 0) 0 :: nil) :: nil)).
Print two_from_syntax.

Require Import NPeano.
Require Import Recdef.
Require Import Omega.
Require Import List.

(***
Function half (n: nat) {wf lt n} : nat :=
  if ltb 1 n then half (pred (pred n))  else 0.
Proof.
intros n. unfold ltb. induction (n). simpl. discriminate.
intros h. simpl. omega. exact lt_wf.
Qed.

Print half_F.
Eval compute in (half_F half 10).
***)

Fixpoint fibrec (n:nat) (fs:list nat) {struct n} : nat :=
  match n with
    | 0 => hd 0 fs
    | (S n) => fibrec n (cons ((hd 0 fs) + (hd 0 (tl fs))) fs)
  end.
Definition fib n := fibrec n (cons 0 (cons 1 nil)).
Quote Definition qfib := fib.
Print qfib.
Quote Definition qfib1 := Eval cbv delta[fib] in fib.
Print qfib1.

Eval compute in (fib 0).
Eval compute in (fib 1).
Eval compute in (fib 2).
Eval compute in (fib 3).
Eval compute in (fib 20).
Eval compute in (fib 24).

Definition Fib (n:nat) :=
  let fibrec:= fibrec in let plus:= plus in fibrec n (cons 0 (cons 1 nil)).
Definition Fib' := Eval cbv delta[Fib fibrec plus] in Fib.
Print Fib'.

Quote Definition fib' := fib.
Print fib'.
Definition fib'' := Eval cbv delta[fib fibrec] in fib.
Print fib''.
Quote Definition fib''' := Eval cbv delta[fib fibrec] in fib.
Print fib'''.
Quote Definition fib'''' := Eval compute in fib.
Print fib''''.

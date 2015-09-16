Require Import String.
Set Implicit Arguments.

Inductive exception (A:Type) := Exc (_:string) | Ret (_:A).
Implicit Arguments Ret [A].
Implicit Arguments Exc [A].

Definition ret {A: Type} (x: A) := Ret x.
Definition raise {A: Type} (str:string) := @Exc A str.
 
Definition bind
    {A B: Type} (a: exception A) (f: A -> exception B): exception B :=
  match a with
    | Ret x => f x
    | Exc str => Exc str
  end.

Notation "A >>= F" := (bind A F) (at level 42, left associativity).
Notation "'do' X <- A ; B" := (bind A (fun X => B))
    (at level 200, X ident, A at level 100, B at level 200).

Lemma mon_left_id: forall (A B: Type) (a: A) (f: A -> exception B),
  ret a >>= f = f a.
intros.
reflexivity.
Qed.

Lemma mon_right_id: forall (A: Type) (a: exception A),
  a >>= ret = a.
intros.
induction a; repeat reflexivity.
Qed.
 
Lemma mon_assoc :
  forall (A B C: Type) (a: exception A)
         (f: A -> exception B) (g: B -> exception C),
    (a >>= f) >>= g = a >>= (fun x => f x >>= g).
intros.
induction a; repeat reflexivity.
Qed.

Definition econs
  (B:Type) (b:exception B) (bs:exception (list B)): exception (list B) :=
  do bb <- b;
  do bbs <- bs;
  ret (cons bb bbs).

Fixpoint emap (A B: Type) (f: A -> exception B) (cs: list A) :
                       exception (list B) :=
  match cs with
    | nil => ret nil
    | cons c cs => do C <- f c;
                   do Cs <- emap f cs;
                   ret (cons C Cs)
  end.

Definition epair2
  (A B:Type) (a:A) (b:exception B): exception (A * B) :=
  do bb <- b;
  ret (pair a bb).

Fixpoint exnNth (A:Type) (xs:list A) (n:nat) : exception A :=
  match xs, n with
    | nil, _ => raise "exnNth; no hit"
    | cons x xs, 0 => ret x
    | cons x xs, S m => exnNth xs m
  end.


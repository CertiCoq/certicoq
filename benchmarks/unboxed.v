(* These definitions from https://coq.inria.fr/distrib/current/stdlib/Coq.Numbers.Cyclic.Int31.Int31.html *)

Require Export ZArith.

Fixpoint nfun A n B :=
 match n with
  | O => B
  | S n => A -> (nfun A n B)
 end.

Notation " A ^^ n --> B " := (nfun A n B)
 (at level 50, n at next level) : type_scope.

Fixpoint napply_cst (A B:Type)(a:A) n : (A^^n-->B) -> B :=
 match n return (A^^n-->B) -> B with
  | O => fun x => x
  | S n => fun x => napply_cst _ _ a n (x a)
 end.

Fixpoint nfun_to_nfun (A B C:Type)(f:B -> C) n :
 (A^^n-->B) -> (A^^n-->C) :=
 match n return (A^^n-->B) -> (A^^n-->C) with
  | O => f
  | S n => fun g a => nfun_to_nfun _ _ _ f n (g a)
 end.
Definition napply_except_last (A B:Type) :=
 nfun_to_nfun A B (A->B) (fun b a => b).

Definition napply_then_last (A B:Type)(a:A) :=
 nfun_to_nfun A (A->B) B (fun fab => fab a).

Fixpoint nfold A B (f:A->B->B)(b:B) n : (A^^n-->B) :=
 match n return (A^^n-->B) with
  | O => b
  | S n => fun a => (nfold _ _ f (f a b) n)
 end.

Fixpoint nprod A n : Type := match n with
 | O => unit
 | S n => (A * nprod A n)%type
end.
Notation "A ^ n" := (nprod A n) : type_scope.

Fixpoint ncurry (A B:Type) n : (A^n -> B) -> (A^^n-->B) :=
  match n return (A^n -> B) -> (A^^n-->B) with
  | O => fun x => x tt
  | S n => fun f a => ncurry _ _ n (fun p => f (a,p))
  end.

Fixpoint nuncurry (A B:Type) n : (A^^n-->B) -> (A^n -> B) :=
 match n return (A^^n-->B) -> (A^n -> B) with
  | O => fun x _ => x
  | S n => fun f p => let (x,p) := p in nuncurry _ _ n (f x) p
 end.

Definition nfun_to_nfun_bis A B C (f:B->C) n :
 (A^^n-->B) -> (A^^n-->C) :=
 fun anb => ncurry _ _ n (fun an => f ((nuncurry _ _ n anb) an)).

Fixpoint nfold_bis A B (f:A->B->B)(b:B) n : (A^^n-->B) :=
 match n return (A^^n-->B) with
  | O => b
  | S n => fun a =>
      nfun_to_nfun_bis _ _ _ (f a) n (nfold_bis _ _ f b n)
 end.

Fixpoint napply_discard (A B:Type)(b:B) n : A^^n-->B :=
 match n return A^^n-->B with
  | O => b
  | S n => fun _ => napply_discard _ _ b n
 end.

Definition size := 31%nat.

Inductive digits : Type := D0 | D1.

Definition digits31 t := Eval compute in nfun digits size t.

Inductive int31 : Type := I31 : digits31 int31.


Delimit Scope int31_scope with int31.
Local Open Scope int31_scope.

Definition On : int31 := Eval compute in napply_cst _ _ D0 size I31.

Definition In : int31 := Eval compute in (napply_cst _ _ D0 (size-1) I31) D1.

Definition Tn : int31 := Eval compute in napply_cst _ _ D1 size I31.

Definition Twon : int31 := Eval compute in (napply_cst _ _ D0 (size-2) I31) D1 D0.

Definition sneakr : digits -> int31 -> int31 := Eval compute in
 fun b => int31_rect _ (napply_except_last _ _ (size-1) (I31 b)).

Definition sneakl : digits -> int31 -> int31 := Eval compute in
 fun b => int31_rect _ (fun _ => napply_then_last _ _ b (size-1) I31).

Definition shiftl := sneakl D0.
Definition shiftr := sneakr D0.
Definition twice := sneakl D0.
Definition twice_plus_one := sneakl D1.

Definition firstl : int31 -> digits := Eval compute in
 int31_rect _ (fun d => napply_discard _ _ d (size-1)).

Definition firstr : int31 -> digits := Eval compute in
 int31_rect _ (napply_discard _ _ (fun d=>d) (size-1)).


Definition iszero : int31 -> bool := Eval compute in
 let f d b := match d with D0 => b | D1 => false end
 in int31_rect _ (nfold_bis _ _ f true size).

Fixpoint recl_aux (n:nat)(A:Type)(case0:A)(caserec:digits->int31->A->A)
 (i:int31) : A :=
  match n with
  | O => case0
  | S next =>
          if iszero i then
             case0
          else
             let si := shiftl i in
             caserec (firstl i) si (recl_aux next A case0 caserec si)
  end.

Fixpoint recr_aux (n:nat)(A:Type)(case0:A)(caserec:digits->int31->A->A)
 (i:int31) : A :=
  match n with
  | O => case0
  | S next =>
          if iszero i then
             case0
          else
             let si := shiftr i in
             caserec (firstr i) si (recr_aux next A case0 caserec si)
  end.

Definition recl := recl_aux size.
Definition recr := recr_aux size.


Definition incr : int31 -> int31 :=
 recr int31 In
   (fun b si rec => match b with
     | D0 => sneakl D1 si
     | D1 => sneakl D0 rec end).

Definition phi : int31 -> Z :=
 recr Z (0%Z)
  (fun b _ => match b with D0 => Z.double | D1 => Z.succ_double end).

Definition compare31 (n m : int31) := ((phi n)?=(phi m))%Z.

Definition eqb31 (n m : int31) :=
 match compare31 n m with Eq => true | _ => false end.

Inductive list_or_int (A: Type) : Type :=
|  LI_list: list(A) -> list_or_int A
|  LI_int: int31 -> list_or_int A.
Arguments LI_list {A} _.
Arguments  LI_int {A} _.
Definition bignum := list_or_int int31.


(** Now, this is the code we'd like to optimize: *)

Definition f(x: int31) := incr (incr (x)).

Fixpoint div2' (carry: digits) (x: list int31) : list int31 :=
 match x with
 | nil => nil
 | cons a r => sneakr carry a :: div2' (firstr a) r
 end.

Fixpoint normalize (x: list int31) : bignum :=
 match x with
 | nil => LI_int On
 | cons a nil => LI_int a
 | cons a r => if eqb31 a On 
                     then normalize r 
                     else LI_list x
 end.

Definition div2 (x: bignum) : bignum :=
match x with
| LI_list a => normalize (div2' D0 a)
| LI_int i => LI_int (shiftr i)
end.






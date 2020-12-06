From CertiCoq.Plugin Require Import CertiCoq.

Require Import Arith PArith List String Ascii.
Require Import ExtLib.Data.String.

Import ListNotations. 

(* Example 1: printing axioms *)
Axiom (print_nat : nat -> unit).
Axiom (print_str : string -> unit).
Axiom (new_line : unit -> unit).

Definition print_list (l : list nat) : unit :=
  let aux :=
      fix aux l :=
        match l with
        | [] => tt
        | [x] => print_nat x
        | x :: l =>
          let _ := print_nat x in
          let _ := print_str ";" in
          aux l
        end in
  let _ := print_str "[" in
  let _ := aux l in
  let _ := print_str "]" in new_line tt.


Definition print_lst := print_list [1;2;3;4;5].

CertiCoq Compile -direct print_lst
Extract Constants [ print_nat => "print_gallina_nat", print_str => "print_gallina_string", new_line => "print_new_line" ]
Include [ "print.h" ].


(* Example 2: int 63 *)

Axiom (int63 : Type).
Axiom (add : int63 -> int63 -> int63).
Axiom (minus : int63 -> int63 -> int63).
Axiom (mul : int63 -> int63 -> int63).
Axiom (print_int63 : int63 -> unit).

Axiom (zero_int63 : int63).
Axiom (one_int63 : int63).


Fixpoint fib_aux (n : nat) (prev0 prev1 : int63) :=
  match n with
  | 0 => add prev0 prev1
  | S n => fib_aux n (add prev0 prev1) prev0
  end.

Fixpoint fib (n : nat) :=
  match n with
  | 0 => zero_int63
  | _ => fib_aux (n - 1) zero_int63 one_int63
  end.

Definition fibn : unit :=
  let _ := print_int63 (fib 11) in
  new_line tt.

CertiCoq Compile -direct fibn
Extract Constants [ add => "add_int63", zero_int63 => "zero_int63", one_int63 => "one_int63", print_int63 => "print_int63", new_line => "print_new_line" ]
Include [ "int63.h" ].

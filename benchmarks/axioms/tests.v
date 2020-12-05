From CertiCoq.Plugin Require Import CertiCoq.
From MetaCoq.SafeChecker Require Import Loader.
From MetaCoq.Erasure Require Import Loader.

Require Import Arith PArith List String Ascii.
Require Import ExtLib.Data.String.

Import ListNotations. 

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

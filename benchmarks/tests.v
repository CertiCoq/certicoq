Require Import Arith List String.
Require Import CertiCoq.Benchmarks.lib.vs.
Require Import CertiCoq.Benchmarks.lib.Binom.
Require Import CertiCoq.Benchmarks.lib.Color.
Require Import CertiCoq.Benchmarks.lib.sha256.

From CertiCoq.Plugin Require Import CertiCoq.

Open Scope string.

Import ListNotations.
Import VeriStar.

CertiCoq -help.

CertiCoq Generate Glue -file "basics" [ nat, list, bool ].

(* Demo 1 *)

(* Definition demo1 := List.app (List.repeat true 500) (List.repeat false 300). *)
Definition demo1 := List.app (List.repeat true 10) (List.repeat false 10).

(* Demo 2 *)

Fixpoint repeat2 {A : Type} (x y : A) (n : nat) :=
  match n with
  | 0 => []
  | S n => x :: y :: repeat2 x y n
  end.

Definition demo2 := List.map negb (repeat2 true false 100).

(* Demo 3 *)

Definition demo3 := andb.

(* List sum *)

Definition list_sum := List.fold_left plus (List.repeat 1 100) 0.

(* Veristar *)

Definition vs_easy :=
  (fix loop (n : nat) (res : veristar_result) :=
     match n with
     | 0 =>
       match res with
       | Valid => true
       | _ => false
       end
     | S n =>
       let res := check_entailment example_ent in
       loop n res
     end) 100  Valid.

Definition vs_hard :=
  match vs.main_h with
  | Valid => true
  | _ => false
  end.

(* Binom *)

Definition binom := Binom.main.

(* Color *)
Definition color := Color.main.

(* Sha *)

(* From the Coq website *)
Definition test := "Coq is a formal proof management system. It provides a formal language to write mathematical definitions, executable algorithms and theorems together with an environment for semi-interactive development of machine-checked proofs. Typical applications include the certification of properties of programming languages (e.g. the CompCert compiler certification project, the Verified Software Toolchain for verification of C programs, or the Iris framework for concurrent separation logic), the formalization of mathematics (e.g. the full formalization of the Feit-Thompson theorem, or homotopy type theory), and teaching.".

Definition sha := sha256.SHA_256 (sha256.str_to_bytes test).

Definition sha_fast := sha256.SHA_256' (sha256.str_to_bytes test).

(* CertiCoq Show IR -time_anf binom. *)
(* CertiCoq Show IR -time_anf -O 1 -ext "_opt" binom. *)
(* CertiCoq Show IR -config 2 -direct -time_anf -ext "_inl" vs_easy. *)
(* CertiCoq Show IR -config 2 -direct -O 1 -time_anf -ext "_opt_no_inl" vs_easy. *)

(*
Eval compute in "Compiling demo1".

CertiCoq Compile -O 0 demo1.
(*CertiCoq Compile -O 0 -cps -ext "_cps" demo1.*)
CertiCoq Compile -ext "_opt" demo1.
(*CertiCoq Compile -cps -ext "_cps_opt" demo1.
CertiCoq Compile -args 1000 -config 9 -O 1 -ext "_opt_ll" demo1.*)

Eval compute in "Compiling demo2".

CertiCoq Compile -O 0 demo2.
(*CertiCoq Compile -O 0 -cps -ext "_cps" demo2.*)
CertiCoq Compile -ext "_opt" demo2.
(*CertiCoq Compile -cps -ext "_cps_opt" demo2.
CertiCoq Compile -args 1000 -config 9 -O 1 -ext "_opt_ll" demo2.*)

Eval compute in "Compiling demo3".

CertiCoq Compile -O 0 demo3.
(*CertiCoq Compile -O 0 -cps -ext "_cps" demo3.*)
CertiCoq Compile -ext "_opt" demo3.
(*CertiCoq Compile -cps -ext "_cps_opt" demo3.
CertiCoq Compile -args 1000 -config 9 -O 1 -ext "_opt_ll" demo3.*)

Eval compute in "Compiling list_sum".

CertiCoq Compile -O 0 list_sum.
(*CertiCoq Compile -O 0 -cps -ext "_cps" list_sum.*)
CertiCoq Compile -ext "_opt" list_sum.
(*CertiCoq Compile -cps -ext "_cps_opt" list_sum.
CertiCoq Compile -args 1000 -config 9 -O 1 -ext "_opt_ll" list_sum.*)
*)

Eval compute in "vs_easy".
CertiCoq Compile -O 0 -time vs_easy.
Eval compute in "vs_hard".
CertiCoq Compile -O 0 -time vs_hard.
Eval compute in "binom".
CertiCoq Compile -O 0 -time binom.
Eval compute in "color".
CertiCoq Compile -O 0 -time color.
Eval compute in "sha".
CertiCoq Compile -O 0 -time sha.

Eval compute in "extreme currying".
Definition extreme_uncurrying
  (a b c d e f g h i j k l m n o p q r s t u v w x y z
  (*a0 b0 c0 d0 e0 f0 g0 h0 i0 j0 k0 l0 m0 n0 o0 p0 q0 r0 s0 t0 u0 v0 w0 x0 y0 z0
  a1 b1 c1 d1 e1 f1 g1 h1 i1 j1 k1 l1 m1 n1 o1 p1 q1 r1 s1 t1 u1 v1 w1 x1 y1 z1
  a2 b2 c2 d2 e2 f2 g2 h2 i2 j2 k2 l2 m2 n2 o2 p2 q2 r2 s2 t2 u2 v2 w2 x2 y2 z2
  a3 b3 c3 d3 e3 f3 g3 h3 i3 j3 k3 l3 m3 n3 o3 p3 q3 r3 s3 t3 u3 v3 w3 x3 y3 z3
  a4 b4 c4 d4 e4 f4 g4 h4 i4 j4 k4 l4 m4 n4 o4 p4 q4 r4 s4 t4 u4 v4 w4 x4 y4 z4
  a5 b5 c5 d5 e5 f5 g5 h5 i5 j5 k5 l5 m5 n5 o5 p5 q5 r5 s5 t5 u5 v5 w5 x5 y5 z5*) : nat)
  : nat
:=
  a+b+c+d+e+f+g+h+i+j+k+l+m+n+o+p+q+r+s+t+u+v+w+x+y+z+
  a0+b0+c0+d0+e0+f0+g0(*+h0+i0+j0+k0+l0+m0+n0+o0+p0+q0+r0+s0+t0+u0+v0+w0+x0+y0+z0+
  a1+b1+c1+d1+e1+f1+g1+h1+i1+j1+k1+l1+m1+n1+o1+p1+q1+r1+s1+t1+u1+v1+w1+x1+y1+z1+
  a2+b2+c2+d2+e2+f2+g2+h2+i2+j2+k2+l2+m2+n2+o2+p2+q2+r2+s2+t2+u2+v2+w2+x2+y2+z2+
  a3+b3+c3+d3+e3+f3+g3+h3+i3+j3+k3+l3+m3+n3+o3+p3+q3+r3+s3+t3+u3+v3+w3+x3+y3+z3+
  a4+b4+c4+d4+e4+f4+g4+h4+i4+j4+k4+l4+m4+n4+o4+p4+q4+r4+s4+t4+u4+v4+w4+x4+y4+z4+
  a5+b5+c5+d5+e5+f5+g5+h5+i5+j5+k5+l5+m5+n5+o5+p5+q5+r5+s5+t5+u5+v5+w5+x5+y5+z5*).
CertiCoq Compile -O 0 -time extreme_uncurrying.

(*
Eval compute in "Compiling vs_easy".

(*CertiCoq Compile -O 0 -cps -ext "_cps" -time_anf vs_easy.*)
CertiCoq Compile -O 0 -time_anf vs_easy.
CertiCoq Compile -ext "_opt" vs_easy.
(*CertiCoq Compile -time -cps -ext "_cps_opt" vs_easy.
CertiCoq Compile -args 1000 -config 9 -O 1 -ext "_opt_ll" vs_easy.*)

Eval compute in "Compiling vs_hard".

CertiCoq Compile -O 0 vs_hard.
(*CertiCoq Compile -O 0 -cps -ext "_cps" vs_hard.*)
CertiCoq Compile -ext "_opt" vs_hard.
(*CertiCoq Compile -cps -ext "_cps_opt" vs_hard.
CertiCoq Compile -args 1000 -config 9 -O 1 -ext "_opt_ll" vs_hard.*)


Eval compute in "Compiling binom".

CertiCoq Compile -O 0 binom.
(*CertiCoq Compile -O 0 -cps -ext "_cps" binom.*)
CertiCoq Compile -ext "_opt" binom.
(*CertiCoq Compile -cps -ext "_cps_opt" binom.
CertiCoq Compile -args 1000 -config 9 -O 1 -ext "_opt_ll" binom.*)

Eval compute in "Compiling color".

CertiCoq Compile -O 0 -time color.
(*CertiCoq Compile -O 0 -time -cps -ext "_cps" color.*)
CertiCoq Compile -time -ext "_opt" color.
(*CertiCoq Compile -time -cps -ext "_cps_opt" color.
CertiCoq Compile -args 1000 -config 9 -O 1 -ext "_opt_ll" color.

(* Don't compile slow sha *)
(* Eval compute in "Compiling sha". *)

(* CertiCoq Compile -cps -ext "_cps" sha. *)
(* CertiCoq Compile sha. *)
(* CertiCoq Compile -O 1 -cps -ext "_cps_opt" sha. *)
(* CertiCoq Compile -O 1 -ext "_opt" sha. *)

Eval compute in "Compiling sha_fast".

CertiCoq Compile -O 0 sha_fast.
CertiCoq Compile -O 0 -cps -ext "_cps" sha_fast.
CertiCoq Compile -ext "_opt" sha_fast.
CertiCoq Compile -cps -ext "_cps_opt" sha_fast.
CertiCoq Compile -args 1000 -config 9 -O 1 -ext "_opt_ll" sha_fast.
*)
*)

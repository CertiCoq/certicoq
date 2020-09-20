(* Compile Binom, Color, Veristar, and SHA through Certicoq

Time CertiCoq should only be used for T0 or T1 
(Since T2 does *)
From CertiCoq Require Import CertiCoq.
(* Unset Template Cast Propositions. *)

(*From CertiCoq.Compiler Require Import pipeline.*)
(* currently bugged. 
  CertiCoq Compile -debug -time -direct lbox_pipeline. *)

(* BINOM *)
Require Import CertiCoq.Benchmarks.lib.Binom.
(* Time Extraction "bench_binom.ml" main.   *)
Time CertiCoq Compile main.

(* Color *)
Require Import CertiCoq.Benchmarks.lib.Color.
(* Time Extraction "bench_color.ml" main.  *)
(* Stack overflows? Time CertiCoq Compile -time -debug main. *)

(* VS*)
Require Import CertiCoq.Benchmarks.lib.vs.
(* Time Extraction "bench_vs.ml" main_h.  *)
Time CertiCoq Compile -time -direct main_h.

(* SHA256 *)
Require Import CertiCoq.Benchmarks.lib.sha256.
Require Import String.
Open Scope string_scope.

Definition compute_sha (m:String.string) :=  (SHA_256 (sha256.str_to_bytes m)). 


Definition test500 := "The Secure Hash Algorithm is a family of cryptographic hash functions published by the National Institute of Standards and Technology (NIST) as a U.S. Federal Information Processing Standard (FIPS)The Secure Hash Algorithm is a family of cryptographic hash functions published by the National Institute of Standards and Technology (NIST) as a U.S. Federal Information Processing Standard (FIPS)The Secure Hash Algorithm is a family of cryptographic hash functions published by the National Institute ".

Definition test200 := "The Secure Hash Algorithm is a family of cryptographic hash functions published by the National Institute of Standards and Technology (NIST) as a U.S. Federal Information Processing Standard (FIPS)".

Definition benchsha := compute_sha test200.

(*  Time Extraction "bench_sha.ml" benchsha. *)  
Time CertiCoq Compile -time benchsha.

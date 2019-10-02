(* Compile Binom, Color, Veristar, and SHA through Certicoq

Time CertiCoq should only be used for T0 or T1 *)
From CertiCoq Require Import CertiCoq.
(* Unset Template Cast Propositions. *)


(* BINOM *)
Require Import CertiCoq.Benchmarks.Binom.
Time Extraction "bench_binom.ml" main.  
Time CertiCoq Compile main.

(* VS*)
Require Import CertiCoq.Benchmarks.vs.
Time Extraction "bench_vs.ml" main_h.  
Time CertiCoq Compile main_h. 

(* Color *)
Require Import CertiCoq.Benchmarks.Color.
Time Extraction "bench_color.ml" main.  
Time CertiCoq Compile main.
 
(* SHA256 *)
Require Import CertiCoq.Benchmarks.sha256.
Require Import String.
Open Scope string_scope.

Definition compute_sha (m:String.string) :=  (SHA_256 (sha256.str_to_bytes m)). 


Definition test500 := "The Secure Hash Algorithm is a family of cryptographic hash functions published by the National Institute of Standards and Technology (NIST) as a U.S. Federal Information Processing Standard (FIPS)The Secure Hash Algorithm is a family of cryptographic hash functions published by the National Institute of Standards and Technology (NIST) as a U.S. Federal Information Processing Standard (FIPS)The Secure Hash Algorithm is a family of cryptographic hash functions published by the National Institute ".

Definition test200 := "The Secure Hash Algorithm is a family of cryptographic hash functions published by the National Institute of Standards and Technology (NIST) as a U.S. Federal Information Processing Standard (FIPS)".

 

Definition benchsha := compute_sha test200.
Time Extraction "bench_sha.ml" benchsha.  
Time CertiCoq Compile benchsha.


Require Import Arith List.

Import ListNotations.
  
From CertiCoq.Plugin Require Import CertiCoq.

(* **

Flags:

0 : C code uses args + default pipeline
1 : C code uses args and argv optimization + default pipeline
2 : Old C code generators + default pipeline 
3 : Old C code generators with argv optimization + default pipeline 
4 : C code uses args + lambda lifting pipeline
5 : C code uses args and argv optimization + lambda lifting pipeline
6 : Old C code generator + lambda lifting pipeline
7 : Old C code generator with argv optimization + lambda lifting pipeline
8 :  Old C code generator + old pipeline

**)


(* Definition demo0 := List.app [true; false] [true]. *)
(* Definition demo0_cps := List.app [true; false] [true]. *)

(* CertiCoq Compile ANF Opt 0 demo0. *)
(* CertiCoq Compile Opt 0 demo0_cps. *)

Definition demo1 := List.app (List.repeat true 5) (List.repeat false 4).
Definition demo1_cps := List.app (List.repeat true 5) (List.repeat false 4).

CertiCoq Show L6 Opt 1 demo1.

CertiCoq Compile ANF Opt 0 demo1.
CertiCoq Compile Opt 0 demo1_cps.

(* Definition demo2 := (negb, List.hd_error). *)
Definition demo2 := List.map negb [true; false; true].
Definition demo2_cps := List.map negb [true; false; true].

CertiCoq Compile ANF Opt 0 demo2.
CertiCoq Compile Opt 0 demo2_cps.

Definition add := 10*10*10*7*2*10 + 4.
Definition add_cps := 10*10*10*7*2*10 + 4.

CertiCoq Compile Opt 0 add_cps.
CertiCoq Compile ANF Opt 0 add.


(* Definition lala := List.map (fun x => 1 + x) (List.repeat 10 10000). *)
(* Definition test1_opt := List.map (fun x => 1 + x) (List.repeat 10 10000). *)


(* CertiCoq Compile lala. *)
(* CertiCoq Compile Opt test1_opt. *)


(* an out of generations with (100 * 100 * 100 * 100 * 100) *)
Fixpoint list_add y z w l : nat :=
  match l with
  | nil => 0%nat
  | x::xs =>
    let clos r := (y + z + w + r)%nat in
    x + list_add y z w xs
  end.

Fixpoint loop n (f : Datatypes.unit -> nat) : nat :=
  match n with
  | 0%nat => f tt
  | S n => f tt + loop n f
  end.
    
(* Definition clos := (loop 3 (fun _ => list_add (* 0 0 0 *) (List.repeat 2%nat 3))%nat). *)
(* Definition clos_old := (loop 3 (fun _ => list_add (* 0 0 0 *) (List.repeat 2%nat 3))%nat). *)

(* XXX weird performance *)
(* 
Definition clos_loop (u : unit) : nat :=
  (fix list_add y z w u k m n k1 k2 k3 k4 k5 l : nat :=
     match l with
     | [] => 0
     | x::xs =>
       let clos z := x + z + w + u + k + m + n + y + k1 + k2 + k3 + k4 + k5 in
       (clos x) + (clos 0) + list_add y z w u k m n k1 k2 k3 k4 k5 xs
     end) 0 0 0 0 0 0 0 0 0 0 0 0 (List.repeat 0 (100*1000)).
Definition clos := loop (100*10) clos_loop.
*)

(* Definition clos_loop (u : unit) : nat := *)
(*   (fix list_add y z w u k l : nat := *)
(*      match l with *)
(*      | [] => 0 *)
(*      | x::xs => *)
(*        let clos z := x + z + w + u + k  in *)
(*        (clos x) + (clos 0) + list_add y z w u k xs *)
(*      end) 0 0 0 0 0 (List.repeat 0 (100*1000)). *)

Definition clos_loop (u : unit) : nat :=
  (fix list_add y z w u k m n k1 k2 k3 k4 k5 l : nat :=
     match l with
     | [] => 0
     | x::xs =>
       let clos z := x + z + w + u + k + m + n + y + k1 + k2 + k3 + k4 + k5 in
       (clos x) + list_add y z w u k m n k1 k2 k3 k4 k5 xs
     end) 0 0 0 0 0 0 0 0 0 0 0 0 (List.repeat 0 (100*1000)).



(* Fixpoint loop n (f : unit -> nat) : nat := *)
(*   match n with *)
(*   | 0 => f tt *)
(*   | S n => f tt + loop n f *)
(*   end. *)
    
Definition clos := loop (100*10) clos_loop.
Definition clos_opt := loop (100*10) clos_loop.
Definition clos_old := loop (100*10) clos_loop.

(* Definition clos := loop (100*100*10) clos_loop. *)
(* Definition clos_opt := loop (100*100*10) clos_loop. *)
(* Definition clos_old := loop (100*100*10) clos_loop. *)

(* Definition res := Eval native_compute in clos. *)

(* Definition clos := 1. *)
(* Definition clos_opt := 2. *)
(* Definition clos_old := 3. *)

CertiCoq Compile ANF Opt 0 clos.
CertiCoq Compile ANF Opt 1 clos_opt.
(* CertiCoq Compile ANF Opt 1 clos_opt. *)
CertiCoq Compile Opt 0 clos_old.

(* In this clos should be lambda lifted and the environment should not be constructed in every iteration of the loop *)
(* Time saved:
   1. Closure construction upon each rec. call. Check if that works.
   2. Projection out of the env every time clos is called. This does not show in this example,
      and maybe needs invariant argument optimization. 
*)
(* Definition clos_opt (u : unit) := *)
(*   (fix list_add y z w u k m n k1 k2 k3 k4 k5 l := *)
(*      match l with *)
(*      | [] => [] *)
(*      | x::xs => *)
(*        let clos z := x + z + w + u + k + m + n + y + k1 + k2 + k3 + k4 + k5 in *)
(*        (clos x) :: list_add y z w u k m n k1 k2 k3 k4 k5 xs *)
(*      end) 1 2 3 4 3 2 1 2 3 4 5 6 (List.repeat 10 (100 * 100 * 50)). *)



From CertiCoq.Benchmarks Require Import vs.

Import VeriStar.

Definition is_valid :=
  match main_h with
  | Valid => true
  | _ => false
  end.

Definition is_valid_opt :=
  match main_h with
  | Valid => true
  | _ => false
  end.

Definition is_valid_old :=
  match main_h with
  | Valid => true
  | _ => false
  end.

(* CertiCoq Show L6 Opt 0 is_valid. *)

Time CertiCoq Compile ANF Opt 0 is_valid. (* 5 secs ! *)

Time CertiCoq Compile ANF Opt 1 is_valid_opt. (* 5 secs ! *)

Time CertiCoq Compile Opt 0 is_valid_old. (* 5 secs ! *)

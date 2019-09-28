Require Import Arith List.

Import ListNotations.
  
From CertiCoq.Plugin Require Import CertiCoq.


Definition demo1 := List.app (List.repeat true 5) (List.repeat false 3).

CertiCoq Compile demo1.

Definition demo2 := (negb, List.hd_error).

CertiCoq Compile demo2.


Definition test1 := List.map (fun x => 1 + x) (List.repeat 10 10000).
Definition test1_opt := List.map (fun x => 1 + x) (List.repeat 10 10000).

CertiCoq Compile test1.
CertiCoq Compile Opt test1_opt.

(* an out of generations with (100 * 100 * 100 * 100 * 100) *)

Definition clos_loop (u : unit) : nat :=
  (fix list_add y z w u k m n k1 k2 k3 k4 k5 l : nat :=
     match l with
     | [] => 0
     | x::xs =>
       let clos z := x + z + w + u + k + m + n + y + k1 + k2 + k3 + k4 + k5 in
       (clos x) + list_add y z w u k m n k1 k2 k3 k4 k5 xs
     end) 0 0 0 0 0 0 0 0 0 0 0 0 (List.repeat 0 (100*1000)).


Fixpoint loop n (f : unit -> nat) : nat :=
  match n with
  | 0 => f tt
  | S n => f tt + loop n f
  end.
    
Definition clos := loop (100*10) clos_loop.
Definition clos_opt := loop (100*10) clos_loop.

CertiCoq Compile clos.
CertiCoq Compile Opt clos_opt.


(* In this clos should be lambda lifted and the environment should not be constructed in every iteration of the loop *)
(* Time saved:
   1. Closure construction upon each rec. call. Check if that works.
   2. Projection out of the env every time clos is called. This does not show in this example,
      and maybe needs invariant argument optimization. 
*)
Definition clos_opt (u : unit) :=
  (fix list_add y z w u k m n k1 k2 k3 k4 k5 l :=
     match l with
     | [] => []
     | x::xs =>
       let clos z := x + z + w + u + k + m + n + y + k1 + k2 + k3 + k4 + k5 in
       (clos x) :: list_add y z w u k m n k1 k2 k3 k4 k5 xs
     end) 1 2 3 4 3 2 1 2 3 4 5 6 (List.repeat 10 (100 * 100 * 50)).




Fixpoint 



- recursive closure



  
  (fun x y =>


From CertiCoq.Benchmarks Require Import vs.
Import VeriStar.
Definition is_valid :=
  match main with
  | Valid => true
  | _ => false
  end.

Time CertiCoq Compile is_valid. (* 5 secs ! *)

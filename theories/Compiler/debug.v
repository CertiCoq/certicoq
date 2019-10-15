Require Export Common.certiClasses.
Require Export Common.certiClasses2.
Require Export L1g.instances.
Require Export L2k.instances.
Require Export L4.instances.
Require Export L6.instances L6.cps_show L6.state L6.closure_conversion2.
Require Import Compiler.allInstances.
(* Require Export L7.Clightexec. *)


Open Scope Z_scope.
Require Import ZArith.


Require Import Common.Common.
Require Import String.
Open Scope string_scope.
Require Import  maps_util.

Import ListNotations.

Instance fuel : utils.Fuel := { fuel := 2 ^ 14 }.


Definition compile_L6_show (opt : bool) (e: Ast.global_declarations * Ast.term) : (string * cps.exp) :=  
  match (translateTo (cTerm certiL5) (Flag 0) e) with
  | Ret p =>
    match L5_to_L6.convert_top default_cTag default_iTag fun_fTag kon_fTag p with
    | Some r =>
      let '(c_env, n_env, f_env, next_cTag, next_iTag, e) := r in
      (* make compilation state *)
      let c_data :=
          let next_var := ((identifiers.max_var e 1) + 1)%positive in
          let next_fTag := M.fold (fun cm => fun ft => fun _ => Pos.max cm ft) f_env 1 + 1 in
          pack_data next_var next_cTag next_iTag next_fTag c_env f_env n_env nil
      in
      (* uncurring *)
      let '(e, s, c_data) := uncurry.uncurry_fuel 100 (shrink_cps.shrink_top e) c_data in
      (* inlining *)
      let (e, c_data) := beta_contraction.inline_uncurry e s 10 10 c_data in
      (* Shrink reduction      *)
      let e := shrink_cps.shrink_top e in
      (* lambda lifting *)
      let (e, c_data) := lambda_lifting.lambda_lift' e c_data in
      (* Shrink reduction *)
      let e := shrink_cps.shrink_top e in
      (* (* Closure conversion *) *)
      (* let '(mkCompData next ctag itag ftag cenv fenv names log) := c_data in *)
      (* let '(cenv', names', e) := *)
      (*     closure_conversion.closure_conversion_hoist bogus_cloTag e ctag itag cenv names in *)
      (* let c_data := *)
      (*     let next_var := ((identifiers.max_var e 1) + 1)%positive in *)
      (*     pack_data next_var ctag itag ftag (add_cloTag bogus_cloTag bogus_cloiTag cenv') fenv names' log *)
      (* in *)
      (* Closure conversion *)
      let (e, c_data) := closure_conversion2.closure_conversion_hoist bogus_cloTag (* bogus_cloiTag *) e c_data in
      let '(mkCompData next ctag itag ftag cenv fenv names log) := c_data in
      let c_data :=
          let next_var := ((identifiers.max_var e 1) + 1)%positive in
          pack_data next_var ctag itag ftag (cps.add_cloTag bogus_cloTag bogus_cloiTag cenv) fenv  (add_binders_exp names e) log
      in
      (* Shrink reduction *)
      let e := shrink_cps.shrink_top e in
      (* (* Dead parameter elimination *) *)
      (* (* let e := dead_param_elim.eliminate e in *) *)
      (* (* Shrink reduction *) *)
      (* let e := shrink_cps.shrink_top e in *)
      let 'mkCompData _ _ _ _ cenv _ nenv log := c_data in
      ((cps_show.show_exp nenv cenv false e ++ state.newline ++ log_to_string log)%string, e)
    | None => ("Failed to compile to L6", cps.Ehalt 1%positive)
    end
  | Exc s => (s, cps.Ehalt 1%positive)
  end.

Definition test_pipeline  (e: Ast.global_declarations * Ast.term) :=
  match (translateTo (cTerm certiL5) (Flag 3) e) with
  | Ret p => 
    match L6_pipeline p with 
    | Ret ((_, cenv, nenv, _),  (_, e)) => cps_show.show_exp nenv cenv false e
    | Exc s => s
    end
  | Exc s => s
  end.

(* Quote Recursively Definition demo1 := (List.app (List.repeat true 5) (List.repeat false 3)). *)

(* Definition demo1_L6 := Eval native_compute in (compile_L6_show false demo1). *)

(* Definition demo1_fv := Eval native_compute in (identifiers.exp_fv (snd demo1_L6)). *)

(* Quote Recursively Definition demo1' := (List.repeat false 3). *)

(* Definition demo1'_L6 := Eval native_compute in (compile_L6_show false demo1'). *)

(* Quote Recursively Definition demo1 := (List.app (List.repeat true 5) (List.repeat false 3)). *)

(* Definition demo1_L6 := Eval native_compute in (compile_L6_show false demo1). *)

(* Print demo1_L6. *)

Fixpoint list_add y z w l : nat :=
  match l with
  | nil => 0%nat
  | x::xs =>
    let clos r := (y + z + w + r)%nat in
    (clos x) + list_add y z w xs
  end.



Fixpoint loop n (f : Datatypes.unit -> nat) : nat :=
  match n with
  | 0%nat => f tt
  | S n => f tt + loop n f
  end.
    
Quote Recursively Definition clos := (loop 3 (fun _ => list_add 0 0 0 (List.repeat 0%nat 3))%nat).

Definition clos_cL6 := Eval native_compute in (test_pipeline clos).

Definition clos_L'6 := Eval native_compute in (compile_L6_show false clos).


Definition add_off (l : list nat) (off : nat) :=
  let fix aux l acc :=
      match l with
      | nil => acc
      | x :: xs =>
        aux xs (x + off)%nat
      end in aux l 0%nat.

Quote Recursively Definition rec_clos:= (add_off [1;2;3]%nat 3).

Definition rec_clos_cL6 := Eval native_compute in (test_pipeline rec_clos).

Definition rec_clos_cL6' := Eval native_compute in (compile_L6_show false rec_clos).

Print clos_L6.

Definition print_C_program (opt : nat) (p : Ast.program) :=
  match compile_template_L7 0 clos with
  | Ret ((e, _), p) => (M.elements e, Ctypes.prog_defs p)
  | _ => (nil, nil)
  end.

Definition print_name_env (opt : nat) (p : Ast.program) :=
  match compile_template_L7 0 clos with
  | Ret ((e, _), _) => M.elements e
  | _ => nil
  end.

Definition clos_L7 := Eval native_compute in (print_C_program 0 clos).
 
Print clos_L7.

Definition clos_env := Eval native_compute in (fst clos_L7).

Set Printing Depth 10000. 

Print clos_env.


Definition repeat_fun :=
  Eval native_compute in (filter (fun (e : AST.ident * _) => (fst e) =? 730%positive) (snd clos_L7), fst clos_L7). 

Definition clos_L6_opt := Eval native_compute in (compile_L6_show true clos).
 
Print clos_L6_opt.

Import ListNotations.

Fixpoint list_add' y z w l : nat :=
  match l with
  | nil => 0%nat
  | x::xs =>
    let fix clos l : nat :=
        match l with
        | nil => (y + z + w)%nat
        | x :: l => (clos l + x)%nat
        end
    in 
    (clos [x; x]) + list_add y z w xs
  end.

    
Quote Recursively Definition clos' := (loop 3 (fun _ => list_add' 0 0 0 (List.repeat 0%nat 3))%nat).
 
Definition clos_L6' := Eval native_compute in (compile_L6_show clos').

Print clos_L6'.

Let m :=  Eval native_compute in (M.set 1 34 (M.empty _)).

Fixpoint tail (x y : nat) :=
  match x with
  | O => y
  | S x' =>
    let fix my_add x y :=
        match x with
        | O => y
        | S x => my_add x (S y)
        end
    in let y' := my_add y 3%nat in tail x' y'
  end.

Quote Recursively Definition test_tail := (tail 1 2). 
Definition tail_c := Eval native_compute in (compile_L6_show test_tail).


  (List.app (List.repeat true 5) (List.repeat false 3)).

Quote Recursively Definition demo1 := (List.app (List.repeat true 5) (List.repeat false 3)).

(* XXX :   fun loop_uncurried_lifted_780(env_950,k_622,f_623,n_624,add_uncurried_695) := 
add_uncarried should not be lambda lifted
 *)

(* XXX

letrec [
 fun x164(k_166,x165) := 
   k_166(x164)
] in

 Is not reduced by shrink reduction

*)

(* -> list_add_uncurried_601 is never inlined *)

Definition demo1_L6 := Eval native_compute in (compile_L6_show demo1).

Print demo1_L6.

Fixpoint my_add x y :=
  match x with
  | O => y
  | S x => S (my_add x y)
  end.


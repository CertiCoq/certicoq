Require Import Common.Pipeline_utils Common.compM Common.
Require Import L1g.toplevel.
Require Import L2k.toplevel.
Require Import L4.toplevel.
Require Import L6.toplevel L6.cps_show L6.state Compiler.pipeline maps_util.
Require Import ExtLib.Structures.Monad Strings.String.

Import MonadNotation.
Open Scope monad_scope.

Open Scope Z_scope.
Require Import ZArith.

Definition compile_to_L4 (p : Template.Ast.program) :=
  p <- compile_L1g p ;;
  p <- compile_L2k p ;;
  p <- compile_L2k_eta p ;;
  compile_L4 p.

Definition debug_CPS (p : Template.Ast.program) :=
  p <- compile_L1g p ;;
  p <- compile_L2k p ;;
  p <- compile_L2k_eta p ;;
  p <- compile_L4 p ;;
  p <- compile_L4_2 p ;;
  p <- compile_L4_5 p ;;
  p <- compile_L5 p ;;
  p <- compile_L6_CPS p ;;
  L6_trans p.

Definition debug_ANF (p : Template.Ast.program) :=
  p <- compile_L1g p ;;
  p <- compile_L2k p ;;
  p <- compile_L2k_eta p ;;
  p <- compile_L4 p ;;
  p <- compile_L6_ANF p ;;
  L6_trans p.


Definition compile_L6_show (e: Template.Ast.program) : string  :=
  match run_pipeline _ _ default_opts e debug_CPS with
  | (compM.Ret (pr, cenv, vtag, itag, nenv, fenv, rho, term), _) =>
    cps_show.show_exp nenv cenv false term
  | (compM.Err s, _) => s
  end.

Definition compile_L6_ANF_show (e: Template.Ast.program) : string  :=
  match run_pipeline _ _ default_opts e debug_ANF with
  | (compM.Ret (pr, cenv, vtag, itag, nenv, fenv, rho, term), _) =>
    cps_show.show_exp nenv cenv false term
  | (compM.Err s, _) => s
  end.

Definition compile_L4_AST (e: Template.Ast.program) : error L4.expression.exp :=
  match run_pipeline _ _ default_opts e compile_to_L4 with
  | (compM.Ret (ienv, term), _) => compM.Ret term
  | (compM.Err s, _) => compM.Err s
  end.


Quote Recursively Definition demo1 := (List.app (List.repeat true 5) (List.repeat false 3)).

(* Definition demo1_CPS := Eval native_compute in (compile_L6_show demo1). *)
Definition demo1_ANF := Eval native_compute in (compile_L6_ANF_show demo1).
Definition demo1_CPS := Eval native_compute in (compile_L6_show demo1).
Definition demo1_L4 := Eval native_compute in (compile_L4_AST demo1).

(* (* experimenting -- take out later *) *)
(* Require Import L6.L4_to_L6 L6.cps L6.eval L4.exp_eval. *)

(* Definition demo2_L4 := Eval native_compute in (compile_L4_show demo2). *)
(* Definition demo4_L4 := Eval native_compute in (compile_L4_show demo4).  *)

(* Definition test_eval := demo4_L4. *)

(* Definition test := *)
(*   match test_eval with *)
(*   | compM.Ret (ienv, p) => (ienv, p) *)
(*   | compM.Err s => (nil, L4.expression.Prf_e) *)
(*   end. *)

(* Definition test_result := *)
(*   let (ienv, e) := test in *)
(*   let '(_, cenv, ctag, itag,  dcm) := convert_env ienv in *)
(*   let f := (100%positive) in *)
(*   let k := (101%positive) in *)
(*   let x := (102%positive) in *)
(*   match (cps_cvt e nil k (SG (103%positive, n_empty)) dcm) with *)
(*   | Some (e', sg) => *)
(*     match sg with *)
(*       SG (next, nenv) => *)
(*       let fenv : fun_env := M.set func_tag (2%N, (0%N::1%N::nil)) *)
(*                                (M.set kon_tag (1%N, (0%N::nil)) (M.empty _) ) in *)
(*       let pr := cps.M.empty (list val -> option val) in *)
(*       (* let fenv := cps.M.empty fun_ty_info in  *) *)
(*       (* let cont := (cps.Efun *) *)
(*       (*               (Fcons f kon_tag (k::nil) e' *) *)
(*       (*                      (Fcons k kon_tag (x::nil) (Ehalt x) Fnil)) *) *)
(*       (*               (cps.Eapp f kon_tag (k::nil))) in *) *)
(*       let cont := (Fcons k kon_tag (x::nil) (Ehalt x) Fnil) in *)
(*       let env := cps.M.empty val in *)
(*       let env' := def_funs cont cont env env in *)
(*       print_BigStepResult_L6 ((pr, cenv, nenv, fenv), (env', e')) 60%nat *)
(*     end *)
(*   | None => *)
(*     L7.L6_to_Clight.print ("Failed during comp_L6") *)
(*   end. *)

(* Definition test_eval_res (L4term : L3_to_L4.ienv * expression.exp) := *)
(*   let (ienv, e) := L4term in *)
(*   match eval_env_f 100 nil e with *)
(*   | Some v => v *)
(*   | None => Prf_v *)
(*   end.  *)

(* Definition L4_eval := Eval native_compute in (test_eval_res test). *)

(* Definition test_result_val := *)
(*   let (ienv, e) := test in *)
(*   let '(_, cenv, ctag, itag,  dcm) := convert_env ienv in *)
(*   let f := (100%positive) in *)
(*   let k := (101%positive) in *)
(*   let x := (102%positive) in *)
(*   match eval_env_f 20 nil e with *)
(*   | Some v => *)
(*     match cps_cvt_val v (SG (103%positive, n_empty)) dcm with *)
(*     | Some (v', sg) => *)
(*       match sg with *)
(*         SG (next, nenv) => *)
(*         let fenv : fun_env := M.set func_tag (2%N, (0%N::1%N::nil)) *)
(*                                (M.set kon_tag (1%N, (0%N::nil)) (M.empty _) ) in *)
(*         let pr := cps.M.empty (list val -> option val) in *)
(*         let cont := (Fcons k kon_tag (x::nil) (Ehalt x) Fnil) in *)
(*         match v' with *)
(*         | Vfun env _ _ => *)
(*           let env' := def_funs cont cont env env in *)
(*           print_BigStepResult_L6Val ((pr, cenv, nenv, fenv), (env', v')) *)
(*         | _ =>  *)
(*           let env := cps.M.empty val in *)
(*           let env' := def_funs cont cont env env in *)
(*           print_BigStepResult_L6Val ((pr, cenv, nenv, fenv), (env', v')) *)
(*         end *)
(*       end *)
(*     | None => *)
(*       L7.L6_to_Clight.print ("Failed during cps_cvt_val_L6") *)
(*     end *)
(*   | None => *)
(*     L7.L6_to_Clight.print ("Failed during eval_env") *)
(*   end. *)

(* Require Import ExtrOcamlBasic. *)
(* Require Import ExtrOcamlString. *)
(* Require Import ExtrOcamlZInt. *)
(* Require Import ExtrOcamlNatInt. *)

(* Extract Inductive Decimal.int => *)
(* unit [ "(fun _ -> ())" "(fun _ -> ())" ] "(fun _ _ _ -> assert false)". *)

(* Extract Constant L6_to_Clight.print => *)
(* "(fun s-> print_string (String.concat """" (List.map (String.make 1) s)))". *)


(* Extract Constant   varImplDummyPair.varClassNVar => *)
(* " (fun f (p:int*bool) -> varClass0 (f (fst p)))". *)

(* Extraction "test1.ml" test_result. *)
(* Extraction "testval.ml" test_result_val. *) 

(* -- *)

Definition demo1_L6_anf := Eval native_compute in (compile_L6_anf_show false demo1).
Definition demo1_L6_init := Eval native_compute in (compile_anf_show false demo1).

Definition demo1_L6_opt := Eval native_compute in (compile_L6_show false demo1).
(* Definition p := Eval native_compute in (demo1_L6_anf ++ state.newline ++ demo1_L6_anf_opt)%string. *)
(* Print p. *)
         
Definition demo1_L6 := Eval native_compute in (compile_L6_show false demo1).

(* Definition demo1_fv := Eval native_compute in (identifiers.exp_fv (snd demo1_L6)). *)

(* Quote Recursively Definition demo1' := (List.repeat false 3). *)

(* Definition demo1'_L6 := Eval native_compute in (compile_L6_show false demo1'). *)

(* Quote Recursively Definition demo1 := (List.app (List.repeat true 5) (List.repeat false 3)). *)

(* Definition demo1_L6 := Eval native_compute in (compile_L6_show false demo1). *)

(* Print demo1_L6. *)

Fixpoint list_add y z w l : nat :=
  match l with
  | nil => 0%nat
  | (x, y) :: xs =>
    let clos r := (y + z + w + r)%nat in
    (clos x) + (clos y) + list_add y z w xs
  end.


Fixpoint loop n (f : Datatypes.unit -> nat) : nat :=
  match n with
  | 0%nat => f tt
  | S n => f tt + loop n f
  end.
    
Quote Recursively Definition clos := (loop 3 (fun _ => list_add 0 0 0 (List.repeat (0, 0) 3))%nat).

Definition clos_anf_init := Eval native_compute in (compile_anf_show false clos).

Definition clos_anf := Eval native_compute in  (compile_L6_anf_show false clos).
Definition clos_anf_opt := Eval native_compute in  (compile_L6_anf_show true clos).

Definition clos_L6 := Eval native_compute in (compile_L6_show false clos).


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


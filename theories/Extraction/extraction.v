Require compcert.common.AST
        compcert.common.Errors
        compcert.common.Values
        compcert.lib.Integers
        compcert.cfrontend.Cop
        compcert.cfrontend.Ctypes
        compcert.cfrontend.Clight
        compcert.cfrontend.Csyntax
        compcert.lib.Coqlib
        compcert.lib.Floats
        compcert.common.Globalenvs
        Int31.

Require L6.L5_to_L6
        L7.L6_to_Clight
        L7.Clightexec
        Compiler.allInstances.

(* Standard lib *)
Require Import ExtrOcamlBasic.
Require Import ExtrOcamlString ExtrOcamlZInt.

(* Coqlib *)
Extract Inlined Constant Coqlib.proj_sumbool => "(fun x -> x)".

(* L6_to_Clight *)
Extract Constant L6_to_Clight.print_Clight => "PrintClight.print_if".
Extract Constant L6_to_Clight.print_Clight_dest => "PrintClight.print_dest".
Extract Constant L6_to_Clight.print_Clight_dest_names' => "PrintClight.print_dest_names".
Extract Constant L6_to_Clight.print => "print_string".


(* Timing *)
(* T0 : No timing *)
(*
Extract Constant AstCommon.timePhase => "(fun c x -> x ())". 
*)

(* T1 : Time each phase, print to debug *)
(*
Extract Constant AstCommon.timePhase =>
"(fun c x -> let time = Unix.gettimeofday() in
                            let temp = x () in
                            let time = (Unix.gettimeofday() -. time) in
              Feedback.msg_debug (Pp.str (Printf.sprintf ""Time elapsed in %s:  %f"" ((fun s-> (String.concat """" (List.map (String.make 1) s))) c) time));
              temp)".
*)
(* T2 : Time each phase 10 times, print average to debug 
debug: Feedback.msg_debug (Pp.str (Printf.sprintf ""%f""  (Unix.gettimeofday() -. time)));   *)

(* Extract Constant AstCommon.timePhase => *)
(* "(fun c x -> let time = Unix.gettimeofday() in *)
(*              let temp = ref (x ()) in *)
(*              for i = 2 to 10 do  *)
(*               temp := x () *)
(*              done; *)
(*              let time = ((Unix.gettimeofday() -. time) /. 10.) in *)
(*               Feedback.msg_debug (Pp.str (Printf.sprintf ""Average time elapsed in %s:  %f"" ((fun s-> (String.concat """" (List.map (String.make 1) s))) c) time)); *)
(*               !temp)". *)






                                
        

(* TEMP STUFF *)
(* OS: This is now defined in allInstances
Extract Constant L6_to_Clight.allocIdent => "Camlcoq.P.of_int 28".
Extract Constant L6_to_Clight.limitIdent => "Camlcoq.P.of_int 29".
Extract Constant L6_to_Clight.argsIdent => "Camlcoq.P.of_int 26".
Extract Constant L6_to_Clight.gcIdent => "Camlcoq.P.of_int 80".
Extract Constant L6_to_Clight.mainIdent => "Camlcoq.P.of_int 81".
Extract Constant L6_to_Clight.bodyIdent => "Camlcoq.P.of_int 90".
Extract Constant L6_to_Clight.threadInfIdent => "Camlcoq.P.of_int 31".
Extract Constant L6_to_Clight.tinfIdent => "Camlcoq.P.of_int 91".
Extract Constant L6_to_Clight.heapInfIdent => "Camlcoq.P.of_int 95".
Extract Constant L6_to_Clight.numArgsIdent => "Camlcoq.P.of_int 97". *)


(* Int31 *)
Extract Inductive Int31.digits => "bool" [ "false" "true" ].
Extract Inductive Int31.int31 => "int" [ "Camlcoq.Int31.constr" ] "Camlcoq.Int31.destr".
Extract Constant Int31.twice => "Camlcoq.Int31.twice".
Extract Constant Int31.twice_plus_one => "Camlcoq.Int31.twice_plus_one".
Extract Constant Int31.compare31 => "Camlcoq.Int31.compare".
Extract Constant Int31.On => "0".
Extract Constant Int31.In => "1".

Extract Inductive Decimal.int => unit [ "(fun _ -> ())" "(fun _ -> ())" ] "(fun _ _ _ -> assert false)".

Extract Inlined Constant RandyPrelude.ascii_dec_bool => "(=)".

(* Avoid name clashes with OCaml or Coq module names *)
Extraction Blacklist List String Nat Int Ast univ uGraph Char OrderedType
           Instances Classes Term Monad Coqlib Errors Compile Checker.

(* Cutting the dependency to R. 
Extract Inlined Constant Fcore_defs.F2R => "fun _ -> assert false".
Extract Inlined Constant Fappli_IEEE.FF2R => "fun _ -> assert false".
Extract Inlined Constant Fappli_IEEE.B2R => "fun _ -> assert false".
Extract Inlined Constant Fappli_IEEE.round_mode => "fun _ -> assert false".
Extract Inlined Constant Fcalc_bracket.inbetween_loc => "fun _ -> assert false". *)

Cd "Extraction".
Separate Extraction
         Ctypes.merge_attributes Ctypes.remove_attributes Ctypes.build_composite_env
         Csyntax
         Ctypes.make_program
         AST.signature_main
(*         Floats.Float32.from_parsed Floats.Float.from_parsed
         Floats.Float32.of_bits Floats.Float.of_bits
         Floats.Float32.to_bits Floats.Float.to_bits *)
         String.length
         Compiler.allInstances.printProg
         Compiler.allInstances.compile_template_L7
         Compiler.allInstances.compile_template_L7_anf
         Compiler.allInstances.emit_L6_anf
         Compiler.allInstances.emit_L6_pre_cc
         Compiler.allInstances.emit_L6_cc
         L7.Clightexec.run. 
Cd "..".

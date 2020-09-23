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

Require L7.Clightexec
        Glue.glue
        Compiler.pipeline.

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

Extract Constant AstCommon.timePhase =>
"(fun c x -> let time = Unix.gettimeofday() in
                            let temp = x () in
                            let time = (Unix.gettimeofday() -. time) in
              Feedback.msg_debug (Pp.str (Printf.sprintf ""Time elapsed in %s:  %f"" ((fun s-> (String.concat """" (List.map (String.make 1) s))) c) time));
              temp)".

(* T2 : Time each phase 10 times, print average to debug
debug: Feedback.msg_debug (Pp.str (Printf.sprintf ""%f""  (Unix.gettimeofday() -. time)));   *)

(** **  Zoe : I'm commenting timing out for now because it blocks computation inside Coq when we want to test
              comp passes. TODO add compiler opt *)

(* Extract Constant AstCommon.timePhase => *)
(* "(fun c x -> let time = Unix.gettimeofday() in *)
(*              let temp = ref (x ()) in *)
(*              for i = 2 to 10 do *)
(*               temp := x () *)
(*              done; *)
(*              let time = ((Unix.gettimeofday() -. time) /. 10.) in *)
(*               Feedback.msg_debug (Pp.str (Printf.sprintf ""Average time elapsed in %s:  %f"" ((fun s-> (String.concat """" (List.map (String.make 1) s))) c) time)); *)
(*               !temp)". *)


(* Int31 *)
Extract Inductive Int31.digits => "bool" [ "false" "true" ].
Extract Inductive Int31.int31 => "int" [ "Camlcoq.Int31.constr" ] "Camlcoq.Int31.destr".
Extract Constant Int31.twice => "Camlcoq.Int31.twice".
Extract Constant Int31.twice_plus_one => "Camlcoq.Int31.twice_plus_one".
Extract Constant Int31.compare31 => "Camlcoq.Int31.compare".
Extract Constant Int31.On => "0".
Extract Constant Int31.In => "1".

Extract Inductive Decimal.int => unit [ "(fun _ -> ())" "(fun _ -> ())" ] "(fun _ _ _ -> assert false)".
Extract Inductive Hexadecimal.int => unit [ "(fun _ -> ())" "(fun _ -> ())" ] "(fun _ _ _ -> assert false)".
Extract Inductive Numeral.int => unit [ "(fun _ -> ())" "(fun _ -> ())" ] "(fun _ _ _ -> assert false)".

Extraction Inline Equations.Prop.Classes.noConfusion.
Extraction Inline Equations.Prop.Logic.eq_elim.
Extraction Inline Equations.Prop.Logic.eq_elim_r.
Extraction Inline Equations.Prop.Logic.transport.
Extraction Inline Equations.Prop.Logic.transport_r.
Extraction Inline Equations.Prop.Logic.False_rect_dep.
Extraction Inline Equations.Prop.Logic.True_rect_dep.
Extraction Inline Equations.Init.pr1.
Extraction Inline Equations.Init.pr2.
Extraction Inline Equations.Init.hidebody.
Extraction Inline Equations.Prop.DepElim.solution_left.

Extract Inlined Constant RandyPrelude.ascii_dec_bool => "(=)".

(* Avoid name clashes with OCaml or Coq module names *)
Extraction Blacklist config List String Nat Int Ast Universes UnivSubst Typing Retyping 
           OrderedType Logic Common Equality Char char uGraph
           Instances Classes Term Monad Coqlib Errors Compile Checker Eq Classes0 Numeral.

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
         Floats.Float32.from_parsed Floats.Float.from_parsed
         Floats.Float32.of_bits Floats.Float.of_bits
         Floats.Float32.to_bits Floats.Float.to_bits
         String.length
         Compiler.pipeline.printProg
         Compiler.pipeline.make_opts
         Compiler.pipeline.compile
         Compiler.pipeline.make_glue
         Compiler.pipeline.make_ffi
         Compiler.pipeline.show_IR.
Recursive Extraction Library BinPos.
Recursive Extraction Library OrdersTac.
Cd "..".

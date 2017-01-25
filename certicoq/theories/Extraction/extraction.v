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
        Compiler.allInstances.

(* Standard lib *)
Require Import ExtrOcamlBasic.
Require Import ExtrOcamlString.

(* Coqlib *)
Extract Inlined Constant Coqlib.proj_sumbool => "(fun x -> x)".


(* L6_to_Clight *)
Extract Constant L6_to_Clight.print_Clight => "PrintClight.print_if".
Extract Constant L6_to_Clight.print_Clight_dest => "PrintClight.print_dest".
Extract Constant L6_to_Clight.print_Clight_dest_names' => "PrintClight.print_dest_names".
Extract Constant L6_to_Clight.print => "print_string".
(* TEMP STUFF *)
Extract Constant L6_to_Clight.allocIdent => "Camlcoq.P.of_int 28".
Extract Constant L6_to_Clight.limitIdent => "Camlcoq.P.of_int 29".
Extract Constant L6_to_Clight.argsIdent => "Camlcoq.P.of_int 26".
Extract Constant L6_to_Clight.gcIdent => "Camlcoq.P.of_int 80".
Extract Constant L6_to_Clight.mainIdent => "Camlcoq.P.of_int 81".
Extract Constant L6_to_Clight.bodyIdent => "Camlcoq.P.of_int 90".
Extract Constant L6_to_Clight.threadInfIdent => "Camlcoq.P.of_int 31".
Extract Constant L6_to_Clight.tinfIdent => "Camlcoq.P.of_int 91".
Extract Constant L6_to_Clight.heapInfIdent => "Camlcoq.P.of_int 95".
Extract Constant L6_to_Clight.numArgsIdent => "Camlcoq.P.of_int 97".
(* Int31 *)
Extract Inductive Int31.digits => "bool" [ "false" "true" ].
Extract Inductive Int31.int31 => "int" [ "Camlcoq.Int31.constr" ] "Camlcoq.Int31.destr".
Extract Constant Int31.twice => "Camlcoq.Int31.twice".
Extract Constant Int31.twice_plus_one => "Camlcoq.Int31.twice_plus_one".
Extract Constant Int31.compare31 => "Camlcoq.Int31.compare".
Extract Constant Int31.On => "0".
Extract Constant Int31.In => "1".

(* Avoid name clashes *)
Extraction Blacklist List String Int Ast Char.

(* Cutting the dependency to R. *)
Extract Inlined Constant Fcore_defs.F2R => "fun _ -> assert false".
Extract Inlined Constant Fappli_IEEE.FF2R => "fun _ -> assert false".
Extract Inlined Constant Fappli_IEEE.B2R => "fun _ -> assert false".
Extract Inlined Constant Fappli_IEEE.round_mode => "fun _ -> assert false".
Extract Inlined Constant Fcalc_bracket.inbetween_loc => "fun _ -> assert false".

Cd "Extraction".

Separate Extraction
         Ctypes.merge_attributes Ctypes.remove_attributes Ctypes.build_composite_env
         Csyntax
         Ctypes.make_program
         AST.signature_main
         Floats.Float32.from_parsed Floats.Float.from_parsed
         Floats.Float32.of_bits Floats.Float.of_bits
         Floats.Float32.to_bits Floats.Float.to_bits
         Compiler.allInstances.test.

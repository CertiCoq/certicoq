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

Require Glue.glue
        Compiler.pipeline.

(* Standard lib *)
Require Import ExtrOcamlBasic.
Require Import ExtrOcamlString ExtrOcamlZInt.

(* Coqlib *)
Extract Inlined Constant Coqlib.proj_sumbool => "(fun x -> x)".

(* L6_to_Clight *)
(* Extract Constant pipeline.print_Clight => "PrintClight.print_if". *)
(* Extract Constant L6_to_Clight.print_Clight_dest => "PrintClight.print_dest". *)
(* Extract Constant L6_to_Clight.print_Clight_dest_names => "PrintClight.print_dest_names". *)
(* Extract Constant pipeline.print_Clight_names_dest_imports => "PrintClight.print_dest_names_imports". *)
(* Extract Constant pipeline.print => "print_string". *)


(* Time each phase, print to debug channel *)

Extract Constant AstCommon.timePhase =>
"(fun c x a -> let time = Unix.gettimeofday() in
               let temp = x a in
               let time = (Unix.gettimeofday() -. time) in
               Feedback.msg_debug (Pp.str (Printf.sprintf ""Time elapsed in %s:  %f"" ((fun s-> (String.concat """" (List.map (String.make 1) s))) c) time));
               temp)".


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
(* Set Extraction Flag 2031. (* default optimizations + linear let + linear beta *) *)
Separate Extraction
         Ctypes.merge_attributes Ctypes.remove_attributes Ctypes.build_composite_env
         Csyntax
         Ctypes.make_program
         AST.signature_main
         Floats.Float32.from_parsed Floats.Float.from_parsed
         Floats.Float32.of_bits Floats.Float.of_bits
         Floats.Float32.to_bits Floats.Float.to_bits
         String.length
         Compiler.pipeline.make_opts
         Compiler.pipeline.compile
         Glue.glue.generate_glue
         Glue.ffi.generate_ffi
         cps.M.elements
         Compiler.pipeline.show_IR.

Recursive Extraction Library BinPos.
Recursive Extraction Library OrdersTac.

Cd "..".

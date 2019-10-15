open AstCommon
open CertiClasses
open Compile0
open Compile1

(** val certiL2_to_L2k :
    (Compile0.coq_Term coq_Program, coq_Term coq_Program)
    coq_CerticoqTotalTranslation **)

let certiL2_to_L2k _ =
  stripProgram

(* ========================================================================= *)
(* fpSem: port of HOL4 semantics/fpSemScript.sml (CakeML v3479).             *)
(* Definitions of the floating point operations used in CakeML.              *)
(* (binary_ieee's fp_op constructors FP_Add ... are binary_ieee_FP_Add ...   *)
(* in the port, so the constructors below keep their HOL4 names.)            *)
(* ========================================================================= *)

needs "hol4/machine_ieee.ml";;
needs "semantics/ast.ml";;

type_invention_error := true;;

let fp_cmp_INDUCT,fp_cmp_RECURSION = cake_type
  "fp_cmp = FP_Less | FP_LessEqual | FP_Greater | FP_GreaterEqual | FP_Equal";;

let fp_uop_INDUCT,fp_uop_RECURSION = cake_type
  "fp_uop = FP_Abs | FP_Neg | FP_Sqrt";;

let fp_bop_INDUCT,fp_bop_RECURSION = cake_type
  "fp_bop = FP_Add | FP_Sub | FP_Mul | FP_Div";;

let fp_top_INDUCT,fp_top_RECURSION = cake_type
  "fp_top = FP_Fma";;

let fp_cmp_def = cake_def
  `fp_cmp (cmp:opb) =
     match cmp with
       Lt -> fp64_lessThan
     | Leq -> fp64_lessEqual
     | Gt -> fp64_greaterThan
     | Geq -> fp64_greaterEqual`;;

let fp_cmp_comp_def = cake_def
  `fp_cmp_comp (fop:fp_cmp) =
     match fop with
       FP_Less -> fp64_lessThan
     | FP_LessEqual -> fp64_lessEqual
     | FP_Greater -> fp64_greaterThan
     | FP_GreaterEqual -> fp64_greaterEqual
     | FP_Equal -> fp64_equal`;;

let fp_uop_comp_def = cake_def
  `fp_uop_comp (fop:fp_uop) =
     match fop with
       FP_Abs -> fp64_abs
     | FP_Neg -> fp64_negate
     | FP_Sqrt -> fp64_sqrt roundTiesToEven`;;

let fp_bop_comp_def = cake_def
  `fp_bop_comp (fop:fp_bop) =
     match fop with
       FP_Add -> fp64_add roundTiesToEven
     | FP_Sub -> fp64_sub roundTiesToEven
     | FP_Mul -> fp64_mul roundTiesToEven
     | FP_Div -> fp64_div roundTiesToEven`;;

let fpfma_def = cake_def
  `fpfma (v1:int64) (v2:int64) (v3:int64) =
     fp64_mul_add roundTiesToEven v2 v3 v1`;;

let fp_top_comp_def = cake_def
  `fp_top_comp (fop:fp_top) = fpfma`;;

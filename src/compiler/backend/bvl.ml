(* ========================================================================= *)
(* bvl: port of HOL4 compiler/backend/bvlScript.sml (CakeML v3479).          *)
(* The BVL intermediate language. This language is a simple first-order      *)
(* functional language without closures.                                     *)
(*                                                                           *)
(* BVL = bytecode-value language                                             *)
(*                                                                           *)
(* All operations that are uninteresting from a control-flow and binding    *)
(* perspective are lumped together in closLang op (clos_op).                 *)
(*                                                                           *)
(* There are only a handful of interesting operations.                      *)
(*                                                                           *)
(* BVL uses De Bruijn indices so there is no need for a variable name in    *)
(* the let-expression.                                                       *)
(*                                                                           *)
(* The optional number in the call expression below is the label to which  *)
(* the call will target. If that component is NONE, then the target address *)
(* is read from the end of the argument list, i.e. in case of NONE, the     *)
(* last exp in the argument list must evaluate to a CodePtr. This first     *)
(* number in the Call expression is how many additional ticks the Call      *)
(* should do.                                                                *)
(*                                                                           *)
(* Notes on the rendering: FUNPOW f n x is ITER n f x; the HOL4 overloads   *)
(* mk_unit = bvl_Op (BlockOp (clos_Cons 0)) [] and                           *)
(* mk_elem_at b i = bvl_Op (BlockOp (ElemAt i)) [b] are expanded where they *)
(* are used.                                                                 *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "compiler/backend/closLang.ml";;
needs "compiler/backend/backend_common.ml";;

type_invention_error := true;;

(* bvl_Force loc v: loc to call for evaluation of unevaluated thunk, v the  *)
(* var holding the thunk                                                     *)

let bvl_exp_INDUCT,bvl_exp_RECURSION = cake_type
  "bvl_exp = bvl_Var num
           | bvl_If bvl_exp bvl_exp bvl_exp
           | bvl_Let (bvl_exp list) bvl_exp
           | bvl_Raise bvl_exp
           | bvl_Handle bvl_exp bvl_exp
           | bvl_Tick bvl_exp
           | bvl_Call num (num option) (bvl_exp list)
           | bvl_Force num num
           | bvl_Op clos_op (bvl_exp list)";;

(* HOL4: Bool *)

let bvl_Bool_def = cake_def
  `bvl_Bool b = bvl_Op (BlockOp (clos_Cons (bool_to_tag b))) []`;;

let mk_tick_def = cake_def
  `mk_tick n (e:bvl_exp) = ITER n bvl_Tick e`;;

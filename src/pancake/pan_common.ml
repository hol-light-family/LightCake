(* ========================================================================= *)
(* pan_common: port of HOL4 pancake/pan_commonScript.sml (CakeML v3479).     *)
(* Common definitions for Pancake compiler.                                  *)
(* ========================================================================= *)

needs "misc/misc.ml";;

prioritize_num();;
type_invention_error := true;;

let distinct_lists_def = cake_def
  `distinct_lists (xs:A list) ys <=> ALL (\x. ~MEM x ys) xs`;;

(* ========================================================================= *)
(* mloption: port of HOL4 basis/pure/mloptionScript.sml (CakeML v3479).      *)
(* Pure functions for the Option module.                                     *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "hol4/ternaryComparisons.ml";;

type_invention_error := true;;

let getOpt_def = cake_def
  `(getOpt (SOME (v:A)) a = v) /\
   (getOpt NONE a = a)`;;

let filter_def = cake_def
  `filter (f:A->bool) a = if f a then SOME a else NONE`;;

(* HOL4: mapPartial *)

let mloption_mapPartial_def = cake_def
  `mloption_mapPartial (f:A->B option) opt = OPTION_BIND opt f`;;

let compose_def = cake_def
  `compose (f:B->C) (g:A->B option) a =
     match g a with
       SOME v -> SOME (f v)
     | NONE -> NONE`;;

let composePartial_def = cake_def
  `composePartial (f:B->C option) (g:A->B option) a =
     match g a with
       SOME v -> f v
     | NONE -> NONE`;;

(* HOL4: compare *)

let mloption_compare_def = cake_def
  `mloption_compare (f:A->B->ordering) x y =
     match x with
       NONE -> (match y with NONE -> EQUAL | _ -> LESS)
     | SOME vx -> (match y with NONE -> GREATER | SOME vy -> f vx vy)`;;

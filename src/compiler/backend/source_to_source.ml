(* ========================================================================= *)
(* source_to_source: port of HOL4 compiler/backend/source_to_sourceScript.sml*)
(* (CakeML v3479).                                                           *)
(* This phase collects all source-to-source transformations.                *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "compiler/backend/source_let.ml";;

type_invention_error := true;;

let source_to_source_compile_def = cake_def
  `source_to_source_compile = source_let_compile_decs`;;

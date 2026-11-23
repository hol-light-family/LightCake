(* ========================================================================= *)
(* pan_to_word: port of HOL4 pancake/pan_to_wordScript.sml (CakeML v3479).   *)
(* Compiler from pan to word.                                                *)
(*                                                                           *)
(* Notes on the rendering:                                                   *)
(* - Names as doc/names.tsv says: compile_prog is                           *)
(*   pan_to_word_compile_prog; the passes are pan_simp_compile_prog,         *)
(*   pan_structs_compile_top, pan_globals_compile_top,                       *)
(*   pan_to_crep_compile_prog, crep_to_loop_compile_prog and                 *)
(*   loop_to_word_compile.                                                   *)
(* - HOL4's sequential let is written as nested lets; strlit "main" is      *)
(*   implode "main".                                                         *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "pancake/pan_simp.ml";;
needs "pancake/pan_structs.ml";;
needs "pancake/pan_globals.ml";;
needs "pancake/pan_to_crep.ml";;
needs "pancake/crep_to_loop.ml";;
needs "pancake/loop_to_word.ml";;

prioritize_num();;
type_invention_error := true;;

let pan_to_word_compile_prog_def = cake_def
  `pan_to_word_compile_prog arch (prog:((A)decl)list) =
     let prog = pan_simp_compile_prog prog in
     let prog = pan_structs_compile_top prog in
     let prog = pan_globals_compile_top prog (implode "main") in
     let prog = pan_to_crep_compile_prog prog in
     let prog = crep_to_loop_compile_prog arch prog in
     loop_to_word_compile prog`;;

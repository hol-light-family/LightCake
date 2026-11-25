(* ========================================================================= *)
(* cfDiv: port of HOL4 characteristic/cfDivScript.sml (CakeML v3479), the    *)
(* code part: the declaration of the repeat function, the one declaration   *)
(* cfDiv adds to the basis program (decision D2: the CF theory of cfDiv,     *)
(* the repeat lemmas used to prove non-termination of programs in cf, is     *)
(* cfDiv_part2.ml, milestone M10).                                           *)
(* ========================================================================= *)

needs "translator/std_prelude.ml";;
needs "translator/ml_parseLib.ml";;

type_invention_error := true;;

translation_extends "std_prelude";;

(* HOL4's local append_prog of cfDiv (QCONV EVAL changes nothing in the    *)
(* parser's output): add_prog with the identity as name function            *)
let cfDiv_append_prog tm = ml_prog_update (ml_prog_add_prog tm I);;

(* -- old repeat approach -- *)

let _ = cfDiv_append_prog
  (process_topdecs_at (3987,4) "fun repeat f x = repeat f (f x);");;

(* HOL4 val repeat_v = fetch "-" "repeat_v_def" *)
let repeat_v_def = ml_prog_fetch "repeat_v_def";;

finalise_translation ();;

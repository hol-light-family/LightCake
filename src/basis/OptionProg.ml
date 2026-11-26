(* ========================================================================= *)
(* OptionProg: port of HOL4 basis/OptionProgScript.sml (CakeML v3479).       *)
(* Module about the option type.                                             *)
(* ========================================================================= *)

needs "basis/RuntimeProg.ml";;
needs "basis/pure/mloption.ml";;

type_invention_error := true;;

translation_extends "RuntimeProg";;

ml_prog_update (ml_prog_open_module "Option");;

ml_prog_update (ml_prog_add_dec
  `Dtabbrev unknown_loc [implode "'a"] (implode "option")
     (Atapp [Atvar (implode "'a")] (Short (implode "option")))` I);;

next_ml_names := ["getOpt"];;
let _ = translate getOpt_def;;

next_ml_names := ["isSome"];;
let _ = translate IS_SOME_DEF;;

next_ml_names := ["valOf"];;
let _ = translate THE_DEF;;
let the_side_def = update_precondition (prove
 (`the_side = IS_SOME:A option->bool`,
  REWRITE_TAC[FUN_EQ_THM] THEN MATCH_MP_TAC option_INDUCT THEN
  REWRITE_TAC[tr_fetch "the_side_def"; IS_SOME_DEF] THEN
  CAKE_REWRITE_TAC[] THEN MESON_TAC[option_DISTINCT; option_INJ]));;

next_ml_names := ["join"];;
let _ = translate OPTION_JOIN_DEF;;

next_ml_names := ["map"];;
let _ = translate OPTION_MAP_DEF;;

next_ml_names := ["mapPartial"];;
let _ = translate (REWRITE_RULE [GSYM mloption_mapPartial_def] OPTION_BIND_DEF);;

let _ = translate compose_def;;

next_ml_names := ["composePartial"];;
let _ = translate composePartial_def;;

next_ml_names := ["isNone"];;
let _ = translate IS_NONE_DEF;;

next_ml_names := ["map2"];;
let _ = translate OPTION_MAP2_DEF;;

next_ml_names := ["compare"];;
let _ = translate mloption_compare_def;;

ml_prog_update (ml_prog_close_module None);;

finalise_translation ();;

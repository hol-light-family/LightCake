(* ========================================================================= *)
(* PrettyPrinterProg: port of HOL4 basis/PrettyPrinterProgScript.sml         *)
(* (CakeML v3479).  Module providing pretty-printer implementation, and      *)
(* setup of the global builtin pretty-printer functions.                     *)
(* ========================================================================= *)

needs "basis/pure/mlprettyprinter.ml";;
needs "basis/IntProg.ml";;
needs "basis/addPrettyPrintersLib.ml";;

type_invention_error := true;;

translation_extends "IntProg";;

let previous_prog_pps =
  pps_of_global_tys (ml_prog_get_prog (ml_prog_remove_snocs (get_ml_prog_state ())));;

ml_prog_update (ml_prog_open_module "PrettyPrinter");;

use_full_type_names := false;;
register_type `:pp_data`;;
register_type `:default_type`;;

(* HOL4's local function tr *)
let prettyprinter_tr name def =
  next_ml_names := [name];
  translate def;;

ml_prog_update ml_prog_open_local_block;;

let _ = translate app_intersperse_def;;
let _ = translate app_list_wrap_def;;
let _ = translate pp_paren_contents_def;;

let _ = translate escape_str_app_list_def;;

let escape_str_app_list_side = prove
 (`!i s. escape_str_app_list_side i s <=> i <= strlen s`,
  MATCH_MP_TAC escape_str_app_list_ind THEN REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[tr_fetch "escape_str_app_list_side_def"] THEN
  MP_TAC (ISPEC `str_findi (\c. IS_SOME (char_escape_seq c)) i s` (cases "option")) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[distinctness "option"; injectivity "option"] THENL
   [ARITH_TAC;
    REWRITE_TAC[FORALL_UNWIND_THM1] THEN
    FIRST_ASSUM (MP_TAC o MATCH_MP (GEN_ALL str_findi_range)) THEN
    FIRST_X_ASSUM (fun th -> FIRST_ASSUM (fun th2 -> REWRITE_TAC[MATCH_MP th th2])) THEN
    ARITH_TAC]);;
let _ = update_precondition escape_str_app_list_side;;

ml_prog_update ml_prog_open_local_in_block;;

let _ = prettyprinter_tr "toAppList" pp_contents_def;;
let _ = prettyprinter_tr "no_parens" pp_no_parens_def;;
let _ = prettyprinter_tr "token" pp_token_def;;
let _ = prettyprinter_tr "tuple" pp_paren_tuple_def;;
let _ = prettyprinter_tr "spaced_block" pp_spaced_block_def;;
let _ = prettyprinter_tr "app_block" pp_app_block_def;;
let _ = prettyprinter_tr "val_eq" pp_val_eq_def;;
let _ = prettyprinter_tr "val_eq" pp_val_eq_def;;
let _ = prettyprinter_tr "val_hidden_type" pp_val_hidden_type_def;;
let _ = prettyprinter_tr "failure_message" pp_failure_message_def;;
let _ = prettyprinter_tr "unprintable" pp_unprintable_def;;

let _ = translate pp_list_def;;
let _ = translate pp_bool_def;;

let _ = translate pp_char_def;;
let _ = translate pp_string_def;;

let _ = translate pp_app_list_def;;
let _ = translate pp_pp_data_def;;

let _ = translate pp_default_type_def;;

ml_prog_update ml_prog_close_local_blocks;;

ml_prog_update (ml_prog_close_module None);;

(* pretty-printers for global (builtin) types, at global scope *)

let _ = translate pp_exn_def;;
let _ = translate pp_unit_def;;
let _ = translate pp_vector_def;;

(* add global names for some printers, esp. those used in pp_pp_data *)
let rename_pp_list_def = new_definition
  `rename_pp_list = (pp_list:(A->pp_data)->(A)list->pp_data)`;;
let _ = prettyprinter_tr "pp_list" rename_pp_list_def;;

let rename_pp_bool_def = new_definition
  `rename_pp_bool = pp_bool`;;
let _ = prettyprinter_tr "pp_bool" rename_pp_bool_def;;

let rename_pp_char_def = new_definition
  `rename_pp_char = pp_char`;;
let _ = prettyprinter_tr "pp_char" rename_pp_char_def;;

let rename_pp_string_def = new_definition
  `rename_pp_string = pp_string`;;
let _ = prettyprinter_tr "pp_string" rename_pp_string_def;;

let rename_pp_app_list_def = new_definition
  `rename_pp_app_list = (pp_app_list:(A->pp_data)->(A)app_list->pp_data)`;;
let _ = prettyprinter_tr "pp_app_list" rename_pp_app_list_def;;

(* useless pretty-printers for impure types.
   should be replaced later in the basis *)
let _ = translate pp_ref_def;;
let _ = translate pp_array_def;;
let _ = translate pp_word8array_def;;

(* candle needs constants in the basis to be defined as literals, no funcalls *)
let _ = translate (REWRITE_RULE [pp_token_def] pp_fun_def);;

(* pretty printers for numeric types *)
let _ = translate pp_int_def;;
let _ = translate pp_word8_def;;
let _ = translate pp_word64_def;;

(* setup pretty-printers for previously existing global types *)
ml_prog_update (add_pps previous_prog_pps);;

finalise_translation ();;

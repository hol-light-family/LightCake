(* ========================================================================= *)
(* CharProg: port of HOL4 basis/CharProgScript.sml (CakeML v3479).           *)
(* A module about the char type for the CakeML standard basis library.       *)
(*                                                                           *)
(* HOL4's EVAL of some_chars_vector is a conversion here (BAS1AUX_EVAL_    *)
(* SOME_CHARS_VECTOR): GENLIST (list_of_seq) by GENLIST_AUX, one element at *)
(* a time; the characters CHR n stay as HOL4's EVAL leaves them (they are    *)
(* HOL4's character literals, and the translator makes them literals).       *)
(* ========================================================================= *)

needs "hol4/string4.ml";;
needs "hol4/regexp_compiler.ml";;
needs "basis/pure/mlstring.ml";;
needs "basis/RatProg.ml";;
needs "basis/basisFunctionsLib.ml";;

type_invention_error := true;;

translation_extends "RatProg";;

(* Char module -- translated *)

ml_prog_update (ml_prog_open_module "Char");;

(* HOL4 generate_sigs := true: no signatures (see ListProg.ml) *)

ml_prog_update (ml_prog_add_dec
  `Dtabbrev unknown_loc [] (implode "char") (Atapp [] (Short (implode "char")))` I);;

let _ = trans "ord" `ORD`;;
let CharProg_Char_ord_def = tr_fetch "Char_ord_def";;
let _ = trans "chr" `CHR`;;
let CharProg_Char_chr_def = tr_fetch "Char_chr_def";;
let _ = trans "=" `(=):char->char->bool`;;
let CharProg_Char_eq_def = tr_fetch "Char_eq_def";;
let _ = trans "<" `char_lt`;;
let CharProg_Char_lt_def = tr_fetch "Char_lt_def";;
let _ = trans ">" `char_gt`;;
let CharProg_Char_gt_def = tr_fetch "Char_gt_def";;
let _ = trans "<=" `char_le`;;
let CharProg_Char_le_def = tr_fetch "Char_le_def";;
let _ = trans ">=" `char_ge`;;
let CharProg_Char_ge_def = tr_fetch "Char_ge_def";;

next_ml_names := ["isSpace"];;
let _ = translate isSpace_def;;
next_ml_names := ["isLower"];;
let _ = translate isLower_def;;
next_ml_names := ["isUpper"];;
let _ = translate isUpper_def;;
next_ml_names := ["isDigit"];;
let _ = translate isDigit_def;;
next_ml_names := ["isAlpha"];;
let _ = translate isAlpha_def;;
next_ml_names := ["isAlphaNum"];;
let _ = translate isAlphaNum_def;;

let _ = trans "fromByte" `word8_to_char`;;
let Char_fromByte_def = tr_fetch "Char_fromByte_def";;

let some_chars_vector_def = new_definition
  `some_chars_vector = Vector (list_of_seq (\n. SOME (CHR n)) 256)`;;

let some_char_def = new_definition
  `some_char c = regexp_compiler_sub some_chars_vector (ORD c)`;;

let some_char_thm = prove
 (`!c. some_char c = SOME c`,
  GEN_TAC THEN REWRITE_TAC[some_chars_vector_def; some_char_def; regexp_compiler_sub_def] THEN
  SIMP_TAC[EL_LIST_OF_SEQ; ORD_BOUND; CHR_ORD]);;

(* HOL4: EVAL some_chars_vector *)
let BAS1AUX_EVAL_SOME_CHARS_VECTOR =
  let step = REWR_CONV (CONJUNCT2 GENLIST_AUX) and stop = REWR_CONV (CONJUNCT1 GENLIST_AUX) in
  let rec genlist_aux_conv tm =
    if rand (rator tm) = `0` then stop tm
    else (RATOR_CONV (RAND_CONV num_CONV) THENC step THENC genlist_aux_conv) tm in
  let th = REWRITE_RULE [GENLIST_GENLIST_AUX] some_chars_vector_def in
  let th = CONV_RULE (RAND_CONV (RAND_CONV genlist_aux_conv)) th in
  CONV_RULE (RAND_CONV (DEPTH_CONV BETA_CONV)) th;;

ml_prog_update ml_prog_open_local_block;;

let _ = translate BAS1AUX_EVAL_SOME_CHARS_VECTOR;;

ml_prog_update ml_prog_open_local_in_block;;

next_ml_names := ["some"];;
let _ = translate some_char_def;;

let some_char_side_thm = prove
 (`!v. some_char_side v <=> T`,
  REWRITE_TAC[tr_fetch "some_char_side_def"; some_chars_vector_def;
              regexp_compiler_length_def; LENGTH_LIST_OF_SEQ; ORD_BOUND]);;

let _ = update_precondition some_char_side_thm;;

ml_prog_update ml_prog_close_local_blocks;;

ml_prog_update (ml_prog_close_module None);;

finalise_translation ();;

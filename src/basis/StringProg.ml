(* ========================================================================= *)
(* StringProg: port of HOL4 basis/StringProgScript.sml (CakeML v3479).       *)
(* Module about the built-in string type.                                    *)
(* ========================================================================= *)

needs "translator/ml_translator.ml";;
needs "basis/pure/mlstring.ml";;
needs "basis/VectorProg.ml";;
needs "basis/basisFunctionsLib.ml";;

type_invention_error := true;;

translation_extends "VectorProg";;
use_string_type false;;

ml_prog_update (ml_prog_open_module "String");;

(* HOL4 generate_sigs := true: no signatures (see ListProg.ml) *)

ml_prog_update (ml_prog_add_dec
  `Dtabbrev unknown_loc [] (implode "string") (Atapp [] (Short (implode "string")))` I);;

let _ = trans "<" `mlstring_lt`;;
let StringProg_String_lt_def = tr_fetch "String_lt_def";;
let _ = trans "<=" `mlstring_le`;;
let StringProg_String_le_def = tr_fetch "String_le_def";;
let _ = trans ">" `mlstring_gt`;;
let StringProg_String_gt_def = tr_fetch "String_gt_def";;
let _ = trans ">=" `mlstring_ge`;;
let StringProg_String_ge_def = tr_fetch "String_ge_def";;

ml_prog_update (ml_prog_open_module "Fast");;
let _ = trans "<" `fast_lt`;;
let String_Fast_lt_def = tr_fetch "String_Fast_lt_def";;
let _ = trans "<=" `fast_le`;;
let String_Fast_le_def = tr_fetch "String_Fast_le_def";;
let _ = trans ">" `fast_gt`;;
let String_Fast_gt_def = tr_fetch "String_Fast_gt_def";;
let _ = trans ">=" `fast_ge`;;
let String_Fast_ge_def = tr_fetch "String_Fast_ge_def";;
ml_prog_update (ml_prog_close_module None);;

let _ = trans "sub" `strsub`;;
let StringProg_String_sub_def = tr_fetch "String_sub_def";;
let _ = trans "implode" `implode`;;
let StringProg_String_implode_def = tr_fetch "String_implode_def";;
let _ = trans "explode" `explode`;;
let StringProg_String_explode_def = tr_fetch "String_explode_def";;
let _ = trans "size" `strlen`;;
let StringProg_String_size_def = tr_fetch "String_size_def";;
let _ = trans "concat" `mlstring_concat`;;
let StringProg_String_concat_def = tr_fetch "String_concat_def";;
let _ = trans "substring" `substring`;;
let StringProg_String_substring_def = tr_fetch "String_substring_def";;
let _ = translate strcat_def;;
let _ = trans "^" `strcat`;;
let StringProg_String_strcat_def = tr_fetch "String_strcat_def";;
let _ = trans "=" `((=):mlstring->mlstring->bool)`;;
let StringProg_String_eq_def = tr_fetch "String_eq_def";;

let _ = translate mlstring_extract_def;;

(* HOL4 proves extract_side (with MIN_DEF); the translator may already have *)
(* discharged it (then there is no extract_side_def)                         *)
let extract_side_thm =
  if not (can tr_fetch "extract_side_def") then TRUTH else
  update_precondition (prove
   (`!s i opt. extract_side s i opt`,
    REWRITE_TAC[tr_fetch "extract_side_def"; MIN] THEN ARITH_TAC));;

next_ml_names := ["concatWith"];;
let _ = translate concatWith_def;;

next_ml_names := ["str"];;
let _ = translate chr_to_str_def;;

ml_prog_update ml_prog_open_local_block;;
let _ = translate translate_aux_def;;
let translate_aux_side_def = tr_fetch "translate_aux_side_def";;
ml_prog_update ml_prog_open_local_in_block;;

next_ml_names := ["translate"];;
let _ = translate translate_def;;
let translate_side_def = tr_fetch "translate_side_def";;

let translate_aux_side_thm = prove
 (`!(f:char->char) s n len. n + len = strlen s ==> translate_aux_side f s n len`,
  BAS1AUX_SIDE_TAC "len" translate_aux_side_def);;

let translate_side_thm = update_precondition (prove
 (`!f s. translate_side (f:char->char) s`,
  REWRITE_TAC[translate_side_def] THEN REPEAT GEN_TAC THEN
  MATCH_MP_TAC translate_aux_side_thm THEN ARITH_TAC));;

ml_prog_update ml_prog_open_local_block;;
let _ = translate splitl_aux_def;;
ml_prog_update ml_prog_open_local_in_block;;

next_ml_names := ["split"];;
let _ = translate splitl_def;;

ml_prog_update ml_prog_open_local_block;;

let _ = translate tokens_alt_aux_def;;

let tokens_alt_aux_side_def = tr_fetch "tokens_alt_aux_side_def";;

ml_prog_update ml_prog_open_local_in_block;;

next_ml_names := ["tokens"];;
let _ = translate tokens_alt;;
let tokens_side_def = tr_fetch "tokens_side_def";;

let tokens_alt_aux_side_thm = prove
 (`!f s i j k. i <= j /\ j <= k /\ k <= strlen s ==> tokens_alt_aux_side f s i j k`,
  MATCH_MP_TAC tokens_alt_aux_ind THEN REPEAT GEN_TAC THEN STRIP_TAC THEN STRIP_TAC THEN
  ONCE_REWRITE_TAC[tokens_alt_aux_side_def] THEN REPEAT STRIP_TAC THEN
  TRY (FIRST_X_ASSUM (MATCH_MP_TAC o REWRITE_RULE[IMP_IMP])) THEN
  ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

let tokens_side_thm = update_precondition (prove
 (`!f s. tokens_side f s`,
  REWRITE_TAC[tokens_side_def] THEN REPEAT GEN_TAC THEN
  MATCH_MP_TAC tokens_alt_aux_side_thm THEN ARITH_TAC));;

ml_prog_update ml_prog_open_local_block;;

let _ = translate fields_alt_aux_def;;
let fields_alt_aux_side_def = tr_fetch "fields_alt_aux_side_def";;

ml_prog_update ml_prog_open_local_in_block;;

next_ml_names := ["fields"];;
let _ = translate fields_alt;;
let fields_side_def = tr_fetch "fields_side_def";;

let fields_alt_aux_side_thm = prove
 (`!f s i j k. i <= j /\ j <= k /\ k <= strlen s ==> fields_alt_aux_side f s i j k`,
  MATCH_MP_TAC fields_alt_aux_ind THEN REPEAT GEN_TAC THEN STRIP_TAC THEN STRIP_TAC THEN
  ONCE_REWRITE_TAC[fields_alt_aux_side_def] THEN REPEAT STRIP_TAC THEN
  TRY (FIRST_X_ASSUM (MATCH_MP_TAC o REWRITE_RULE[IMP_IMP])) THEN
  ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

let fields_side_thm = update_precondition (prove
 (`!f s. fields_side f s`,
  REWRITE_TAC[fields_side_def] THEN REPEAT GEN_TAC THEN
  MATCH_MP_TAC fields_alt_aux_side_thm THEN ARITH_TAC));;

next_ml_names := ["findi"];;
let _ = translate str_findi_def;;

ml_prog_update ml_prog_open_local_block;;
let _ = translate isStringThere_aux_def;;
let isStringThere_aux_side_def = tr_fetch "isstringthere_aux_side_def";;
ml_prog_update ml_prog_open_local_in_block;;

let isStringThere_aux_side_thm = prove
 (`!s1 s2 s1i s2i len.
     s1i + len <= strlen s1 /\ s2i + len <= strlen s2 ==>
     isstringthere_aux_side s1 s2 s1i s2i len`,
  BAS1AUX_SIDE_TAC "len" isStringThere_aux_side_def);;

next_ml_names := ["isSubstring"];;
let _ = translate isSubstring_aux_def;;
let isSubstring_aux_side_def = tr_fetch "issubstring_aux_side_def";;
let isSubstring_aux_side_thm = prove
 (`!s1 s2 lens1 n len.
     (lens1 = strlen s1) /\ n + len + lens1 <= strlen s2 + 1 ==>
     issubstring_aux_side s1 s2 lens1 n len`,
  BAS1AUX_SIDE_LEMMAS_TAC "len" isSubstring_aux_side_def [isStringThere_aux_side_thm]);;

next_ml_names := ["isSubstring"];;
let _ = translate isSubstring_def;;
let isSubstring_side_def = tr_fetch "issubstring_side_def";;
let isSubstring_side_thm = update_precondition (prove
 (`!s1 s2. issubstring_side s1 s2`,
  REWRITE_TAC[isSubstring_side_def] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC isSubstring_aux_side_thm THEN ASM_ARITH_TAC));;

next_ml_names := ["isSuffix"];;
let _ = translate isSuffix_def;;
let isSuffix_side_def = tr_fetch "issuffix_side_def";;
let isSuffix_thm = update_precondition (prove
 (`!s1 s2. issuffix_side s1 s2`,
  REWRITE_TAC[isSuffix_side_def] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC isStringThere_aux_side_thm THEN ASM_ARITH_TAC));;

next_ml_names := ["isPrefix"];;
let _ = translate isPrefix_def;;
let isPrefix_side_def = tr_fetch "isprefix_side_def";;
let isPrefix_thm = update_precondition (prove
 (`!s1 s2. isprefix_side s1 s2`,
  REWRITE_TAC[isPrefix_side_def] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC isStringThere_aux_side_thm THEN ASM_ARITH_TAC));;

next_ml_names := ["compare"];;
let _ = translate compare_thm;;

ml_prog_update ml_prog_open_local_block;;
let _ = translate mlstring_collate_aux_def;;
let StringProg_collate_aux_side_def = tr_fetch "collate_aux_side_def";;
ml_prog_update ml_prog_open_local_in_block;;

next_ml_names := ["collate"];;
let _ = translate mlstring_collate_def;;
let StringProg_collate_side_def = tr_fetch "collate_1_side_def";;

(* the side constants of this collate are StringProg_collate_aux_side and   *)
(* StringProg_collate_1_side (VectorProg made collate_aux_side and          *)
(* collate_1_side; NAMING.md 11.4); the OCaml names of HOL4's collate_aux_  *)
(* side_def, collate_side_def and collate_side_thm take the prefix too      *)
let StringProg_collate_aux_side_thm = prove
 (`!(f:char->char->ordering) s1 s2 ord n len.
     (n + len = if strlen s1 < strlen s2 then strlen s1 else strlen s2) ==>
     StringProg_collate_aux_side f s1 s2 ord n len`,
  BAS1AUX_COLLATE_SIDE_TAC "len" StringProg_collate_aux_side_def);;

let StringProg_collate_side_thm = update_precondition (prove
 (`!f s1 s2. StringProg_collate_1_side (f:char->char->ordering) s1 s2`,
  REWRITE_TAC[StringProg_collate_side_def] THEN REPEAT GEN_TAC THEN
  REPEAT CONJ_TAC THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC StringProg_collate_aux_side_thm THEN ASM_ARITH_TAC));;

let _ = translate char_escape_seq_def;;
ml_prog_update ml_prog_open_local_block;;
let _ = translate char_escaped_def;;
ml_prog_update ml_prog_open_local_in_block;;
let _ = translate escape_str_def;;
let _ = translate escape_char_def;;

ml_prog_update ml_prog_close_local_blocks;;
ml_prog_update (ml_prog_close_module None);;

finalise_translation ();;

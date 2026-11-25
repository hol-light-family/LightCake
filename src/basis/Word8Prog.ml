(* ========================================================================= *)
(* Word8Prog: port of HOL4 basis/Word8ProgScript.sml (CakeML v3479).         *)
(* Module about the built-in word8 type.                                     *)
(*                                                                           *)
(* word8 is byte; the word operations are Library/words.ml's as in           *)
(* Word64Prog.ml.  HOL4's Overload WORD8 is ml_WORD at type byte (expanded   *)
(* at its uses); the attribute xlet_auto_match of the four unicity theorems  *)
(* belongs to the CF automation (OPEN(M10)).                                 *)
(* ========================================================================= *)

needs "hol4/words4.ml";;
needs "translator/ml_translator.ml";;
needs "basis/Word64Prog.ml";;
needs "basis/basisFunctionsLib.ml";;

type_invention_error := true;;

translation_extends "Word64Prog";;

(* Word8 module -- translated *)

ml_prog_update (ml_prog_add_dec
  `Dtabbrev unknown_loc [] (implode "byte") (Atapp [] (Short (implode "word8")))` I);;

ml_prog_update (ml_prog_open_module "Word8");;

(* HOL4 generate_sigs := true: no signatures (see ListProg.ml) *)

ml_prog_update (ml_prog_add_dec
  `Dtabbrev unknown_loc [] (implode "word") (Atapp [] (Short (implode "word8")))` I);;

(* to/from int/char *)
let _ = trans "fromInt" `word:num->byte`;;
let Word8_fromInt_def = tr_fetch "Word8_fromInt_def";;
let _ = trans "fromChar" `char_to_word8`;;
let Word8_fromChar_def = tr_fetch "Word8_fromChar_def";;
let _ = trans "toInt" `val:byte->num`;;
let Word8_toInt_def = tr_fetch "Word8_toInt_def";;
let _ = trans "toIntSigned" `ival:byte->int`;;
let Word8_toIntSigned_def = tr_fetch "Word8_toIntSigned_def";;

(* bitwise operations *)
let _ = trans "andb" `word_and:byte->byte->byte`;;
let Word8Prog_Word8_andb_def = tr_fetch "Word8_andb_def";;
let _ = trans "orb" `word_or:byte->byte->byte`;;
let Word8Prog_Word8_orb_def = tr_fetch "Word8_orb_def";;
let _ = trans "xorb" `word_xor:byte->byte->byte`;;
let Word8Prog_Word8_xorb_def = tr_fetch "Word8_xorb_def";;

let Word8Prog_word_1comp_eq = prove
 (`!w:byte. word_not w = word_xor w (word 255)`,
  CONV_TAC WORD_BLAST);;

next_ml_names := ["notb"];;
let _ = translate Word8Prog_word_1comp_eq;;

(* arithmetic *)
let _ = trans "+" `word_add:byte->byte->byte`;;
let Word8Prog_Word8_plus_def = tr_fetch "Word8_plus_def";;
let _ = trans "-" `word_sub:byte->byte->byte`;;
let Word8Prog_Word8_minus_def = tr_fetch "Word8_minus_def";;
let _ = trans "=" `(=):byte->byte->bool`;;
let Word8Prog_Word8_eq_def = tr_fetch "Word8_eq_def";;
let _ = trans "<" `word_ult:byte->byte->bool`;;
let Word8Prog_Word8_lt_def = tr_fetch "Word8_lt_def";;
let _ = trans ">" `word_ugt:byte->byte->bool`;;
let Word8Prog_Word8_gt_def = tr_fetch "Word8_gt_def";;
let _ = trans "<=" `word_ule:byte->byte->bool`;;
let Word8Prog_Word8_le_def = tr_fetch "Word8_le_def";;
let _ = trans ">=" `word_uge:byte->byte->bool`;;
let Word8Prog_Word8_ge_def = tr_fetch "Word8_ge_def";;

(* shifts *)

let Word8Prog_var_word_lsl_def = new_definition
  `Word8Prog_var_word_lsl (w:byte) (n:num) =
     if n < 8 then
     if n < 4 then
       if n < 2 then if n < 1 then w else word_shl w 1
       else if n < 3 then word_shl w 2
       else word_shl w 3
     else if n < 6 then if n < 5 then word_shl w 4 else word_shl w 5
     else if n < 7 then word_shl w 6
     else word_shl w 7 else word 0`;;

(* HOL4's proofs (ntac 32 Cases_on n): below 8 one of the cases, beyond the *)
(* shift is trivial                                                         *)
let BAS1AUX_VAR_SHIFT8_TAC def big_tac zero =
  REPEAT GEN_TAC THEN REWRITE_TAC[def] THEN
  ASM_CASES_TAC `n < 8` THEN ASM_REWRITE_TAC[] THENL
   [UNDISCH_TAC `n < 8` THEN SPEC_TAC (`n:num`,`n:num`) THEN
    CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[zero];
    big_tac];;

let Word8Prog_var_word_lsl_thm = prove
 (`!w n. Word8Prog_var_word_lsl w n = word_shl w n`,
  BAS1AUX_VAR_SHIFT8_TAC Word8Prog_var_word_lsl_def
   (CONV_TAC SYM_CONV THEN MATCH_MP_TAC WORD_SHL_TRIVIAL THEN
    REWRITE_TAC[DIMINDEX_8] THEN ASM_ARITH_TAC)
   WORD_SHL_ZERO);;

let Word8Prog_var_word_lsr_def = new_definition
  `Word8Prog_var_word_lsr (w:byte) (n:num) =
     if n < 8 then
     if n < 4 then
       if n < 2 then if n < 1 then w else word_ushr w 1
       else if n < 3 then word_ushr w 2
       else word_ushr w 3
     else if n < 6 then if n < 5 then word_ushr w 4 else word_ushr w 5
     else if n < 7 then word_ushr w 6
     else word_ushr w 7 else word 0`;;

let Word8Prog_var_word_lsr_thm = prove
 (`!w n. Word8Prog_var_word_lsr w n = word_ushr w n`,
  BAS1AUX_VAR_SHIFT8_TAC Word8Prog_var_word_lsr_def
   (CONV_TAC SYM_CONV THEN REWRITE_TAC[WORD_USHR_EQ_0] THEN
    MATCH_MP_TAC LTE_TRANS THEN EXISTS_TAC `2 EXP 8` THEN
    REWRITE_TAC[REWRITE_RULE[DIMINDEX_8] (ISPEC `w:byte` VAL_BOUND)] THEN
    REWRITE_TAC[LE_EXP; ARITH_EQ] THEN ASM_ARITH_TAC)
   WORD_USHR_ZERO);;

let Word8Prog_var_word_asr_def = new_definition
  `Word8Prog_var_word_asr (w:byte) (n:num) =
     if n < 8 then
     if n < 4 then
       if n < 2 then if n < 1 then w else word_ishr w 1
       else if n < 3 then word_ishr w 2
       else word_ishr w 3
     else if n < 6 then if n < 5 then word_ishr w 4 else word_ishr w 5
     else if n < 7 then word_ishr w 6
     else word_ishr w 7 else word_ishr w 8`;;

let Word8Prog_var_word_asr_thm = prove
 (`!w n. Word8Prog_var_word_asr w n = word_ishr w n`,
  BAS1AUX_VAR_SHIFT8_TAC Word8Prog_var_word_asr_def
   (REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_ISHR; DIMINDEX_8] THEN
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    ASM_SIMP_TAC[ARITH_RULE `~(i + 8 < 8)`; ARITH_RULE `~(n < 8) ==> ~(i + n < 8)`])
   WORD_ISHR_ZERO);;

let Word8Prog_word_ror_eq_word_shifts = prove
 (`!(w:N word) n.
     word_ror w n =
     word_or (word_shl w (dimindex(:N) - (n MOD dimindex(:N))))
             (word_ushr w (n MOD dimindex(:N)))`,
  REWRITE_TAC[Word64Prog_word_ror_eq_word_shifts]);;

let Word8Prog_var_word_ror_def = new_definition
  `Word8Prog_var_word_ror (w:byte) n =
     word_or (Word8Prog_var_word_lsl w (8 - (n MOD 8)))
             (Word8Prog_var_word_lsr w (n MOD 8))`;;

let Word8Prog_var_word_ror_thm = prove
 (`!w n. Word8Prog_var_word_ror w n = word_ror w n`,
  REWRITE_TAC[Word8Prog_var_word_ror_def; Word8Prog_var_word_lsl_thm;
              Word8Prog_var_word_lsr_thm; Word8Prog_word_ror_eq_word_shifts;
              DIMINDEX_8]);;

(* HOL4: the var_word theorems are [simp] *)
let _ = cake_add_simps [Word8Prog_var_word_lsl_thm; Word8Prog_var_word_lsr_thm;
                        Word8Prog_var_word_asr_thm; Word8Prog_var_word_ror_thm];;

next_ml_names := ["<<"];;
let _ = translate Word8Prog_var_word_lsl_def;;

next_ml_names := [">>"];;
let _ = translate Word8Prog_var_word_lsr_def;;

next_ml_names := ["~>>"];;
let _ = translate Word8Prog_var_word_asr_def;;

next_ml_names := ["ror"];;
let _ = translate Word8Prog_var_word_ror_def;;

(* HOL4 proves var_word_ror_side (n MOD 8 <= 8); the translator may already *)
(* have discharged it (then there is no var_word_ror_side_def)               *)
let Word8Prog_var_word_ror_side =
  if not (can tr_fetch "var_word_ror_side_def") then TRUTH else
  let side_def = SPEC_ALL (tr_fetch "var_word_ror_side_def") in
  update_precondition (GEN_ALL (prove
   (mk_iff (lhs (concl side_def), `T`),
    REWRITE_TAC[side_def] THEN
    MATCH_MP_TAC LT_IMP_LE THEN REWRITE_TAC[MOD_LT_EQ] THEN ARITH_TAC)));;

let Word8Prog_sigs = module_signatures ["fromInt"; "toInt"; "andb";
  "orb"; "xorb"; "notb"; "+"; "-"; "<<"; ">>"; "~>>"; "ror"];;

ml_prog_update (ml_prog_close_module (Some Word8Prog_sigs));;

(* if any more theorems get added here, probably should create             *)
(* Word8ProofTheory (HOL4 comment)                                          *)

let WORD_UNICITY_R = prove
 (`!f fv fv'. ml_WORD (f:byte) fv ==> (ml_WORD f fv' <=> fv' = fv)`,
  REWRITE_TAC[ml_WORD_def] THEN CONV_TAC (DEPTH_CONV BETA_CONV) THEN MESON_TAC[]);;

let WORD_UNICITY_L = prove
 (`!f f' fv. ml_WORD (f:byte) fv ==> (ml_WORD f' fv <=> f = f')`,
  REWRITE_TAC[ml_WORD_def; DIMINDEX_8] THEN CONV_TAC (DEPTH_CONV BETA_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[WORD_SHL_ZERO; WORD_ZX_TRIVIAL] THEN
  REPEAT GEN_TAC THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[injectivity "v"; injectivity "lit"] THEN MESON_TAC[]);;

let n2w_UNICITY = prove
 (`!n1 n2. n1 <= 255 ==> ((word n1:byte = word n2 /\ n2 <= 255) <=> n1 = n2)`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [STRIP_TAC THEN
    FIRST_X_ASSUM (MP_TAC o AP_TERM `val:byte->num`) THEN
    REWRITE_TAC[VAL_WORD; DIMINDEX_8] THEN CONV_TAC NUM_REDUCE_CONV THEN
    ASM_SIMP_TAC[MOD_LT; ARITH_RULE `n <= 255 ==> n < 256`];
    DISCH_THEN SUBST_ALL_TAC THEN ASM_REWRITE_TAC[]]);;

let WORD_n2w_UNICITY_L = prove
 (`!n1 n2 f. n1 <= 255 /\ ml_WORD (word n1:byte) f ==>
             (ml_WORD (word n2:byte) f /\ n2 <= 255 <=> n1 = n2)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM (fun th -> REWRITE_TAC[MATCH_MP WORD_UNICITY_L th]) THEN
  MP_TAC (SPECL [`n1:num`; `n2:num`] n2w_UNICITY) THEN ASM_REWRITE_TAC[]);;

finalise_translation ();;

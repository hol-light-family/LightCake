(* ========================================================================= *)
(* Word64Prog: port of HOL4 basis/Word64ProgScript.sml (CakeML v3479).       *)
(* Module about the built-in word64 type.                                    *)
(*                                                                           *)
(* HOL4's word operations are Library/words.ml's (hol4/words4.ml): word64 = *)
(* int64, n2w = word, w2n = val, w2i = ival, word_1comp = word_not, << =     *)
(* word_shl, >>> = word_ushr, >> = word_ishr, word_lo/hi/ls/hs = word_ult/   *)
(* ugt/ule/uge, w2w = word_zx.  HOL4's concat_word_list (wordsTheory) is not *)
(* in the library layer: it is defined here.                                 *)
(* ========================================================================= *)

needs "hol4/words4.ml";;
needs "basis/CharProg.ml";;
needs "basis/basisFunctionsLib.ml";;

type_invention_error := true;;

translation_extends "CharProg";;

(* Word64 module -- translated *)

ml_prog_update (ml_prog_open_module "Word64");;

(* HOL4 generate_sigs := true: no signatures (see ListProg.ml) *)

ml_prog_update (ml_prog_add_dec
  `Dtabbrev unknown_loc [] (implode "word") (Atapp [] (Short (implode "word64")))` I);;

(* to/from int *)
let _ = trans "fromInt" `word:num->int64`;;
let Word64_fromInt_def = tr_fetch "Word64_fromInt_def";;
let _ = trans "toInt" `val:int64->num`;;
let Word64_toInt_def = tr_fetch "Word64_toInt_def";;
let _ = trans "toIntSigned" `ival:int64->int`;;
let Word64_toIntSigned_def = tr_fetch "Word64_toIntSigned_def";;

(* bitwise operations *)
let _ = trans "andb" `word_and:int64->int64->int64`;;
let Word64Prog_Word64_andb_def = tr_fetch "Word64_andb_def";;
let _ = trans "orb" `word_or:int64->int64->int64`;;
let Word64Prog_Word64_orb_def = tr_fetch "Word64_orb_def";;
let _ = trans "xorb" `word_xor:int64->int64->int64`;;
let Word64Prog_Word64_xorb_def = tr_fetch "Word64_xorb_def";;

let Word64Prog_word_1comp_eq = prove
 (`!w:int64. word_not w = word_xor w (word 18446744073709551615)`,
  CONV_TAC WORD_BLAST);;

next_ml_names := ["notb"];;
let _ = translate Word64Prog_word_1comp_eq;;

(* arithmetic *)
let _ = trans "+" `word_add:int64->int64->int64`;;
let Word64Prog_Word64_plus_def = tr_fetch "Word64_plus_def";;
let _ = trans "-" `word_sub:int64->int64->int64`;;
let Word64Prog_Word64_minus_def = tr_fetch "Word64_minus_def";;
let _ = trans "=" `(=):int64->int64->bool`;;
let Word64Prog_Word64_eq_def = tr_fetch "Word64_eq_def";;
let _ = trans "<" `word_ult:int64->int64->bool`;;
let Word64Prog_Word64_lt_def = tr_fetch "Word64_lt_def";;
let _ = trans ">" `word_ugt:int64->int64->bool`;;
let Word64Prog_Word64_gt_def = tr_fetch "Word64_gt_def";;
let _ = trans "<=" `word_ule:int64->int64->bool`;;
let Word64Prog_Word64_le_def = tr_fetch "Word64_le_def";;
let _ = trans ">=" `word_uge:int64->int64->bool`;;
let Word64Prog_Word64_ge_def = tr_fetch "Word64_ge_def";;

(* shifts *)

let Word64Prog_var_word_lsl_def = cake_def
  `Word64Prog_var_word_lsl (w:int64) (n:num) =
     if 64 < n then word 0
     else if n < 8 then
     if n < 4 then
       if n < 2 then if n < 1 then w else word_shl w 1
       else if n < 3 then word_shl w 2
       else word_shl w 3
     else if n < 6 then if n < 5 then word_shl w 4 else word_shl w 5
     else if n < 7 then word_shl w 6
     else word_shl w 7 else Word64Prog_var_word_lsl (word_shl w 8) (n - 8)`;;

(* HOL4's proofs (ntac 32 Cases_on n) are an induction on n here: beyond   *)
(* 64 the shift is trivial, below 8 one of the cases, otherwise the        *)
(* composition of shifts                                                    *)
let BAS1AUX_VAR_SHIFT_TAC def big_tac zero compose =
  ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN MATCH_MP_TAC num_WF THEN
  X_GEN_TAC `n:num` THEN DISCH_TAC THEN X_GEN_TAC `w:int64` THEN
  ONCE_REWRITE_TAC[def] THEN
  ASM_CASES_TAC `64 < n` THEN ASM_REWRITE_TAC[] THENL [big_tac; ALL_TAC] THEN
  ASM_CASES_TAC `n < 8` THEN ASM_REWRITE_TAC[] THENL
   [UNDISCH_TAC `n < 8` THEN SPEC_TAC (`n:num`,`n:num`) THEN
    CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[zero];
    FIRST_X_ASSUM (MP_TAC o SPEC `n - 8`) THEN ANTS_TAC THENL
     [ASM_ARITH_TAC; DISCH_THEN (fun th -> REWRITE_TAC[th; compose])] THEN
    AP_TERM_TAC THEN ASM_ARITH_TAC];;

let Word64Prog_var_word_lsl_thm = prove
 (`!w n. Word64Prog_var_word_lsl w n = word_shl w n`,
  BAS1AUX_VAR_SHIFT_TAC Word64Prog_var_word_lsl_def
   (CONV_TAC SYM_CONV THEN MATCH_MP_TAC WORD_SHL_TRIVIAL THEN
    REWRITE_TAC[DIMINDEX_64] THEN ASM_ARITH_TAC)
   WORD_SHL_ZERO WORD_SHL_COMPOSE);;

let Word64Prog_var_word_lsr_def = cake_def
  `Word64Prog_var_word_lsr (w:int64) (n:num) =
     if 64 < n then word 0
     else if n < 8 then
     if n < 4 then
       if n < 2 then if n < 1 then w else word_ushr w 1
       else if n < 3 then word_ushr w 2
       else word_ushr w 3
     else if n < 6 then if n < 5 then word_ushr w 4 else word_ushr w 5
     else if n < 7 then word_ushr w 6
     else word_ushr w 7 else Word64Prog_var_word_lsr (word_ushr w 8) (n - 8)`;;

let Word64Prog_var_word_lsr_thm = prove
 (`!w n. Word64Prog_var_word_lsr w n = word_ushr w n`,
  BAS1AUX_VAR_SHIFT_TAC Word64Prog_var_word_lsr_def
   (CONV_TAC SYM_CONV THEN REWRITE_TAC[WORD_USHR_EQ_0] THEN
    MATCH_MP_TAC LTE_TRANS THEN EXISTS_TAC `2 EXP 64` THEN
    REWRITE_TAC[REWRITE_RULE[DIMINDEX_64] (ISPEC `w:int64` VAL_BOUND)] THEN
    REWRITE_TAC[LE_EXP; ARITH_EQ] THEN ASM_ARITH_TAC)
   WORD_USHR_ZERO WORD_USHR_COMPOSE);;

let Word64Prog_var_word_asr_def = cake_def
  `Word64Prog_var_word_asr (w:int64) (n:num) =
     if 64 < n then word_ishr w 64
     else if n < 8 then
     if n < 4 then
       if n < 2 then if n < 1 then w else word_ishr w 1
       else if n < 3 then word_ishr w 2
       else word_ishr w 3
     else if n < 6 then if n < 5 then word_ishr w 4 else word_ishr w 5
     else if n < 7 then word_ishr w 6
     else word_ishr w 7 else Word64Prog_var_word_asr (word_ishr w 8) (n - 8)`;;

let Word64Prog_var_word_asr_thm = prove
 (`!w n. Word64Prog_var_word_asr w n = word_ishr w n`,
  BAS1AUX_VAR_SHIFT_TAC Word64Prog_var_word_asr_def
   (REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_ISHR; DIMINDEX_64] THEN
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    ASM_SIMP_TAC[ARITH_RULE `~(i + 64 < 64)`; ARITH_RULE `64 < n ==> ~(i + n < 64)`])
   WORD_ISHR_ZERO WORD_ISHR_COMPOSE);;

let Word64Prog_word_ror_eq_word_shifts = prove
 (`!(w:N word) n.
     word_ror w n =
     word_or (word_shl w (dimindex(:N) - (n MOD dimindex(:N))))
             (word_ushr w (n MOD dimindex(:N)))`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[WORD_ROR_MOD] THEN
  SIMP_TAC[WORD_ROR_SHIFTS; MOD_LT_EQ; DIMINDEX_NONZERO; LT_IMP_LE] THEN
  MATCH_ACCEPT_TAC WORD_OR_SYM);;

let Word64Prog_var_word_ror_def = new_definition
  `Word64Prog_var_word_ror (w:int64) n =
     word_or (Word64Prog_var_word_lsl w (64 - (n MOD 64)))
             (Word64Prog_var_word_lsr w (n MOD 64))`;;

let Word64Prog_var_word_ror_thm = prove
 (`!w n. Word64Prog_var_word_ror w n = word_ror w n`,
  REWRITE_TAC[Word64Prog_var_word_ror_def; Word64Prog_var_word_lsl_thm;
              Word64Prog_var_word_lsr_thm; Word64Prog_word_ror_eq_word_shifts;
              DIMINDEX_64]);;

(* HOL4: the var_word theorems are [simp] *)
let _ = cake_add_simps [Word64Prog_var_word_lsl_thm; Word64Prog_var_word_lsr_thm;
                        Word64Prog_var_word_asr_thm; Word64Prog_var_word_ror_thm];;

next_ml_names := ["<<"];;
let _ = translate Word64Prog_var_word_lsl_def;;

next_ml_names := [">>"];;
let _ = translate Word64Prog_var_word_lsr_def;;

next_ml_names := ["~>>"];;
let _ = translate Word64Prog_var_word_asr_def;;

next_ml_names := ["ror"];;
let _ = translate Word64Prog_var_word_ror_def;;

(* HOL4 proves var_word_ror_side (n MOD 64 <= 64); the translator may       *)
(* already have discharged it (then there is no var_word_ror_side_def)       *)
let Word64Prog_var_word_ror_side =
  if not (can tr_fetch "var_word_ror_side_def") then TRUTH else
  update_precondition (prove
   (`!w n. var_word_ror_side w n <=> T`,
    REWRITE_TAC[tr_fetch "var_word_ror_side_def"] THEN REPEAT GEN_TAC THEN
    MATCH_MP_TAC LT_IMP_LE THEN REWRITE_TAC[MOD_LT_EQ] THEN ARITH_TAC));;

(* HOL4 wordsTheory concat_word_list (not in the library layer) *)
let concat_word_list_def = cake_def
  `(concat_word_list ([]:(N word)list) = (word 0:M word)) /\
   (concat_word_list (CONS (h:N word) t) =
      word_or (word_zx h) (word_shl (concat_word_list t:M word) (dimindex(:N))))`;;

let concat_all_def = new_definition
  `concat_all (a:byte) b c d e f g h =
     (concat_word_list [a;b;c;d;e;f;g;h]:int64)`;;

let concat_all_impl =
  REWRITE_RULE [concat_word_list_def; DIMINDEX_8; WORD_SHL_0; WORD_OR_0] concat_all_def;;

next_ml_names := ["concatAll"];;
let _ = translate concat_all_impl;;

let Word64Prog_sigs = module_signatures ["fromInt"; "toInt"; "andb";
  "orb"; "xorb"; "notb"; "+"; "-"; "<<"; ">>"; "~>>"; "concatAll"];;

ml_prog_update (ml_prog_close_module (Some Word64Prog_sigs));;

finalise_translation ();;

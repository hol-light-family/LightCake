(* ========================================================================= *)
(* Marshalling: port of HOL4 basis/MarshallingScript.sml (CakeML v3479).     *)
(* HOL functions that aid converting to and from the byte arrays that        *)
(* CakeML foreign-function interface (FFI) uses.                             *)
(*                                                                           *)
(* Notes on the rendering:                                                   *)
(* - word8 is byte, n2w is word and w2n is val (hol4/words4.ml); the HOL4    *)
(*   powers of 256 are 256 EXP k.                                            *)
(* - w22n and w82n have one clause each (lists of length 2 and 8), as in     *)
(*   HOL4; the kit completes them with ARB, as HOL4's TFL does.              *)
(* - Helpers that are not HOL4 theorems have the prefix BAS0AUX_.            *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "hol4/words4.ml";;

type_invention_error := true;;

(* encode/decode nums as 2 or 8 bytes *)
(* similar to n2l and l2n but with padding *)

let n2w2_def = cake_def
  `n2w2 (i:num) = [word (i DIV 256):byte; word i]`;;

let n2w8_def = cake_def
  `n2w8 (i:num) =
     [word (i DIV 256 EXP 7):byte; word (i DIV 256 EXP 6);
      word (i DIV 256 EXP 5); word (i DIV 256 EXP 4);
      word (i DIV 256 EXP 3); word (i DIV 256 EXP 2);
      word (i DIV 256); word i]`;;

let w22n_def = cake_def
  `w22n [b1; b0:byte] = val b1 * 256 + val b0`;;

let w82n_def = cake_def
  `w82n [b7; b6; b5; b4; b3; b2; b1; b0:byte] =
     256 * (256 * (256 * (256 * (256 * (256 * (256 *
     val b7 + val b6) + val b5) + val b4) + val b3) + val b2) + val b1) +
     val b0`;;

(* arithmetic of one byte *)

let BAS0AUX_VAL_WORD_BYTE = prove
 (`!n. val (word n:byte) = n MOD 256`,
  REWRITE_TAC[VAL_WORD; DIMINDEX_8] THEN CONV_TAC NUM_REDUCE_CONV);;

let BAS0AUX_DIV_MOD_256 = prove
 (`!x. 256 * (x DIV 256) + x MOD 256 = x`,
  GEN_TAC THEN MP_TAC(SPECL [`x:num`; `256`] DIVISION) THEN
  CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC);;

let BAS0AUX_DIV_BYTE = prove
 (`!a (b:byte). (256 * a + val b) DIV 256 = a`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC DIV_UNIQ THEN EXISTS_TAC `val (b:byte)` THEN
  REWRITE_TAC[w2n_lt_256] THEN ARITH_TAC);;

let BAS0AUX_WORD_BYTE = prove
 (`!a (b:byte). word (256 * a + val b):byte = b`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[GSYM VAL_EQ] THEN
  REWRITE_TAC[BAS0AUX_VAL_WORD_BYTE; MOD_MULT_ADD] THEN
  SIMP_TAC[MOD_LT; w2n_lt_256]);;

(* n2w8 with the divisions by 256 one at a time *)

let BAS0AUX_n2w8_ALT = prove
 (`!i. n2w8 i =
       [word (i DIV 256 DIV 256 DIV 256 DIV 256 DIV 256 DIV 256 DIV 256):byte;
        word (i DIV 256 DIV 256 DIV 256 DIV 256 DIV 256 DIV 256);
        word (i DIV 256 DIV 256 DIV 256 DIV 256 DIV 256);
        word (i DIV 256 DIV 256 DIV 256 DIV 256);
        word (i DIV 256 DIV 256 DIV 256); word (i DIV 256 DIV 256);
        word (i DIV 256); word i]`,
  REWRITE_TAC[n2w8_def; DIV_DIV] THEN CONV_TAC NUM_REDUCE_CONV);;

let w22n_n2w2 = prove
 (`!i. i < 2 EXP (2 * 8) ==> w22n (n2w2 i) = i`,
  GEN_TAC THEN CONV_TAC(LAND_CONV NUM_REDUCE_CONV) THEN DISCH_TAC THEN
  REWRITE_TAC[n2w2_def; w22n_def; BAS0AUX_VAL_WORD_BYTE] THEN
  SUBGOAL_THEN `(i DIV 256) MOD 256 = i DIV 256` SUBST1_TAC THENL
   [MATCH_MP_TAC MOD_LT THEN SIMP_TAC[RDIV_LT_EQ; ARITH_EQ] THEN
    ASM_ARITH_TAC;
    ONCE_REWRITE_TAC[MULT_SYM] THEN REWRITE_TAC[BAS0AUX_DIV_MOD_256]]);;

let n2w2_w22n = prove
 (`!b:byte list. LENGTH b = 2 ==> n2w2 (w22n b) = b`,
  GEN_TAC THEN REWRITE_TAC[LENGTH_EQ_NUM_compute; ARITH] THEN
  DISCH_THEN CAKE_STRIP_ASSUME_TAC THEN ASM_REWRITE_TAC[w22n_def; n2w2_def] THEN
  ONCE_REWRITE_TAC[MULT_SYM] THEN
  REWRITE_TAC[BAS0AUX_DIV_BYTE; BAS0AUX_WORD_BYTE; WORD_VAL]);;

let w82n_n2w8 = prove
 (`!i. i <= 256 EXP 8 - 1 ==> w82n (n2w8 i) = i`,
  GEN_TAC THEN CONV_TAC(LAND_CONV NUM_REDUCE_CONV) THEN DISCH_TAC THEN
  REWRITE_TAC[BAS0AUX_n2w8_ALT; w82n_def; BAS0AUX_VAL_WORD_BYTE] THEN
  SUBGOAL_THEN
   `(i DIV 256 DIV 256 DIV 256 DIV 256 DIV 256 DIV 256 DIV 256) MOD 256 =
    i DIV 256 DIV 256 DIV 256 DIV 256 DIV 256 DIV 256 DIV 256`
  SUBST1_TAC THENL
   [MATCH_MP_TAC MOD_LT THEN REWRITE_TAC[DIV_DIV] THEN
    CONV_TAC NUM_REDUCE_CONV THEN SIMP_TAC[RDIV_LT_EQ; ARITH_EQ] THEN
    ASM_ARITH_TAC;
    REWRITE_TAC[BAS0AUX_DIV_MOD_256]]);;

let nw8_w8n = prove
 (`!b:byte list. LENGTH b = 8 ==> n2w8 (w82n b) = b`,
  GEN_TAC THEN REWRITE_TAC[LENGTH_EQ_NUM_compute; ARITH] THEN
  DISCH_THEN CAKE_STRIP_ASSUME_TAC THEN
  ASM_REWRITE_TAC[BAS0AUX_n2w8_ALT; w82n_def] THEN
  REWRITE_TAC[BAS0AUX_DIV_BYTE; BAS0AUX_WORD_BYTE; WORD_VAL]);;

let LENGTH_n2w2 = prove
 (`!n. LENGTH (n2w2 n) = 2`,
  REWRITE_TAC[n2w2_def; LENGTH] THEN CONV_TAC NUM_REDUCE_CONV);;

let LENGTH_n2w8 = prove
 (`!n. LENGTH (n2w8 n) = 8`,
  REWRITE_TAC[n2w8_def; LENGTH] THEN CONV_TAC NUM_REDUCE_CONV);;

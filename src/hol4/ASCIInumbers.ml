(* ========================================================================= *)
(* ASCIInumbers: port of HOL4 src/string/ASCIInumbersScript.sml (the HOL4    *)
(* library of CakeML v3479): string-to-from-number maps.                     *)
(* HOL4 toString and toNum are overloads for num_to_dec_string and           *)
(* num_from_dec_string; character literals #"0" are CHR 48 (string4.ml).     *)
(* Helper lemmas that are not HOL4 theorems have the prefix LSTRAUX_.        *)
(* ========================================================================= *)

needs "hol4/vocab.ml";;
needs "hol4/string4.ml";;
needs "hol4/numposrep.ml";;

prioritize_num();;
type_invention_error := true;;

let s2n_def = new_definition
  `s2n b (f:char->num) (s:string) = l2n b (MAP f (REVERSE s))`;;

let n2s_def = new_definition
  `n2s b (f:num->char) n = REVERSE (MAP f (n2l b n))`;;

(* HOL4: CHR (ORD #"0" + n) and CHR (ORD #"A" + (n - 10))                    *)

let HEX = new_definition
  `HEX n = if n < 10 then CHR (48 + n) else
           if n < 16 then CHR (65 + (n - 10)) else CHR 0`;;

let HEX_def = prove
 (`HEX 0 = CHR 48 /\ HEX 1 = CHR 49 /\ HEX 2 = CHR 50 /\ HEX 3 = CHR 51 /\
   HEX 4 = CHR 52 /\ HEX 5 = CHR 53 /\ HEX 6 = CHR 54 /\ HEX 7 = CHR 55 /\
   HEX 8 = CHR 56 /\ HEX 9 = CHR 57 /\ HEX 10 = CHR 65 /\ HEX 11 = CHR 66 /\
   HEX 12 = CHR 67 /\ HEX 13 = CHR 68 /\ HEX 14 = CHR 69 /\ HEX 15 = CHR 70`,
  REWRITE_TAC[HEX] THEN CONV_TAC NUM_REDUCE_CONV);;

(* HOL4: let n = ORD c in ...; ORD #"0" = 48, ORD #"9" = 57, ORD #"a" = 97,  *)
(* ORD #"f" = 102, ORD #"A" = 65, ORD #"F" = 70                              *)

let UNHEX = new_definition
  `UNHEX c = if 48 <= ORD c /\ ORD c <= 57 then ORD c - 48 else
             if 97 <= ORD c /\ ORD c <= 102 then (10 + ORD c) - 97 else
             if 65 <= ORD c /\ ORD c <= 70 then (10 + ORD c) - 65 else 0`;;

let UNHEX_def = prove
 (`UNHEX (CHR 48) = 0 /\ UNHEX (CHR 49) = 1 /\
   UNHEX (CHR 50) = 2 /\ UNHEX (CHR 51) = 3 /\
   UNHEX (CHR 52) = 4 /\ UNHEX (CHR 53) = 5 /\
   UNHEX (CHR 54) = 6 /\ UNHEX (CHR 55) = 7 /\
   UNHEX (CHR 56) = 8 /\ UNHEX (CHR 57) = 9 /\
   UNHEX (CHR 97) = 10 /\ UNHEX (CHR 98) = 11 /\ UNHEX (CHR 99) = 12 /\
   UNHEX (CHR 100) = 13 /\ UNHEX (CHR 101) = 14 /\ UNHEX (CHR 102) = 15 /\
   UNHEX (CHR 65) = 10 /\ UNHEX (CHR 66) = 11 /\ UNHEX (CHR 67) = 12 /\
   UNHEX (CHR 68) = 13 /\ UNHEX (CHR 69) = 14 /\ UNHEX (CHR 70) = 15`,
  REWRITE_TAC[UNHEX; LSTRAUX_ORD_CHR_MOD] THEN CONV_TAC NUM_REDUCE_CONV);;

let num_from_bin_string_def = new_definition
  `num_from_bin_string = s2n 2 UNHEX`;;

let num_from_oct_string_def = new_definition
  `num_from_oct_string = s2n 8 UNHEX`;;

let num_from_dec_string_def = new_definition
  `num_from_dec_string = s2n 10 UNHEX`;;

let num_from_hex_string_def = new_definition
  `num_from_hex_string = s2n 16 UNHEX`;;

let num_to_bin_string_def = new_definition
  `num_to_bin_string = n2s 2 HEX`;;

let num_to_oct_string_def = new_definition
  `num_to_oct_string = n2s 8 HEX`;;

let num_to_dec_string_def = new_definition
  `num_to_dec_string = n2s 10 HEX`;;

let num_to_hex_string_def = new_definition
  `num_to_hex_string = n2s 16 HEX`;;

(* ------------------------------------------------------------------------- *)
(* Leading zeroes, HEX and UNHEX.                                            *)
(* ------------------------------------------------------------------------- *)

let s2n_leading_zeroes = prove
 (`!b t. 0 < b ==> s2n b UNHEX (CONS (CHR 48) t) = s2n b UNHEX t`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[s2n_def; REVERSE; MAP_APPEND; l2n_APPEND; MAP; UNHEX_def;
              l2n_def; MOD_0] THEN
  ARITH_TAC);;

let num_from_X_string_leading_zeroes = prove
 (`!t. num_from_bin_string (CONS (CHR 48) t) = num_from_bin_string t /\
       num_from_oct_string (CONS (CHR 48) t) = num_from_oct_string t /\
       num_from_dec_string (CONS (CHR 48) t) = num_from_dec_string t /\
       num_from_hex_string (CONS (CHR 48) t) = num_from_hex_string t`,
  SIMP_TAC[num_from_bin_string_def; num_from_oct_string_def;
           num_from_dec_string_def; num_from_hex_string_def;
           s2n_leading_zeroes; ARITH]);;

let UNHEX_HEX = prove
 (`!n. n < 16 ==> UNHEX (HEX n) = n`,
  CONV_TAC EXPAND_CASES_CONV THEN REWRITE_TAC[HEX_def; UNHEX_def]);;

(* a character c = CHR m (m < 256), all definitions unfolded, every case     *)

let LSTRAUX_CHAR_TAC =
  MATCH_MP_TAC CHAR_INDUCT_THM THEN X_GEN_TAC `m:num` THEN DISCH_TAC THEN
  ASM_SIMP_TAC[HEX; UNHEX; toUpper_def; isHexDigit_def; isDigit_def;
               isLower_def; ORD_CHR_RWT] THEN
  REPEAT STRIP_TAC THEN
  REPEAT (COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
  TRY (AP_TERM_TAC THEN ASM_ARITH_TAC) THEN ASM_ARITH_TAC;;

let HEX_UNHEX = prove
 (`!c. isHexDigit c ==> HEX (UNHEX c) = toUpper c`,
  LSTRAUX_CHAR_TAC);;

let DEC_UNDEC = prove
 (`!c. isDigit c ==> HEX (UNHEX c) = c`,
  LSTRAUX_CHAR_TAC);;

(* ------------------------------------------------------------------------- *)
(* Round trips.                                                              *)
(* ------------------------------------------------------------------------- *)

let s2n_n2s = prove
 (`!c2n n2c b n. 1 < b /\ (!x. x < b ==> c2n (n2c x) = x)
                 ==> s2n b c2n (n2s b n2c n) = n`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[s2n_def; n2s_def; REVERSE_REVERSE; GSYM MAP_o] THEN
  SUBGOAL_THEN `MAP ((c2n:char->num) o n2c) (n2l b n) = n2l b n` SUBST1_TAC THENL
   [MATCH_MP_TAC MAP_EQ_DEGEN THEN
    MP_TAC(SPECL [`b:num`; `n:num`] n2l_BOUND) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC MONO_ALL THEN ASM_SIMP_TAC[o_THM; GT];
    ASM_SIMP_TAC[l2n_n2l]]);;

let toNum_toString = prove
 (`!n. num_from_dec_string (num_to_dec_string n) = n`,
  GEN_TAC THEN REWRITE_TAC[num_to_dec_string_def; num_from_dec_string_def] THEN
  MATCH_MP_TAC s2n_n2s THEN REWRITE_TAC[ARITH] THEN
  CONV_TAC EXPAND_CASES_CONV THEN REWRITE_TAC[HEX_def; UNHEX_def]);;

let toString_toNum_cancel = toNum_toString;;

let toString_inj = prove
 (`!n m. num_to_dec_string n = num_to_dec_string m <=> n = m`,
  MESON_TAC[toNum_toString]);;

let toString_11 = toString_inj;;

let STRCAT_toString_inj = prove
 (`!n m s. APPEND s (num_to_dec_string n) = APPEND s (num_to_dec_string m) <=>
           n = m`,
  REWRITE_TAC[APPEND_LCANCEL; toString_inj]);;

let LSTRAUX_NUM_STRING_TAC =
  REWRITE_TAC[FUN_EQ_THM; o_THM; I_THM;
              num_from_bin_string_def; num_from_oct_string_def;
              num_from_dec_string_def; num_from_hex_string_def;
              num_to_bin_string_def; num_to_oct_string_def;
              num_to_dec_string_def; num_to_hex_string_def] THEN
  GEN_TAC THEN MATCH_MP_TAC s2n_n2s THEN REWRITE_TAC[ARITH] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC UNHEX_HEX THEN ASM_ARITH_TAC;;

let num_bin_string = prove
 (`num_from_bin_string o num_to_bin_string = I`,
  LSTRAUX_NUM_STRING_TAC);;

let num_oct_string = prove
 (`num_from_oct_string o num_to_oct_string = I`,
  LSTRAUX_NUM_STRING_TAC);;

let num_dec_string = prove
 (`num_from_dec_string o num_to_dec_string = I`,
  LSTRAUX_NUM_STRING_TAC);;

let num_hex_string = prove
 (`num_from_hex_string o num_to_hex_string = I`,
  LSTRAUX_NUM_STRING_TAC);;

let LSTRAUX_ALL_REVERSE = prove
 (`!(P:A->bool) l. ALL P (REVERSE l) <=> ALL P l`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[REVERSE; ALL; ALL_APPEND] THEN CONV_TAC TAUT);;

let LSTRAUX_MAP_TAKE = prove
 (`!(f:A->B) l n. TAKE n (MAP f l) = MAP f (TAKE n l)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[MAP; TAKE_DEF] THEN
  GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[MAP]);;

let n2s_s2n = prove
 (`!c2n n2c b s.
     1 < b /\ ALL ((>) b o c2n) s ==>
     n2s b n2c (s2n b c2n s) =
     if s2n b c2n s = 0 then CONS (n2c 0) []
     else MAP (n2c o c2n) (LASTN (SUC (LOG b (s2n b c2n s))) s)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `ALL ((>) b) (MAP (c2n:char->num) (REVERSE s))` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[ALL_MAP; LSTRAUX_ALL_REVERSE]; ALL_TAC] THEN
  REWRITE_TAC[n2s_def] THEN REWRITE_TAC[s2n_def] THEN
  ASM_SIMP_TAC[n2l_l2n] THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[MAP; REVERSE; APPEND] THEN
  REWRITE_TAC[LSTRAUX_MAP_TAKE; GSYM MAP_o; MAP_REVERSE; LASTN_DEF]);;

(* ------------------------------------------------------------------------- *)
(* Non-emptiness, digits, lengths.                                           *)
(* ------------------------------------------------------------------------- *)

let LSTRAUX_N2L_NOT_NIL = prove
 (`!b n. ~(n2l b n = [])`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[n2l_def] THEN
  COND_CASES_TAC THEN REWRITE_TAC[NOT_CONS_NIL]);;

let LSTRAUX_NUM_STRING_NIL_TAC =
  REWRITE_TAC[num_to_bin_string_def; num_to_oct_string_def;
              num_to_dec_string_def; num_to_hex_string_def; n2s_def] THEN
  REWRITE_TAC[GSYM LENGTH_EQ_NIL; LENGTH_REVERSE; LENGTH_MAP] THEN
  REWRITE_TAC[LENGTH_EQ_NIL; LSTRAUX_N2L_NOT_NIL];;

let num_to_bin_string_nil = prove
 (`!n. ~(num_to_bin_string n = [])`,
  LSTRAUX_NUM_STRING_NIL_TAC);;

let num_to_oct_string_nil = prove
 (`!n. ~(num_to_oct_string n = [])`,
  LSTRAUX_NUM_STRING_NIL_TAC);;

let num_to_dec_string_nil = prove
 (`!n. ~(num_to_dec_string n = [])`,
  LSTRAUX_NUM_STRING_NIL_TAC);;

let num_to_hex_string_nil = prove
 (`!n. ~(num_to_hex_string n = [])`,
  LSTRAUX_NUM_STRING_NIL_TAC);;

let isDigit_HEX = prove
 (`!n. n < 10 ==> isDigit (HEX n)`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[HEX; isDigit_def] THEN
  ASM_SIMP_TAC[ORD_CHR_RWT; ARITH_RULE `n < 10 ==> 48 + n < 256`] THEN
  ASM_ARITH_TAC);;

let isHexDigit_HEX = prove
 (`!n. n < 16 ==> isHexDigit (HEX n) /\ (isAlpha (HEX n) ==> isUpper (HEX n))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[HEX] THEN
  REWRITE_TAC[isHexDigit_def; isAlpha_def; isLower_def; isUpper_def] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[ORD_CHR_RWT;
               ARITH_RULE `n < 16 ==> 48 + n < 256 /\ 65 + (n - 10) < 256`] THEN
  ASM_ARITH_TAC);;

let EVERY_isDigit_num_to_dec_string = prove
 (`!n. ALL isDigit (num_to_dec_string n)`,
  GEN_TAC THEN
  REWRITE_TAC[num_to_dec_string_def; n2s_def; LSTRAUX_ALL_REVERSE; ALL_MAP] THEN
  MP_TAC(SPECL [`10`; `n:num`] n2l_BOUND) THEN REWRITE_TAC[ARITH] THEN
  MATCH_MP_TAC MONO_ALL THEN REWRITE_TAC[o_THM; GT; isDigit_HEX]);;

let EVERY_isHexDigit_num_to_hex_string = prove
 (`!n. ALL (\c. isHexDigit c /\ (isAlpha c ==> isUpper c))
           (num_to_hex_string n)`,
  GEN_TAC THEN
  REWRITE_TAC[num_to_hex_string_def; n2s_def; LSTRAUX_ALL_REVERSE; ALL_MAP] THEN
  MP_TAC(SPECL [`16`; `n:num`] n2l_BOUND) THEN REWRITE_TAC[ARITH] THEN
  MATCH_MP_TAC MONO_ALL THEN REWRITE_TAC[o_THM; GT; isHexDigit_HEX]);;

let LSTRAUX_LENGTH_NUM_STRING_TAC =
  GEN_TAC THEN
  REWRITE_TAC[num_to_bin_string_def; num_to_oct_string_def;
              num_to_dec_string_def; num_to_hex_string_def; n2s_def] THEN
  SIMP_TAC[LENGTH_REVERSE; LENGTH_MAP; LENGTH_n2l; ARITH; ADD1];;

let LENGTH_num_to_dec_string = prove
 (`!n. LENGTH (num_to_dec_string n) = if n = 0 then 1 else LOG 10 n + 1`,
  LSTRAUX_LENGTH_NUM_STRING_TAC);;

let LENGTH_num_to_hex_string = prove
 (`!n. LENGTH (num_to_hex_string n) = if n = 0 then 1 else LOG 16 n + 1`,
  LSTRAUX_LENGTH_NUM_STRING_TAC);;

let LENGTH_num_to_bin_string = prove
 (`!n. LENGTH (num_to_bin_string n) = if n = 0 then 1 else LOG 2 n + 1`,
  LSTRAUX_LENGTH_NUM_STRING_TAC);;

let LENGTH_num_to_oct_string = prove
 (`!n. LENGTH (num_to_oct_string n) = if n = 0 then 1 else LOG 8 n + 1`,
  LSTRAUX_LENGTH_NUM_STRING_TAC);;

(* ------------------------------------------------------------------------- *)
(* HOL4 [simp] theorems.                                                     *)
(* ------------------------------------------------------------------------- *)

let _ = cake_add_simps
  [num_from_X_string_leading_zeroes; toNum_toString; toString_inj;
   num_to_bin_string_nil; num_to_oct_string_nil; num_to_dec_string_nil;
   num_to_hex_string_nil];;

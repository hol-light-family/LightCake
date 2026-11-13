(* ========================================================================= *)
(* words4: port of the HOL4 word library that CakeML v3479 uses: words       *)
(* (src/n-bit/wordsScript.sml), fcp, bit, integer_word, byte, alignment,     *)
(* address (examples/machine-code/hoare-triple), and the integer theory      *)
(* rows (floor division, HOL4 names of int.ml theorems).  The bitstring      *)
(* rows are in hol4/bitstring.ml.                                            *)
(*                                                                           *)
(* HOL Light's Library/words.ml (loaded by the prelude) is the base: its     *)
(* constants are used wherever HOL4 means the same, so HOL4 terms read:      *)
(*   'a word = N word (bool['a]); word8 = byte; word16/32/64 = int16/32/64;  *)
(*   wordK = (K)word; 'a + 'b as an index type (word_join) =                 *)
(*   (A,B)finite_sum, written ((A,B)finite_sum)word; dimindex(:'a) =         *)
(*   dimindex(:N); n2w n = word n (numeral 5w = word 5); w2n = val;          *)
(*   w2w = word_zx; sw2sw = word_sx; w2i = ival; i2w = iword;                *)
(*   w ' i = bit i w; word_bit i w = bit i w;                                *)
(*   FCP i. P i = word_of_bits (\i. P i);                                    *)
(*   + = word_add; binary - = word_sub; multiplication = word_mul;          *)
(*   unary - (word_2comp) = word_neg; ~ (word_1comp) = word_not;            *)
(*   && = word_and; || = word_or; ?? = word_xor;                            *)
(*   << (word_lsl) = word_shl; >>> (word_lsr) = word_ushr;                  *)
(*   >> (word_asr) = word_ishr; #>> = word_ror; #<< = word_rol;             *)
(*   // (word_div) = word_udiv; word_mod = word_umod;                       *)
(*   / on words (word_quot) = word_jdiv; word_rem = word_jrem;              *)
(*   <+ (word_lo) = word_ult; <=+ (word_ls) = word_ule; >+ = word_ugt;      *)
(*   >=+ = word_uge; < (word_lt) = word_ilt; <= = word_ile; > = word_igt;   *)
(*   >= = word_ige; word_min/max = word_umin/umax; word_smin/smax =         *)
(*   word_imin/imax; UINT_MAXw = word_T = Tw = -1w = word_UINT_MAX          *)
(*   (= word_neg (word 1)); INT_MINw = word_L = word_INT_MIN;               *)
(*   INT_MAXw = word_H = word_INT_MAX;                                       *)
(*   @@ (word_concat) = word_join (result type free); HOL4 word_join =      *)
(*   word_join at result type (M,N)finite_sum;                              *)
(*   bit_field_insert h l a w = word_insert w (l,(h + 1) - l) a;            *)
(*   BIT i n = numbit i n; int ABS = abs; Num = num_of_int (non-negative    *)
(*   arguments); int / = int_div and int % = integer_int_mod (HOL4 floor    *)
(*   division; HOL Light's div and rem are Euclidean, int_mod is the        *)
(*   congruence).                                                            *)
(* Defined here with their HOL4 names (HOL Light has no equivalent):         *)
(*   dimword INT_MIN INT_MAX UINT_MAX (numbers, as in HOL4 words),           *)
(*   word_msb word_lsb nzcv, word_bits (h -- l), word_extract (h >< l),      *)
(*   word_slice (h '' l); BITS LOG2 MOD_2EXP SBIT BITWISE (bit) and LOG      *)
(*   (logroot, for LOG2_def); int_div integer_int_mod (integer);             *)
(*   integer_word_INT_MIN/_INT_MAX/_UINT_MAX (the ints of integer_word);     *)
(*   bytes_in_word byte_index word_slice_alt set_byte get_byte               *)
(*   bytes_to_word word_of_bytes word_to_bytes_aux word_to_bytes (byte);     *)
(*   align byte_align byte_aligned and alignment_aligned = HOL4 aligned      *)
(*   (HOL Light's aligned n w means that n divides val w) (alignment);       *)
(*   CONTAINER (address).  LOG2_CONV evaluates LOG2 of numerals.             *)
(* Prefixed HOL4 theorem names (HOL Light has the name with another          *)
(* statement): fcp_CART_EQ, words_WORD_AND_ASSOC, words_WORD_OR_ASSOC,       *)
(* integer_INT_ABS, integer_INT_LT, integer_INT_SUB, integer_NUM_OF_INT,     *)
(* integer_int_le, integer_int_ge, integer_int_gt, integer_int_sub,          *)
(* integer_word_INT_MIN_def, integer_word_INT_MAX_def.                       *)
(* Where a definition comes out in another form or quantifier order, it is  *)
(* bound as NAME_DEF and NAME_def is the HOL4 statement.  Helpers that are   *)
(* lemmas of another unit's theory have the prefix WORDSAUX_.                *)
(* ========================================================================= *)

needs "hol4/vocab.ml";;

prioritize_num();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* bit: port of HOL4 src/num/extra_theories/bitScript.sml (only what the     *)
(* closure uses).  HOL4 BIT is HOL Light's numbit (words.ml).                *)
(* ------------------------------------------------------------------------- *)

let MOD_2EXP_DEF = new_definition
  `MOD_2EXP x n = n MOD 2 EXP x`;;

let MOD_2EXP_def = prove
 (`!x n. MOD_2EXP x n = n MOD 2 EXP x`,
  REWRITE_TAC[MOD_2EXP_DEF]);;

(* HOL4: BITS_def via MOD_2EXP and DIV_2EXP; BITS_THM is that equation.     *)

let BITS_DEF = new_definition
  `BITS h l n = (n DIV 2 EXP l) MOD 2 EXP (SUC h - l)`;;

let BITS_THM = prove
 (`!h l n. BITS h l n = (n DIV 2 EXP l) MOD 2 EXP (SUC h - l)`,
  REWRITE_TAC[BITS_DEF]);;

(* local arithmetic helpers (arithmetic theory, other unit) *)

let WORDSAUX_EXP2_LT = prove
 (`!m n. 2 EXP m < 2 EXP n <=> m < n`,
  REWRITE_TAC[LT_EXP] THEN ARITH_TAC);;

let WORDSAUX_EXP2_LE = prove
 (`!m n. 2 EXP m <= 2 EXP n <=> m <= n`,
  REWRITE_TAC[LE_EXP] THEN ARITH_TAC);;

(* logroot LOG (a new_specification in HOL4), needed for LOG2_def.          *)

let LOG_DEF = new_definition
  `LOG a n = minimal k. n < a EXP SUC k`;;

let LOG = prove
 (`!a n. 1 < a /\ 0 < n ==> a EXP LOG a n <= n /\ n < a EXP SUC (LOG a n)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `?k. n < a EXP SUC k` MP_TAC THENL
   [EXISTS_TAC `n:num` THEN TRANS_TAC LTE_TRANS `2 EXP n` THEN
    REWRITE_TAC[LT_POW2_REFL] THEN TRANS_TAC LE_TRANS `a EXP n` THEN
    ASM_SIMP_TAC[EXP_MONO_LE; ARITH_RULE `1 < a ==> 2 <= a`] THEN
    REWRITE_TAC[LE_EXP] THEN ASM_ARITH_TAC;
    GEN_REWRITE_TAC LAND_CONV [MINIMAL] THEN REWRITE_TAC[GSYM LOG_DEF] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `LOG a n = 0` THEN ASM_REWRITE_TAC[EXP] THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `LOG a n - 1`) THEN
    ASM_SIMP_TAC[ARITH_RULE `~(k = 0) ==> k - 1 < k /\ SUC (k - 1) = k`] THEN
    ARITH_TAC]);;

let LOG2_def = new_definition
  `LOG2 = LOG 2`;;

let LOG2_PROPERTY = prove
 (`!n. 0 < n ==> 2 EXP LOG2 n <= n /\ n < 2 EXP SUC (LOG2 n)`,
  REWRITE_TAC[LOG2_def] THEN MESON_TAC[LOG; ARITH_RULE `1 < 2`]);;

let LOG2_UNIQUE = prove
 (`!n p. 2 EXP p <= n /\ n < 2 EXP SUC p ==> LOG2 n = p`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `n:num` LOG2_PROPERTY) THEN ANTS_TAC THENL
   [MP_TAC(SPEC `p:num` EXP_2_NE_0) THEN ASM_ARITH_TAC; STRIP_TAC] THEN
  SUBGOAL_THEN `2 EXP LOG2 n < 2 EXP SUC p /\ 2 EXP p < 2 EXP SUC (LOG2 n)`
  MP_TAC THENL
   [ASM_ARITH_TAC; REWRITE_TAC[WORDSAUX_EXP2_LT] THEN ARITH_TAC]);;

let LOG2_TWOEXP = prove
 (`!n. LOG2 (2 EXP n) = n`,
  GEN_TAC THEN MATCH_MP_TAC LOG2_UNIQUE THEN
  REWRITE_TAC[LE_REFL; LT_EXP] THEN ARITH_TAC);;

let BIT0_ODD = prove
 (`numbit 0 = ODD`,
  REWRITE_TAC[FUN_EQ_THM; numbit; EXP; DIV_1]);;

let BIT_def = prove
 (`!b n. numbit b n <=> BITS b b n = 1`,
  REWRITE_TAC[numbit; BITS_THM; ODD_MOD; ARITH_RULE `SUC b - b = 1`; EXP_1]);;

let BITS_THM2 = prove
 (`!h l n. BITS h l n = (n MOD 2 EXP SUC h) DIV 2 EXP l`,
  REPEAT GEN_TAC THEN REWRITE_TAC[BITS_THM] THEN
  ASM_CASES_TAC `l <= SUC h` THENL
   [REWRITE_TAC[DIV_MOD; GSYM EXP_ADD] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    ASM_ARITH_TAC;
    ASM_SIMP_TAC[ARITH_RULE `~(l <= SUC h) ==> SUC h - l = 0`] THEN
    REWRITE_TAC[CONJUNCT1 EXP; MOD_1] THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC DIV_LT THEN TRANS_TAC LTE_TRANS `2 EXP SUC h` THEN
    REWRITE_TAC[MOD_LT_EQ; EXP_2_NE_0; WORDSAUX_EXP2_LE] THEN ASM_ARITH_TAC]);;

let BITS_ZEROL = prove
 (`!h a. a < 2 EXP SUC h ==> BITS h 0 a = a`,
  SIMP_TAC[BITS_THM; EXP; DIV_1; SUB_0; MOD_LT]);;

let BIT_ZERO = prove
 (`!b. ~numbit b 0`,
  REWRITE_TAC[numbit; DIV_0; ODD]);;

let NOT_BIT_GT_TWOEXP = prove
 (`!i n. n < 2 EXP i ==> ~numbit i n`,
  SIMP_TAC[numbit; DIV_LT; ODD]);;

let BIT_DIV2 = prove
 (`!n i. numbit n (i DIV 2) <=> numbit (SUC n) i`,
  REWRITE_TAC[numbit; EXP; DIV_DIV]);;

let TWOEXP_MONO2 = prove
 (`!a b. a <= b ==> 2 EXP a <= 2 EXP b`,
  REWRITE_TAC[WORDSAUX_EXP2_LE]);;

let TWOEXP_MONO = prove
 (`!a b. a < b ==> 2 EXP a < 2 EXP b`,
  REWRITE_TAC[WORDSAUX_EXP2_LT]);;

let BITSLT_THM = prove
 (`!h l n. BITS h l n < 2 EXP (SUC h - l)`,
  REWRITE_TAC[BITS_THM; MOD_LT_EQ; EXP_2_NE_0]);;

let BITSLT_THM2 = prove
 (`!h l n. BITS h l n < 2 EXP SUC h`,
  REPEAT GEN_TAC THEN TRANS_TAC LTE_TRANS `2 EXP (SUC h - l)` THEN
  REWRITE_TAC[BITSLT_THM; WORDSAUX_EXP2_LE] THEN ARITH_TAC);;

let DIV_MULT_THM2 = prove
 (`!n. 2 * (n DIV 2) = n - n MOD 2`,
  GEN_TAC THEN MP_TAC(SPECL [`n:num`; `2`] DIVISION) THEN ARITH_TAC);;

let TWOEXP_NOT_ZERO = EXP_2_NE_0;;

let ZERO_LT_TWOEXP = prove
 (`!n. 0 < 2 EXP n`,
  REWRITE_TAC[EXP_LT_0] THEN ARITH_TAC);;

let ODD_MOD2_LEM = ODD_MOD;;

let LESS_MULT_MONO2 = prove
 (`!a b x y. a < x /\ b < y ==> a * b < x * y`,
  MESON_TAC[LT_MULT2]);;

let DIV_GT0 = prove
 (`!a b. b <= a /\ 0 < b ==> 0 < a DIV b`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ARITH_RULE `0 < n <=> 1 <= n`] THEN
  ASM_SIMP_TAC[LE_RDIV_EQ; ARITH_RULE `0 < b ==> ~(b = 0)`] THEN
  ASM_ARITH_TAC);;

let MOD_ZERO_GT = prove
 (`!n a. ~(a = 0) /\ a MOD 2 EXP n = 0 ==> 2 EXP n <= a`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM NOT_LT] THEN DISCH_TAC THEN
  UNDISCH_TAC `a MOD 2 EXP n = 0` THEN ASM_SIMP_TAC[MOD_LT]);;

let ADD_BIT0 = prove
 (`!m n. numbit 0 (m + n) <=> ~(numbit 0 m <=> numbit 0 n)`,
  REWRITE_TAC[BIT0_ODD; ODD_ADD]);;

let BIT_IMP_GE_TWOEXP = prove
 (`!i n. numbit i n ==> 2 EXP i <= n`,
  MESON_TAC[NOT_BIT_GT_TWOEXP; NOT_LT]);;

let NOT_BITS2 = prove
 (`!n a. ~(BITS n n a = 1) <=> BITS n n a = 0`,
  REPEAT GEN_TAC THEN
  MP_TAC(SPECL [`n:num`; `n:num`; `a:num`] BITSLT_THM) THEN
  REWRITE_TAC[ARITH_RULE `SUC n - n = 1`; EXP_1] THEN ARITH_TAC);;

let MOD_ADD_1 = prove
 (`!n. 0 < n ==> !x. ~((x + 1) MOD n = 0) ==> (x + 1) MOD n = x MOD n + 1`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`x:num`; `n:num`] DIVISION) THEN
  ASM_SIMP_TAC[ARITH_RULE `0 < n ==> ~(n = 0)`] THEN
  ABBREV_TAC `q = x DIV n` THEN ABBREV_TAC `r = x MOD n` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[ARITH_RULE `(q * n + r) + 1 = q * n + (r + 1)`] THEN
  ASM_SIMP_TAC[MOD_MULT_ADD] THEN
  ASM_CASES_TAC `r + 1 = n` THENL
   [UNDISCH_TAC `~((x + 1) MOD n = 0)` THEN
    ASM_REWRITE_TAC[ARITH_RULE `(q * n + r) + 1 = q * n + (r + 1)`] THEN
    ASM_SIMP_TAC[MOD_MULT_ADD; MOD_REFL; ARITH_RULE `0 < n ==> ~(n = 0)`];
    MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC]);;

(* bit-level facts about numbit (helpers of this port) *)

let NUMBIT_MOD_2EXP = prove
 (`!i k n. numbit i (n MOD 2 EXP k) <=> i < k /\ numbit i n`,
  REPEAT GEN_TAC THEN
  MP_TAC(AP_TERM `\s:num->bool. i IN s` (SPECL [`n:num`; `k:num`] BITS_OF_NUM_MOD)) THEN
  REWRITE_TAC[IN_BITS_OF_NUM; IN_ELIM_THM; GSYM numbit] THEN MESON_TAC[]);;

let NUMBIT_DIV_2EXP = prove
 (`!i k n. numbit i (n DIV 2 EXP k) <=> numbit (k + i) n`,
  REWRITE_TAC[numbit; DIV_DIV; EXP_ADD]);;

let NUMBIT_EQ = prove
 (`!m n. m = n <=> !i. numbit i m <=> numbit i n`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [GSYM BITS_OF_NUM_EQ] THEN
  REWRITE_TAC[EXTENSION; IN_BITS_OF_NUM; GSYM numbit]);;

let NUMBIT_BITS = prove
 (`!i h l n. numbit i (BITS h l n) <=> i < SUC h - l /\ numbit (l + i) n`,
  REWRITE_TAC[BITS_THM; NUMBIT_MOD_2EXP; NUMBIT_DIV_2EXP]);;

let BIT_OF_BITS_THM = prove
 (`!n h l a. l + n <= h ==> (numbit n (BITS h l a) <=> numbit (l + n) a)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[NUMBIT_BITS] THEN
  ASM_SIMP_TAC[ARITH_RULE `l + n <= h ==> n < SUC h - l`]);;

let BIT_BITS_THM = prove
 (`!h l a b. (!x. l <= x /\ x <= h ==> (numbit x a <=> numbit x b)) <=>
             BITS h l a = BITS h l b`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC RAND_CONV [NUMBIT_EQ] THEN
  REWRITE_TAC[NUMBIT_BITS] THEN EQ_TAC THEN DISCH_TAC THENL
   [X_GEN_TAC `i:num` THEN ASM_CASES_TAC `i < SUC h - l` THEN
    ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    X_GEN_TAC `x:num` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x - l:num`) THEN
    ASM_SIMP_TAC[ARITH_RULE `l <= x ==> l + x - l = x`] THEN
    ASM_SIMP_TAC[ARITH_RULE `l <= x /\ x <= h ==> x - l < SUC h - l`]]);;

let BIT_COMP_THM3 = prove
 (`!h m l n.
     SUC m <= h /\ l <= m ==>
     BITS h (SUC m) n * 2 EXP (SUC m - l) + BITS m l n = BITS h l n`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[BITS_THM] THEN
  SUBGOAL_THEN `SUC m = l + (SUC m - l) /\
                SUC h - l = (SUC m - l) + (SUC h - SUC m)`
  STRIP_ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `d = SUC m - l` THEN ABBREV_TAC `e = SUC h - SUC m` THEN
  ASM_REWRITE_TAC[EXP_ADD; GSYM DIV_DIV] THEN
  REWRITE_TAC[MOD_MULT_MOD] THEN ARITH_TAC);;

let BIT_LOG2 = prove
 (`!n. ~(n = 0) ==> numbit (LOG2 n) n`,
  REPEAT STRIP_TAC THEN MP_TAC(SPEC `n:num` LOG2_PROPERTY) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; REWRITE_TAC[EXP] THEN STRIP_TAC] THEN
  REWRITE_TAC[numbit] THEN
  SUBGOAL_THEN `n DIV 2 EXP LOG2 n = 1` (fun th -> REWRITE_TAC[th; ARITH]) THEN
  MATCH_MP_TAC DIV_UNIQ THEN EXISTS_TAC `n - 2 EXP LOG2 n` THEN ASM_ARITH_TAC);;

let BIT_TIMES2 = prove
 (`!z n. numbit z (2 * n) <=> 0 < z /\ numbit (z - 1) n`,
  REPEAT GEN_TAC THEN STRUCT_CASES_TAC(SPEC `z:num` num_CASES) THEN
  REWRITE_TAC[numbit; EXP; DIV_1; ODD_MULT; ARITH; LT_REFL; SUC_SUB1; LT_0] THEN
  REWRITE_TAC[GSYM DIV_DIV] THEN SIMP_TAC[DIV_MULT; ARITH_EQ]);;

let BIT_TIMES2_1 = prove
 (`!n z. numbit z (2 * n + 1) <=> z = 0 \/ numbit z (2 * n)`,
  REPEAT GEN_TAC THEN STRUCT_CASES_TAC(SPEC `z:num` num_CASES) THEN
  REWRITE_TAC[numbit; EXP; DIV_1; ODD_ADD; ODD_MULT; ARITH; NOT_SUC] THEN
  REWRITE_TAC[GSYM DIV_DIV] THEN SIMP_TAC[DIV_MULT; ARITH_EQ] THEN
  AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN ARITH_TAC);;

let LT_TWOEXP = prove
 (`!x n. x < 2 EXP n <=> x = 0 \/ LOG2 x < n`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `x = 0` THEN
  ASM_REWRITE_TAC[ZERO_LT_TWOEXP] THEN
  MP_TAC(SPEC `x:num` LOG2_PROPERTY) THEN ANTS_TAC THENL
   [ASM_ARITH_TAC; STRIP_TAC] THEN
  EQ_TAC THEN DISCH_TAC THENL
   [MP_TAC(SPECL [`LOG2 x`; `n:num`] WORDSAUX_EXP2_LT) THEN ASM_ARITH_TAC;
    TRANS_TAC LTE_TRANS `2 EXP SUC (LOG2 x)` THEN
    ASM_REWRITE_TAC[WORDSAUX_EXP2_LE] THEN ASM_ARITH_TAC]);;

let NUMBIT_COMPLEMENT = prove
 (`!n c i. c < 2 EXP n
           ==> (numbit i ((2 EXP n - 1) - c) <=> i < n /\ ~numbit i c)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[numbit] THEN
  ASM_CASES_TAC `i < n:num` THEN ASM_REWRITE_TAC[] THENL
   [ALL_TAC;
    SUBGOAL_THEN `((2 EXP n - 1) - c) DIV 2 EXP i = 0`
     (fun th -> REWRITE_TAC[th; ODD]) THEN
    MATCH_MP_TAC DIV_LT THEN TRANS_TAC LTE_TRANS `2 EXP n` THEN
    REWRITE_TAC[WORDSAUX_EXP2_LE] THEN
    MP_TAC(SPEC `n:num` EXP_2_NE_0) THEN ASM_ARITH_TAC] THEN
  SUBGOAL_THEN `2 EXP n = 2 EXP (n - i) * 2 EXP i` SUBST_ALL_TAC THENL
   [REWRITE_TAC[GSYM EXP_ADD] THEN AP_TERM_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`c:num`; `2 EXP i`] DIVISION) THEN REWRITE_TAC[EXP_2_NE_0] THEN
  MP_TAC(SPEC `n - i:num` EXP_2_NE_0) THEN
  SUBGOAL_THEN `~(n - i = 0)` MP_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  UNDISCH_TAC `c < 2 EXP (n - i) * 2 EXP i` THEN
  SPEC_TAC(`n - i:num`,`k:num`) THEN
  SPEC_TAC(`c DIV 2 EXP i`,`q:num`) THEN SPEC_TAC(`c MOD 2 EXP i`,`r:num`) THEN
  SPEC_TAC(`2 EXP i`,`p:num`) THEN REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
  FIRST_X_ASSUM(CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC) THEN
  SUBGOAL_THEN `q < 2 EXP k` MP_TAC THENL
   [MP_TAC(SPECL [`q:num`; `2 EXP k`; `p:num`] LT_MULT_RCANCEL) THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `d:num` o GEN_REWRITE_RULE I [LT_EXISTS]) THEN
  SUBGOAL_THEN `(2 EXP k * p - 1 - (q * p + r)) DIV p = d` SUBST1_TAC THENL
   [MATCH_MP_TAC DIV_UNIQ THEN EXISTS_TAC `(p - 1) - r` THEN
    ASM_REWRITE_TAC[RIGHT_ADD_DISTRIB; MULT_CLAUSES] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `EVEN(q + SUC d)` MP_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN REWRITE_TAC[EVEN_EXP; ARITH] THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[EVEN_ADD; EVEN; GSYM NOT_EVEN] THEN CONV_TAC TAUT]);;

let BIT_EXP_SUB1 = prove
 (`!b n. numbit b (2 EXP n - 1) <=> b < n`,
  REPEAT GEN_TAC THEN
  MP_TAC(SPECL [`n:num`; `0`; `b:num`] NUMBIT_COMPLEMENT) THEN
  REWRITE_TAC[ZERO_LT_TWOEXP; SUB_0; BIT_ZERO]);;

let BIT_COMPLEMENT = prove
 (`!n i a.
     numbit i (2 EXP n - a MOD 2 EXP n) <=>
     (a MOD 2 EXP n = 0 /\ i = n) \/
     (~(a MOD 2 EXP n = 0) /\ i < n /\ ~numbit i (a MOD 2 EXP n - 1))`,
  REPEAT GEN_TAC THEN
  MP_TAC(SPECL [`a:num`; `2 EXP n`] MOD_LT_EQ) THEN
  REWRITE_TAC[EXP_2_NE_0] THEN
  SPEC_TAC(`a MOD 2 EXP n`,`b:num`) THEN GEN_TAC THEN DISCH_TAC THEN
  ASM_CASES_TAC `b = 0` THEN ASM_REWRITE_TAC[SUB_0] THENL
   [MP_TAC(AP_TERM `\s:num->bool. i IN s` (SPEC `n:num` BITS_OF_NUM_POW2)) THEN
    REWRITE_TAC[IN_BITS_OF_NUM; GSYM numbit; IN_SING];
    SUBGOAL_THEN `2 EXP n - b = (2 EXP n - 1) - (b - 1)` SUBST1_TAC THENL
     [ASM_ARITH_TAC; MATCH_MP_TAC NUMBIT_COMPLEMENT THEN ASM_ARITH_TAC]]);;

(* ------------------------------------------------------------------------- *)
(* fcp: port of HOL4 src/n-bit/fcpScript.sml (the words part).  HOL4 FCP     *)
(* i. P i : 'a word is word_of_bits (\i. P i) : N word, and w ' i is bit i w *)
(* ------------------------------------------------------------------------- *)

let dimindex_def = prove
 (`dimindex(:A) = if FINITE(:A) then CARD(:A) else 1`,
  REWRITE_TAC[dimindex]);;

let FCP_BETA = prove
 (`!(g:num->bool) i.
     i < dimindex(:N) ==> (bit i (word_of_bits g:N word) <=> g i)`,
  SIMP_TAC[BIT_WORD_OF_BITS; IN]);;

(* HOL4 fcp CART_EQ for words (HOL Light's CART_EQ is about A^B vectors) *)

let fcp_CART_EQ = prove
 (`!x y:N word. x = y <=> !i. i < dimindex(:N) ==> (bit i x <=> bit i y)`,
  REWRITE_TAC[WORD_EQ_BITS_ALT]);;

(* HOL4 'a + 'b as an index type is (A,B)finite_sum here (word_join); the  *)
(* HOL4 side condition (both types finite) is not needed.                  *)

let index_sum = prove
 (`dimindex(:(A,B)finite_sum) = dimindex(:A) + dimindex(:B)`,
  REWRITE_TAC[DIMINDEX_FINITE_SUM]);;

(* ------------------------------------------------------------------------- *)
(* words: port of HOL4 src/n-bit/wordsScript.sml (only what the closure      *)
(* uses).  The constants that HOL Light lacks.                               *)
(* ------------------------------------------------------------------------- *)

let dimword_DEF = new_definition
  `dimword (s:A->bool) = 2 EXP dimindex(:A)`;;

let dimword_def = prove
 (`dimword(:A) = 2 EXP dimindex(:A)`,
  REWRITE_TAC[dimword_DEF]);;

let INT_MIN_DEF = new_definition
  `INT_MIN (s:A->bool) = 2 EXP (dimindex(:A) - 1)`;;

let INT_MIN_def = prove
 (`INT_MIN(:A) = 2 EXP (dimindex(:A) - 1)`,
  REWRITE_TAC[INT_MIN_DEF]);;

let UINT_MAX_DEF = new_definition
  `UINT_MAX (s:A->bool) = dimword(:A) - 1`;;

let UINT_MAX_def = prove
 (`UINT_MAX(:A) = dimword(:A) - 1`,
  REWRITE_TAC[UINT_MAX_DEF]);;

let INT_MAX_DEF = new_definition
  `INT_MAX (s:A->bool) = INT_MIN(:A) - 1`;;

let INT_MAX_def = prove
 (`INT_MAX(:A) = INT_MIN(:A) - 1`,
  REWRITE_TAC[INT_MAX_DEF]);;

let word_lsb_def = new_definition
  `word_lsb (w:N word) <=> bit 0 w`;;

let word_msb_def = new_definition
  `word_msb (w:N word) <=> bit (dimindex(:N) - 1) w`;;

let word_slice_DEF = new_definition
  `word_slice h l (w:N word) =
     word_of_bits (\i. l <= i /\ i <= MIN h (dimindex(:N) - 1) /\ bit i w)
       :N word`;;

let word_slice_def = prove
 (`!h l. word_slice h l =
     \w:N word.
       word_of_bits (\i. l <= i /\ i <= MIN h (dimindex(:N) - 1) /\ bit i w)
         :N word`,
  REWRITE_TAC[FUN_EQ_THM; word_slice_DEF]);;

let word_bits_DEF = new_definition
  `word_bits h l (w:N word) =
     word_of_bits (\i. i + l <= MIN h (dimindex(:N) - 1) /\ bit (i + l) w)
       :N word`;;

let word_bits_def = prove
 (`!h l. word_bits h l =
     \w:N word.
       word_of_bits (\i. i + l <= MIN h (dimindex(:N) - 1) /\ bit (i + l) w)
         :N word`,
  REWRITE_TAC[FUN_EQ_THM; word_bits_DEF]);;

let word_extract_DEF = new_definition
  `word_extract h l (w:M word) = word_zx (word_bits h l w):N word`;;

let word_extract_def = prove
 (`!h l. word_extract h l = (word_zx:M word->N word) o word_bits h l`,
  REWRITE_TAC[FUN_EQ_THM; o_THM; word_extract_DEF]);;

(* ------------------------------------------------------------------------- *)
(* words: sizes and the n2w / w2n forms.                                     *)
(* ------------------------------------------------------------------------- *)

let ZERO_LT_dimword = prove
 (`0 < dimword(:N)`,
  REWRITE_TAC[dimword_def; ZERO_LT_TWOEXP]);;

let DIMINDEX_GT_0 = prove
 (`0 < dimindex(:A)`,
  REWRITE_TAC[DIMINDEX_GE_1; ARITH_RULE `0 < n <=> 1 <= n`]);;

let dimindex_lt_dimword = prove
 (`dimindex(:N) < dimword(:N)`,
  REWRITE_TAC[dimword_def; LT_POW2_REFL]);;

let ONE_LT_dimword = prove
 (`1 < dimword(:N)`,
  REWRITE_TAC[dimword_def] THEN
  SUBST1_TAC(ARITH_RULE `1 = 2 EXP 0`) THEN
  REWRITE_TAC[WORDSAUX_EXP2_LT; DIMINDEX_GT_0]);;

let dimword_8 = prove
 (`dimword(:8) = 256`,
  REWRITE_TAC[dimword_def; DIMINDEX_8] THEN CONV_TAC NUM_REDUCE_CONV);;

let dimword_64 = prove
 (`dimword(:64) = 18446744073709551616`,
  REWRITE_TAC[dimword_def; DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV);;

let dimword_IS_TWICE_INT_MIN = prove
 (`dimword(:N) = 2 * INT_MIN(:N)`,
  REWRITE_TAC[dimword_def; INT_MIN_def; GSYM(CONJUNCT2 EXP)] THEN
  AP_TERM_TAC THEN MP_TAC(ISPEC `(:N)` DIMINDEX_GE_1) THEN ARITH_TAC);;

let LT_DIMINDEX_LE_HB = prove
 (`!b. b < dimindex(:N) <=> b <= dimindex(:N) - 1`,
  MP_TAC(ISPEC `(:N)` DIMINDEX_GE_1) THEN ARITH_TAC);;

let HB_LT_DIMINDEX = prove
 (`dimindex(:N) - 1 < dimindex(:N)`,
  MP_TAC(ISPEC `(:N)` DIMINDEX_GE_1) THEN ARITH_TAC);;

let w2n_lt = prove
 (`!w:N word. val w < dimword(:N)`,
  REWRITE_TAC[dimword_def; VAL_BOUND]);;

let w2n_11 = VAL_EQ;;

let n2w_w2n = WORD_VAL;;

let w2n_n2w = prove
 (`!n. val(word n:N word) = n MOD dimword(:N)`,
  REWRITE_TAC[VAL_WORD; dimword_def]);;

let n2w_11 = prove
 (`!m n. (word m:N word = word n) <=> m MOD dimword(:N) = n MOD dimword(:N)`,
  REWRITE_TAC[GSYM VAL_EQ; w2n_n2w]);;

let n2w_mod = prove
 (`!n. word(n MOD dimword(:N)):N word = word n`,
  REWRITE_TAC[dimword_def; WORD_MOD_SIZE]);;

let mod_dimindex = prove
 (`!n. n MOD dimindex(:N) < dimword(:N)`,
  GEN_TAC THEN TRANS_TAC LT_TRANS `dimindex(:N)` THEN
  REWRITE_TAC[dimindex_lt_dimword; MOD_LT_EQ; DIMINDEX_NONZERO]);;

let ranged_word_nchotomy = prove
 (`!w:N word. ?n. w = word n /\ n < dimword(:N)`,
  GEN_TAC THEN EXISTS_TAC `val(w:N word)` THEN
  REWRITE_TAC[WORD_VAL; w2n_lt]);;

let WORD_FINITE = prove
 (`!s:N word->bool. FINITE s`,
  GEN_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `IMAGE (word:num->N word) {n | n < 2 EXP dimindex(:N)}` THEN
  SIMP_TAC[FINITE_IMAGE; FINITE_NUMSEG_LT] THEN
  REWRITE_TAC[SUBSET; IN_IMAGE; IN_ELIM_THM] THEN
  MESON_TAC[WORD_VAL; VAL_BOUND]);;

let n2w_def = prove
 (`!n. word n:N word = word_of_bits (\i. numbit i n)`,
  REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD; BIT_WORD_OF_BITS; IN; numbit] THEN
  MESON_TAC[]);;

let word_index = prove
 (`!n i. i < dimindex(:N) ==> (bit i (word n:N word) <=> numbit i n)`,
  SIMP_TAC[BIT_WORD; numbit]);;

(* HOL4 leaves bits beyond the width unspecified (FAIL); here they are F. *)

let word_index_n2w = prove
 (`!n i. bit i (word n:N word) <=> if i < dimindex(:N) then numbit i n else F`,
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[BIT_WORD; numbit]);;

let word_bit_n2w = prove
 (`!b n. bit b (word n:N word) <=> b <= dimindex(:N) - 1 /\ numbit b n`,
  REWRITE_TAC[BIT_WORD; numbit; GSYM LT_DIMINDEX_LE_HB]);;

let word_0 = prove
 (`!i. i < dimindex(:N) ==> ~bit i (word 0:N word)`,
  REWRITE_TAC[BIT_WORD_0]);;

let word_bit_def = prove
 (`!b w:N word. bit b w <=> b <= dimindex(:N) - 1 /\ bit b w`,
  REWRITE_TAC[GSYM LT_DIMINDEX_LE_HB] THEN MESON_TAC[BIT_GUARD]);;

let word_bit = prove
 (`!w:N word b. b < dimindex(:N) ==> (bit b w <=> bit b w)`,
  REWRITE_TAC[]);;

let word_bit_thm = prove
 (`!n w:N word. bit n w <=> n < dimindex(:N) /\ bit n w`,
  MESON_TAC[BIT_GUARD]);;

let w2w = prove
 (`!w:M word i.
     i < dimindex(:N) ==> (bit i (word_zx w:N word) <=> i < dimindex(:M) /\ bit i w)`,
  SIMP_TAC[BIT_WORD_ZX] THEN MESON_TAC[BIT_GUARD]);;

let w2w_def = word_zx;;

let word_msb_n2w = prove
 (`!n. word_msb (word n:N word) <=> numbit (dimindex(:N) - 1) n`,
  REWRITE_TAC[word_msb_def; BIT_WORD; numbit; HB_LT_DIMINDEX]);;

let word_msb_n2w_numeric = prove
 (`!n. word_msb (word n:N word) <=> INT_MIN(:N) <= n MOD dimword(:N)`,
  REWRITE_TAC[word_msb_def; MSB_VAL; VAL_WORD; INT_MIN_def; dimword_def]);;

let word_msb_neg = prove
 (`!w:N word. word_msb w <=> word_ilt w (word 0)`,
  REWRITE_TAC[word_msb_def; MSB_IVAL; WORD_ILT; IVAL_WORD_0]);;

(* ------------------------------------------------------------------------- *)
(* The definitions of the operations, in HOL4 form.                          *)
(* ------------------------------------------------------------------------- *)

let word_add_def = prove
 (`!v w:N word. word_add v w = word(val v + val w)`,
  REWRITE_TAC[WORD_ADD; WORD_VAL]);;

let word_mul_def = prove
 (`!v w:N word. word_mul v w = word(val v * val w)`,
  REWRITE_TAC[WORD_MUL; WORD_VAL]);;

let word_2comp_def = prove
 (`!w:N word. word_neg w = word(dimword(:N) - val w)`,
  GEN_TAC THEN REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_NEG_CASES; VAL_WORD; dimword_def] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[SUB_0; MOD_REFL] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOD_LT THEN
  MP_TAC(SPEC `dimindex(:N)` EXP_2_NE_0) THEN ASM_ARITH_TAC);;

let word_sub_def = prove
 (`!v w:N word. word_sub v w = word_add v (word_neg w)`,
  WORD_ARITH_TAC);;

let word_div_def = prove
 (`!v w:N word. word_udiv v w = word(val v DIV val w)`,
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_UDIV; VAL_WORD] THEN
  REPEAT GEN_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOD_LT THEN
  MATCH_MP_TAC LET_TRANS THEN EXISTS_TAC `val(v:N word)` THEN
  REWRITE_TAC[DIV_LE; VAL_BOUND]);;

let word_1comp_def = prove
 (`!w:N word. word_not w = word_of_bits (\i. ~bit i w):N word`,
  REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_NOT; BIT_WORD_OF_BITS; IN] THEN
  MESON_TAC[]);;

let word_and_def = prove
 (`!v w:N word. word_and v w = word_of_bits (\i. bit i v /\ bit i w):N word`,
  REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_AND; BIT_WORD_OF_BITS; IN] THEN
  MESON_TAC[]);;

let word_or_def = prove
 (`!v w:N word. word_or v w = word_of_bits (\i. bit i v \/ bit i w):N word`,
  REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_OR; BIT_WORD_OF_BITS; IN] THEN
  MESON_TAC[]);;

let word_xor_def = prove
 (`!v w:N word. word_xor v w = word_of_bits (\i. ~(bit i v <=> bit i w)):N word`,
  REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_XOR; BIT_WORD_OF_BITS; IN] THEN
  MESON_TAC[]);;

let word_lsl_def = prove
 (`!w:N word n.
     word_shl w n =
     word_of_bits (\i. i < dimindex(:N) /\ n <= i /\ bit (i - n) w):N word`,
  REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_SHL; BIT_WORD_OF_BITS; IN] THEN
  MESON_TAC[]);;

let word_lsr_def = prove
 (`!w:N word n.
     word_ushr w n =
     word_of_bits (\i. i + n < dimindex(:N) /\ bit (i + n) w):N word`,
  REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_USHR; BIT_WORD_OF_BITS; IN] THEN
  REPEAT STRIP_TAC THEN ASM_MESON_TAC[BIT_GUARD]);;

let word_asr_def = prove
 (`!w:N word n.
     word_ishr w n =
     word_of_bits (\i. if dimindex(:N) <= i + n then word_msb w
                       else bit (i + n) w):N word`,
  REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_ISHR; BIT_WORD_OF_BITS; IN;
              word_msb_def] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[GSYM NOT_LT] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[]);;

let word_ror_def = prove
 (`!w:N word n.
     word_ror w n =
     word_of_bits (\i. bit ((i + n) MOD dimindex(:N)) w):N word`,
  REWRITE_TAC[word_ror; WORD_EQ_BITS_ALT; BIT_WORD_OF_BITS; IN_ELIM_THM; IN]);;

(* ------------------------------------------------------------------------- *)
(* words: orderings.                                                          *)
(* ------------------------------------------------------------------------- *)

let WORD_LO = WORD_ULT;;

let WORD_LS = WORD_ULE;;

let WORD_LTi = WORD_ILT;;

let WORD_NOT_LOWER = prove
 (`!a b:N word. ~(word_ult a b) <=> word_ule b a`,
  REWRITE_TAC[WORD_ULT; WORD_ULE; NOT_LT]);;

let WORD_NOT_LOWER_EQUAL = prove
 (`!a b:N word. ~(word_ule a b) <=> word_ult b a`,
  REWRITE_TAC[WORD_ULT; WORD_ULE; NOT_LE]);;

let WORD_LOWER_REFL = prove
 (`!a:N word. ~(word_ult a a)`,
  REWRITE_TAC[WORD_ULT; LT_REFL]);;

let WORD_LOWER_NOT_EQ = prove
 (`!a b:N word. word_ult a b ==> ~(a = b)`,
  MESON_TAC[WORD_LOWER_REFL]);;

let WORD_LOWER_EQ_TRANS = prove
 (`!a b c:N word. word_ule a b /\ word_ule b c ==> word_ule a c`,
  REWRITE_TAC[WORD_ULE; LE_TRANS]);;

let WORD_LO_word_0 = prove
 (`(!n:N word. word_ult (word 0) n <=> ~(n = word 0)) /\
   (!n:N word. ~(word_ult n (word 0)))`,
  REWRITE_TAC[WORD_ULT; VAL_WORD_0; GSYM VAL_EQ_0] THEN ARITH_TAC);;

let WORD_LO_word_T = prove
 (`(!n:N word. ~(word_ult (word_neg (word 1)) n)) /\
   (!n:N word. word_ult n (word_neg (word 1)) <=> ~(n = word_neg (word 1)))`,
  REWRITE_TAC[WORD_ULT; GSYM VAL_EQ; VAL_WORD_NEG_1] THEN
  CONJ_TAC THEN GEN_TAC THEN MP_TAC(ISPEC `n:N word` VAL_BOUND) THEN
  ARITH_TAC);;

let word_lo_n2w = prove
 (`!a b. word_ult (word a:N word) (word b) <=>
         a MOD dimword(:N) < b MOD dimword(:N)`,
  REWRITE_TAC[WORD_ULT; w2n_n2w]);;

let word_ls_n2w = prove
 (`!a b. word_ule (word a:N word) (word b) <=>
         a MOD dimword(:N) <= b MOD dimword(:N)`,
  REWRITE_TAC[WORD_ULE; w2n_n2w]);;

let WORD_LT = prove
 (`!a b:N word.
     word_ilt a b <=>
     (word_msb a <=> word_msb b) /\ val a < val b \/ word_msb a /\ ~word_msb b`,
  REPEAT GEN_TAC THEN REWRITE_TAC[WORD_ILT; word_msb_def; IVAL_VAL] THEN
  MP_TAC(ISPEC `a:N word` INT_VAL_BOUND) THEN
  MP_TAC(ISPEC `b:N word` INT_VAL_BOUND) THEN
  MAP_EVERY ASM_CASES_TAC
   [`bit (dimindex(:N) - 1) (a:N word)`; `bit (dimindex(:N) - 1) (b:N word)`] THEN
  ASM_REWRITE_TAC[BITVAL_CLAUSES; GSYM INT_OF_NUM_LT] THEN INT_ARITH_TAC);;

let WORD_LE = prove
 (`!a b:N word.
     word_ile a b <=>
     (word_msb a <=> word_msb b) /\ val a <= val b \/ word_msb a /\ ~word_msb b`,
  REPEAT GEN_TAC THEN REWRITE_TAC[WORD_ILE; word_msb_def; IVAL_VAL] THEN
  MP_TAC(ISPEC `a:N word` INT_VAL_BOUND) THEN
  MP_TAC(ISPEC `b:N word` INT_VAL_BOUND) THEN
  MAP_EVERY ASM_CASES_TAC
   [`bit (dimindex(:N) - 1) (a:N word)`; `bit (dimindex(:N) - 1) (b:N word)`] THEN
  ASM_REWRITE_TAC[BITVAL_CLAUSES; GSYM INT_OF_NUM_LE] THEN INT_ARITH_TAC);;

let WORD_NOT_LESS = prove
 (`!a b:N word. ~(word_ilt a b) <=> word_ile b a`,
  REWRITE_TAC[WORD_ILT; WORD_ILE; INT_NOT_LT]);;

let WORD_LESS_REFL = prove
 (`!a:N word. ~(word_ilt a a)`,
  REWRITE_TAC[WORD_ILT; INT_LT_REFL]);;

let WORD_LESS_OR_EQ = prove
 (`!a b:N word. word_ile a b <=> word_ilt a b \/ a = b`,
  REWRITE_TAC[WORD_ILT; WORD_ILE; GSYM IVAL_EQ] THEN INT_ARITH_TAC);;

let WORD_LESS_EQ_TRANS = prove
 (`!a b c:N word. word_ile a b /\ word_ile b c ==> word_ile a c`,
  REWRITE_TAC[WORD_ILE] THEN INT_ARITH_TAC);;

let word_lt_n2w = prove
 (`!a b. word_ilt (word a:N word) (word b) <=>
         let sa = numbit (dimindex(:N) - 1) a
         and sb = numbit (dimindex(:N) - 1) b in
         (sa <=> sb) /\ a MOD dimword(:N) < b MOD dimword(:N) \/ sa /\ ~sb`,
  REWRITE_TAC[WORD_LT; GSYM word_msb_n2w; w2n_n2w] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* words: the ring and the bitwise operations.                               *)
(* ------------------------------------------------------------------------- *)

let WORD_ADD_COMM = WORD_ADD_SYM;;

let WORD_MULT_COMM = WORD_MUL_SYM;;

let WORD_MULT_ASSOC = WORD_MUL_ASSOC;;

let WORD_AND_COMM = WORD_AND_SYM;;

let WORD_OR_COMM = WORD_OR_SYM;;

let WORD_OR_IDEM = WORD_OR_REFL;;

let WORD_EQ_SUB_ZERO = WORD_SUB_EQ_0;;

let WORD_NEG = WORD_NEG_AS_ADD;;

(* HOL Light's WORD_AND_ASSOC and WORD_OR_ASSOC are the other orientation *)

let words_WORD_AND_ASSOC = prove
 (`!a b c:N word. word_and (word_and a b) c = word_and a (word_and b c)`,
  REWRITE_TAC[WORD_AND_ASSOC]);;

let words_WORD_OR_ASSOC = prove
 (`!a b c:N word. word_or (word_or a b) c = word_or a (word_or b c)`,
  REWRITE_TAC[WORD_OR_ASSOC]);;

let WORD_LEFT_AND_OVER_OR = prove
 (`!a b c:N word.
     word_and a (word_or b c) = word_or (word_and a b) (word_and a c)`,
  WORD_BITWISE_TAC);;

let WORD_LEFT_ADD_DISTRIB = WORD_RULE
 `!v w x:N word.
     word_mul v (word_add w x) = word_add (word_mul v w) (word_mul v x)`;;

let WORD_LEFT_SUB_DISTRIB = WORD_RULE
 `!v w x:N word.
     word_mul v (word_sub w x) = word_sub (word_mul v w) (word_mul v x)`;;

let WORD_MULT_CLAUSES = WORD_RULE
 `!v w:N word.
     word_mul (word 0) v = word 0 /\ word_mul v (word 0) = word 0 /\
     word_mul (word 1) v = v /\ word_mul v (word 1) = v /\
     word_mul (word_add v (word 1)) w = word_add (word_mul v w) w /\
     word_mul v (word_add w (word 1)) = word_add v (word_mul v w)`;;

let WORD_NEG_MUL = WORD_RULE
 `!w:N word. word_neg w = word_mul (word_neg (word 1)) w`;;

let WORD_ADD_SUB = WORD_RULE
 `!v w:N word. word_sub (word_add v w) w = v`;;

let WORD_SUB_PLUS = WORD_RULE
 `!v w x:N word. word_sub v (word_add w x) = word_sub (word_sub v w) x`;;

let WORD_SUB_INTRO = WORD_RULE
 `(!x y:N word. word_add (word_neg y) x = word_sub x y) /\
  (!x y:N word. word_add x (word_neg y) = word_sub x y) /\
  (!x y z:N word. word_add (word_mul (word_neg x) y) z = word_sub z (word_mul x y)) /\
  (!x y z:N word. word_add z (word_mul (word_neg x) y) = word_sub z (word_mul x y)) /\
  (!x:N word. word_mul (word_neg (word 1)) x = word_neg x) /\
  (!x y z:N word. word_sub z (word_mul (word_neg x) y) = word_add z (word_mul x y)) /\
  (!x y z:N word.
     word_sub (word_mul (word_neg x) y) z = word_neg (word_add (word_mul x y) z))`;;

let WORD_ADD_LINV = WORD_RULE
 `!w:N word. word_add (word_neg w) w = word 0`;;

let WORD_ADD_RINV = WORD_RULE
 `!w:N word. word_add w (word_neg w) = word 0`;;

let WORD_ADD_SUB_ASSOC = WORD_RULE
 `!v w x:N word. word_sub (word_add v w) x = word_add v (word_sub w x)`;;

let WORD_ADD_SUB_SYM = WORD_RULE
 `!v w x:N word. word_sub (word_add v w) x = word_add (word_sub v x) w`;;

let WORD_NEG_ADD = WORD_RULE
 `!v w:N word. word_neg (word_add v w) = word_add (word_neg v) (word_neg w)`;;

let WORD_SUB_SUB = WORD_RULE
 `!v w x:N word. word_sub v (word_sub w x) = word_sub (word_add v x) w`;;

let WORD_EQ_ADD_LCANCEL = prove
 (`!v w x:N word. word_add v w = word_add v x <=> w = x`,
  MESON_TAC[WORD_RULE `!v w:N word. word_sub (word_add v w) v = w`]);;

let WORD_ADD_INV_0_EQ = prove
 (`!v w:N word. word_add v w = v <=> w = word 0`,
  MESON_TAC[WORD_RULE `!v w:N word. word_sub (word_add v w) v = w`;
            WORD_SUB_REFL; WORD_ADD_0]);;

let WORD_EQ_NEG = prove
 (`!v w:N word. word_neg v = word_neg w <=> v = w`,
  MESON_TAC[WORD_NEG_NEG]);;

let WORD_ADD_EQ_SUB = prove
 (`!v w x:N word. word_add v w = x <=> v = word_sub x w`,
  MESON_TAC[WORD_RULE `!v w:N word. word_sub (word_add v w) w = v`;
            WORD_RULE `!v w:N word. word_add (word_sub v w) w = v`]);;

let WORD_EQ_SUB_RADD = prove
 (`!v w x:N word. word_sub v w = x <=> v = word_add x w`,
  MESON_TAC[WORD_RULE `!v w:N word. word_sub (word_add v w) w = v`;
            WORD_RULE `!v w:N word. word_add (word_sub v w) w = v`]);;

let WORD_LITERAL_ADD = prove
 (`(!m n. word_add (word_neg (word m)) (word_neg (word n)):N word =
          word_neg (word (m + n))) /\
   (!m n. word_add (word m) (word_neg (word n)):N word =
          if n <= m then word (m - n) else word_neg (word (n - m)))`,
  CONJ_TAC THEN REPEAT GEN_TAC THENL
   [REWRITE_TAC[WORD_ADD] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  COND_CASES_TAC THEN ASM_SIMP_TAC[WORD_SUB; GSYM NOT_LE;
    ARITH_RULE `~(n <= m) ==> m <= n`] THEN
  CONV_TAC WORD_RULE);;

let n2w_SUC = prove
 (`!n. word (SUC n):N word = word_add (word n) (word 1)`,
  REWRITE_TAC[ADD1; WORD_ADD]);;

let n2w_sub = prove
 (`!a b. b <= a ==> word (a - b):N word = word_sub (word a) (word b)`,
  SIMP_TAC[WORD_SUB]);;

let word_2comp_n2w = prove
 (`!n. word_neg (word n):N word = word (dimword(:N) - n MOD dimword(:N))`,
  REWRITE_TAC[word_2comp_def; w2n_n2w]);;

let w2n_minus1 = prove
 (`val (word_neg (word 1):N word) = dimword(:N) - 1`,
  REWRITE_TAC[VAL_WORD_NEG_1; dimword_def]);;

let MOD_COMPLEMENT = prove
 (`!n q a. 0 < n /\ 0 < q /\ a < q * n ==>
           (q * n - a) MOD n = (n - a MOD n) MOD n`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`a:num`; `n:num`] DIVISION) THEN
  ASM_SIMP_TAC[ARITH_RULE `0 < n ==> ~(n = 0)`] THEN
  ABBREV_TAC `k = a DIV n` THEN ABBREV_TAC `r = a MOD n` THEN STRIP_TAC THEN
  SUBGOAL_THEN `k < q` ASSUME_TAC THENL
   [MP_TAC(SPECL [`k:num`; `q:num`; `n:num`] LT_MULT_RCANCEL) THEN
    ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `q * n - a = (q - k - 1) * n + (n - r)` SUBST1_TAC THENL
   [ASM_REWRITE_TAC[RIGHT_SUB_DISTRIB; MULT_CLAUSES] THEN
    SUBGOAL_THEN `(k + 1) * n <= q * n` MP_TAC THENL
     [REWRITE_TAC[LE_MULT_RCANCEL] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[RIGHT_ADD_DISTRIB; MULT_CLAUSES] THEN ASM_ARITH_TAC;
    REWRITE_TAC[MOD_MULT_ADD]]);;

(* ------------------------------------------------------------------------- *)
(* words: values of sums and differences, single bits.                       *)
(* ------------------------------------------------------------------------- *)

let w2n_add = prove
 (`!a b:N word.
     ~word_msb a /\ ~word_msb b ==> val (word_add a b) = val a + val b`,
  REWRITE_TAC[word_msb_def; MSB_VAL; NOT_LE] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[VAL_WORD_ADD_CASES] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(CONJUNCT1 TWICE_MSB) THEN ASM_ARITH_TAC);;

let w2n_add_2 = prove
 (`!a b:N word.
     val a + val b < dimword(:N) ==> val (word_add a b) = val a + val b`,
  SIMP_TAC[VAL_WORD_ADD_CASES; dimword_def]);;

let word_sub_w2n = prove
 (`!x y:N word. word_ule y x ==> val (word_sub x y) = val x - val y`,
  SIMP_TAC[WORD_ULE; VAL_WORD_SUB_CASES]);;

let TWO_COMP_POS = prove
 (`!a:N word.
     ~word_msb a ==>
     (if a = word 0 then ~word_msb (word_neg a) else word_msb (word_neg a))`,
  GEN_TAC THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[WORD_NEG_0; word_msb_def; BIT_WORD_0] THEN
  REWRITE_TAC[MSB_VAL; VAL_WORD_NEG_CASES] THEN
  ASM_REWRITE_TAC[VAL_EQ_0] THEN
  MP_TAC(CONJUNCT1 TWICE_MSB) THEN ARITH_TAC);;

let WORD_ADD_BIT0 = prove
 (`!a b:N word. bit 0 (word_add a b) <=> ~(bit 0 a <=> bit 0 b)`,
  REWRITE_TAC[BIT_WORD_ADD_CLAUSES]);;

let word_bit_test = prove
 (`!n w:N word. bit n w <=> ~(word_and w (word (2 EXP n)) = word 0)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_AND; BIT_WORD_POW2; BIT_WORD_0] THEN
  MESON_TAC[BIT_GUARD]);;

let word_bit_or = prove
 (`!n w1 w2:N word. bit n (word_or w1 w2) <=> bit n w1 \/ bit n w2`,
  REWRITE_TAC[BIT_WORD_OR_ALT]);;

let word_bit_and = prove
 (`!n w1 w2:N word. bit n (word_and w1 w2) <=> bit n w1 /\ bit n w2`,
  REWRITE_TAC[BIT_WORD_AND_ALT]);;

let WORD_NEG_1_T = prove
 (`!i. i < dimindex(:N) ==> bit i (word_neg (word 1):N word)`,
  REWRITE_TAC[WORD_NEG_1; BIT_WORD_NOT; BIT_WORD_0]);;

(* ------------------------------------------------------------------------- *)
(* address: word arithmetic lemmas (examples/machine-code/hoare-triple).     *)
(* ------------------------------------------------------------------------- *)

let CONTAINER_def = new_definition
  `CONTAINER (x:bool) = x`;;

let word_arith_lemma1 = prove
 (`!n m x:N word.
     word_add (word n) (word m):N word = word (n + m) /\
     word_add (word_add x (word n)) (word m) = word_add x (word (n + m)) /\
     word_sub (word_sub x (word n)) (word m) = word_sub x (word (n + m))`,
  REWRITE_TAC[WORD_ADD] THEN CONV_TAC WORD_RULE);;

let word_arith_lemma2 = prove
 (`!n m. word_sub (word n) (word m):N word =
         if n < m then word_neg (word (m - n)) else word (n - m)`,
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[NOT_LT]) THEN
  ASM_SIMP_TAC[WORD_SUB; LT_IMP_LE] THEN CONV_TAC WORD_RULE);;

let word_arith_lemma4 = prove
 (`!x n m. word_sub (word_add x (word n)) (word m):N word =
           if n < m then word_sub x (word (m - n)) else word_add x (word (n - m))`,
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[NOT_LT]) THEN
  ASM_SIMP_TAC[WORD_SUB; LT_IMP_LE] THEN CONV_TAC WORD_RULE);;

let WORD_EQ_ADD_RCANCEL = prove
 (`!v w x:N word. word_add v w = word_add x w <=> v = x`,
  MESON_TAC[WORD_RULE `!v w:N word. word_sub (word_add v w) w = v`]);;

(* a = b <=> c = d for words, when a - b is c - d or its negation *)

let WORD_EQ_CANCEL_TAC =
  ONCE_REWRITE_TAC[GSYM WORD_SUB_EQ_0] THEN
  FIRST
   [MATCH_MP_TAC(MESON[] `!x y:N word. x = y ==> (x = word 0 <=> y = word 0)`) THEN
    CONV_TAC WORD_RULE;
    MATCH_MP_TAC(MESON[WORD_NEG_EQ_0]
      `!x y:N word. x = word_neg y ==> (x = word 0 <=> y = word 0)`) THEN
    CONV_TAC WORD_RULE];;

let WORD_EQ_ADD_CANCEL = prove
 (`!v w x:N word.
     (word_add v w = word_add x w <=> v = x) /\
     (word_add w v = word_add x w <=> v = x) /\
     (word_add v w = word_add w x <=> v = x) /\
     (word_add w v = word_add w x <=> v = x) /\
     (w = word_add x w <=> x = word 0) /\
     (word_add v w = w <=> v = word 0) /\
     (w = word_add w x <=> x = word 0) /\
     (word_add w v = w <=> v = word 0)`,
  REPEAT GEN_TAC THEN REPEAT CONJ_TAC THEN WORD_EQ_CANCEL_TAC);;

let n2w_and_1 = prove
 (`!n. word_and (word n) (word 1):N word = word (n MOD 2)`,
  GEN_TAC THEN REWRITE_TAC[WORD_AND_1; BIT_WORD; EXP; DIV_1] THEN
  REWRITE_TAC[DIMINDEX_GT_0] THEN
  MP_TAC(SPEC `n:num` ODD_MOD) THEN
  MP_TAC(SPECL [`n:num`; `2`] MOD_LT_EQ) THEN REWRITE_TAC[ARITH_EQ] THEN
  SPEC_TAC(`n MOD 2`,`r:num`) THEN GEN_TAC THEN
  ASM_CASES_TAC `ODD n` THEN ASM_REWRITE_TAC[] THEN
  REPEAT DISCH_TAC THEN AP_TERM_TAC THEN ASM_ARITH_TAC);;

let word_LSL_n2w = prove
 (`!m k. word_shl (word m:N word) k = word (m * 2 EXP k)`,
  REWRITE_TAC[WORD_SHL_WORD; MULT_SYM]);;

(* ------------------------------------------------------------------------- *)
(* words: shifts.                                                             *)
(* ------------------------------------------------------------------------- *)

let WORD_MUL_LSL = prove
 (`!a:N word n. word_shl a n = word_mul (word (2 EXP n)) a`,
  REPEAT GEN_TAC THEN REWRITE_TAC[word_shl] THEN
  GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [GSYM WORD_VAL] THEN
  REWRITE_TAC[GSYM WORD_MUL; MULT_SYM]);;

let w2n_lsr = VAL_WORD_USHR;;

let LSR_ADD = WORD_USHR_COMPOSE;;

let LSL_ONE = WORD_RULE
 `!w:N word. word_shl w 1 = word_add w w`;;

let word_1_lsl = prove
 (`!n. word_shl (word 1:N word) n = word (2 EXP n)`,
  REWRITE_TAC[WORD_SHL_WORD; MULT_CLAUSES]);;

let word_lsl_n2w = prove
 (`!n m. word_shl (word m:N word) n =
         if dimindex(:N) - 1 < n then word 0 else word (m * 2 EXP n)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[word_LSL_n2w] THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[GSYM WORD_MOD_SIZE] THEN
  AP_TERM_TAC THEN REWRITE_TAC[MOD_0; MOD_EQ_0] THEN
  EXISTS_TAC `m * 2 EXP (n - dimindex(:N))` THEN
  REWRITE_TAC[GSYM MULT_ASSOC; GSYM EXP_ADD] THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN ASM_ARITH_TAC);;

let WORD_ADD_LSL = prove
 (`!n a b:N word.
     word_shl (word_add a b) n = word_add (word_shl a n) (word_shl b n)`,
  REWRITE_TAC[WORD_MUL_LSL] THEN CONV_TAC WORD_RULE);;

let WORD_2COMP_LSL = prove
 (`!n a:N word. word_shl (word_neg a) n = word_neg (word_shl a n)`,
  REWRITE_TAC[WORD_MUL_LSL] THEN CONV_TAC WORD_RULE);;

let LSL_BITWISE = prove
 (`(!n v w:N word.
      word_and (word_shl w n) (word_shl v n) = word_shl (word_and w v) n) /\
   (!n v w:N word.
      word_or (word_shl w n) (word_shl v n) = word_shl (word_or w v) n) /\
   (!n v w:N word.
      word_xor (word_shl w n) (word_shl v n) = word_shl (word_xor w v) n)`,
  REWRITE_TAC[WORD_SHL_AND; WORD_SHL_OR; WORD_SHL_XOR]);;

let ASR_UINT_MAX = prove
 (`!n. word_ishr (word_UINT_MAX:N word) n = word_UINT_MAX`,
  GEN_TAC THEN REWRITE_TAC[GSYM IVAL_EQ; IVAL_WORD_ISHR] THEN
  SUBGOAL_THEN `ival(word_UINT_MAX:N word) = -- &1` SUBST1_TAC THENL
   [REWRITE_TAC[GSYM IVAL_WORD_NEG_1; IVAL_EQ] THEN
    REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_UINT_MAX; VAL_WORD_NEG_1];
    MATCH_MP_TAC INT_DIV_UNIQ THEN EXISTS_TAC `(&2:int) pow n - &1` THEN
    REWRITE_TAC[INT_ABS_POW; INT_ABS_NUM] THEN
    MP_TAC(SPECL [`n:num`; `&2:int`] INT_POW_LE_1) THEN INT_ARITH_TAC]);;

let lsl_lsr = prove
 (`!w:N word n.
     val w * 2 EXP n < dimword(:N) ==> word_ushr (word_shl w n) n = w`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_USHR; VAL_WORD_SHL] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[dimword_def]) THEN
  ONCE_REWRITE_TAC[MULT_SYM] THEN ASM_SIMP_TAC[MOD_LT] THEN
  SIMP_TAC[ONCE_REWRITE_RULE[MULT_SYM] DIV_MULT; EXP_2_NE_0]);;

let n2w_DIV = prove
 (`!a n. a < dimword(:N) ==> word (a DIV 2 EXP n):N word = word_ushr (word a) n`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[word_ushr; VAL_WORD] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[dimword_def]) THEN ASM_SIMP_TAC[MOD_LT]);;

(* ------------------------------------------------------------------------- *)
(* words: bit fields (word_bits, word_extract, word_slice) and w2w.          *)
(* ------------------------------------------------------------------------- *)

let BIT_WORD_BITS = prove
 (`!h l (w:N word) i. bit i (word_bits h l w) <=> i + l <= h /\ bit (i + l) w`,
  REPEAT GEN_TAC THEN REWRITE_TAC[word_bits_DEF; BIT_WORD_OF_BITS; IN] THEN
  ASM_CASES_TAC `bit (i + l) (w:N word)` THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o ONCE_REWRITE_RULE[BIT_GUARD]) THEN ARITH_TAC);;

let BIT_WORD_EXTRACT = prove
 (`!h l (w:M word) i.
     bit i (word_extract h l w:N word) <=>
     i < dimindex(:N) /\ i + l <= h /\ bit (i + l) w`,
  REWRITE_TAC[word_extract_DEF; BIT_WORD_ZX; BIT_WORD_BITS]);;

let BIT_WORD_SLICE = prove
 (`!h l (w:N word) i. bit i (word_slice h l w) <=> l <= i /\ i <= h /\ bit i w`,
  REPEAT GEN_TAC THEN REWRITE_TAC[word_slice_DEF; BIT_WORD_OF_BITS; IN] THEN
  ASM_CASES_TAC `bit i (w:N word)` THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o ONCE_REWRITE_RULE[BIT_GUARD]) THEN ARITH_TAC);;

let VAL_WORD_BITS = prove
 (`!h l (w:N word). val(word_bits h l w) = BITS h l (val w)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[NUMBIT_EQ; NUMBIT_VAL; BIT_WORD_BITS] THEN
  REWRITE_TAC[NUMBIT_BITS; NUMBIT_VAL] THEN X_GEN_TAC `i:num` THEN
  REWRITE_TAC[ADD_SYM] THEN
  ASM_CASES_TAC `bit (i + l) (w:N word)` THEN ASM_REWRITE_TAC[] THEN ARITH_TAC);;

let word_bits_subword = prove
 (`!h l (w:N word). word_bits h l w = word_subword w (l,(h + 1) - l):N word`,
  REPEAT GEN_TAC THEN REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_BITS; BIT_WORD_SUBWORD] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN REWRITE_TAC[ADD_SYM] THEN
  ASM_CASES_TAC `bit (i + l) (w:N word)` THEN ASM_REWRITE_TAC[] THEN
  ASM_ARITH_TAC);;

let word_extract_subword = prove
 (`!h l (w:M word). word_extract h l w:N word = word_subword w (l,(h + 1) - l)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_EXTRACT; BIT_WORD_SUBWORD] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[ADD_SYM] THEN
  ASM_CASES_TAC `bit (i + l) (w:M word)` THEN ASM_REWRITE_TAC[] THEN
  ASM_ARITH_TAC);;

let word_bits_n2w = prove
 (`!h l n. word_bits h l (word n:N word) =
           word (BITS (MIN h (dimindex(:N) - 1)) l n)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_BITS; BIT_WORD; GSYM numbit] THEN
  REWRITE_TAC[NUMBIT_BITS] THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[ADD_SYM] THEN
  ASM_CASES_TAC `numbit (i + l) n` THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

let w2w_n2w = prove
 (`!n. word_zx (word n:M word):N word =
       if dimindex(:N) <= dimindex(:M) then word n
       else word (BITS (dimindex(:M) - 1) 0 n)`,
  GEN_TAC THEN REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_ZX] THEN
  COND_CASES_TAC THEN REWRITE_TAC[BIT_WORD; GSYM numbit; NUMBIT_BITS] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN ASM_REWRITE_TAC[ADD_CLAUSES] THEN
  ASM_CASES_TAC `numbit i n` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `(:M)` DIMINDEX_GE_1) THEN ASM_ARITH_TAC);;

let word_extract_n2w = prove
 (`!h l n.
     word_extract h l (word n:M word):N word =
     if dimindex(:N) <= dimindex(:M)
     then word (BITS (MIN h (dimindex(:M) - 1)) l n)
     else word (BITS (MIN (MIN h (dimindex(:M) - 1)) (dimindex(:M) - 1 + l)) l n)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[word_extract_DEF; word_bits_n2w; w2w_n2w] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN AP_TERM_TAC THEN
  REWRITE_TAC[NUMBIT_EQ; NUMBIT_BITS] THEN GEN_TAC THEN
  REWRITE_TAC[ADD_CLAUSES] THEN
  ASM_CASES_TAC `numbit (l + i) n` THEN ASM_REWRITE_TAC[] THEN ARITH_TAC);;

let WORD_BITS_EXTRACT = prove
 (`!h l (w:N word). word_bits h l w = word_extract h l w`,
  REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_BITS; BIT_WORD_EXTRACT] THEN
  MESON_TAC[]);;

let WORD_w2w_EXTRACT = prove
 (`!w:M word. word_zx w:N word = word_extract (dimindex(:M) - 1) 0 w`,
  GEN_TAC THEN REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_ZX; BIT_WORD_EXTRACT] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN ASM_REWRITE_TAC[ADD_CLAUSES] THEN
  ONCE_REWRITE_TAC[BIT_GUARD] THEN
  REWRITE_TAC[GSYM CONJ_ASSOC; GSYM LT_DIMINDEX_LE_HB] THEN MESON_TAC[]);;

let WORD_ALL_BITS = prove
 (`!w:N word h. dimindex(:N) - 1 <= h ==> word_bits h 0 w = w`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_BITS] THEN
  REWRITE_TAC[ADD_CLAUSES] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(TAUT `p ==> (p /\ q <=> q)`) THEN ASM_ARITH_TAC);;

let WORD_BITS_COMP_THM = prove
 (`!h1 l1 h2 l2 (w:N word).
     word_bits h2 l2 (word_bits h1 l1 w) =
     word_bits (MIN h1 (h2 + l1)) (l2 + l1) w`,
  REPEAT GEN_TAC THEN REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_BITS] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN REWRITE_TAC[ADD_ASSOC] THEN
  ASM_CASES_TAC `bit ((i + l2) + l1) (w:N word)` THEN ASM_REWRITE_TAC[] THEN
  ARITH_TAC);;

let w2w_w2w = prove
 (`!w:A word. word_zx (word_zx w:B word):C word =
              word_zx (word_bits (dimindex(:B) - 1) 0 w)`,
  GEN_TAC THEN REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_ZX; BIT_WORD_BITS] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN ASM_REWRITE_TAC[ADD_CLAUSES] THEN
  REWRITE_TAC[GSYM LT_DIMINDEX_LE_HB] THEN MESON_TAC[]);;

let word_bits_w2w = prove
 (`!w:M word h l.
     word_bits h l (word_zx w:N word) =
     word_zx (word_bits (MIN h (dimindex(:N) - 1)) l w)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_ZX; BIT_WORD_BITS] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `bit (i + l) (w:M word)` THEN ASM_REWRITE_TAC[] THEN
  ASM_ARITH_TAC);;

let w2n_w2w = prove
 (`!w:M word. val(word_zx w:N word) =
              if dimindex(:M) <= dimindex(:N) then val w
              else val(word_bits (dimindex(:N) - 1) 0 w)`,
  GEN_TAC THEN REWRITE_TAC[VAL_WORD_ZX_GEN; VAL_WORD_BITS; BITS_THM] THEN
  REWRITE_TAC[CONJUNCT1 EXP; DIV_1; SUB_0] THEN COND_CASES_TAC THENL
   [MATCH_MP_TAC MOD_LT THEN TRANS_TAC LTE_TRANS `2 EXP dimindex(:M)` THEN
    ASM_REWRITE_TAC[VAL_BOUND; WORDSAUX_EXP2_LE];
    AP_TERM_TAC THEN AP_TERM_TAC THEN
    MP_TAC(ISPEC `(:N)` DIMINDEX_GE_1) THEN ARITH_TAC]);;

(* bit-level reasoning: split on the single bit atom tm, which, when true, *)
(* also bounds its index by the word size                                  *)

let BIT_ATOM_CASES_TAC (tm:term) : tactic =
  ASM_CASES_TAC tm THEN ASM_REWRITE_TAC[] THEN
  TRY(FIRST_X_ASSUM(fun th -> if concl th = tm
                              then MP_TAC(ONCE_REWRITE_RULE[BIT_GUARD] th)
                              else failwith "BIT_ATOM_CASES_TAC"));;

let WORD_EXTRACT_COMP_THM = prove
 (`!w:C word h l m n.
     word_extract h l (word_extract m n w:B word):A word =
     word_extract
       (MIN m (MIN (h + n) (MIN (dimindex(:C) - 1) ((dimindex(:B) + n) - 1))))
       (l + n) w`,
  REPEAT GEN_TAC THEN REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_EXTRACT] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN ASM_REWRITE_TAC[GSYM ADD_ASSOC] THEN
  BIT_ATOM_CASES_TAC `bit (i + l + n) (w:C word)` THEN
  MP_TAC(ISPEC `(:B)` DIMINDEX_GE_1) THEN MP_TAC(ISPEC `(:C)` DIMINDEX_GE_1) THEN
  ARITH_TAC);;

let WORD_EXTRACT_BITS_COMP = prove
 (`!j k h l (n:M word).
     word_extract j k (word_bits h l n):N word =
     word_extract (MIN h (j + l)) (k + l) n`,
  REPEAT GEN_TAC THEN REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_EXTRACT; BIT_WORD_BITS] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN ASM_REWRITE_TAC[GSYM ADD_ASSOC] THEN
  BIT_ATOM_CASES_TAC `bit (i + k + l) (n:M word)` THEN ARITH_TAC);;

let WORD_EXTRACT_MIN_HIGH = prove
 (`(!h l w:A word.
      dimindex(:A) <= dimindex(:B) + l /\ dimindex(:A) <= h ==>
      word_extract h l w:B word = word_extract (dimindex(:A) - 1) l w) /\
   (!h l w:A word.
      dimindex(:B) + l < dimindex(:A) /\ dimindex(:B) + l <= h ==>
      word_extract h l w:B word = word_extract ((dimindex(:B) + l) - 1) l w)`,
  CONJ_TAC THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_EXTRACT] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  BIT_ATOM_CASES_TAC `bit (i + l) (w:A word)` THEN ASM_ARITH_TAC);;

let WORD_EXTRACT_ID = prove
 (`!w:N word h. val w < 2 EXP SUC h ==> word_extract h 0 w = w`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_EXTRACT] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN ASM_REWRITE_TAC[ADD_CLAUSES] THEN
  ASM_CASES_TAC `bit i (w:N word)` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[ARITH_RULE `i <= h <=> i < SUC h`] THEN
  UNDISCH_TAC `bit i (w:N word)` THEN REWRITE_TAC[GSYM NUMBIT_VAL] THEN
  ASM_MESON_TAC[NOT_BIT_GT_TWOEXP; LTE_TRANS; WORDSAUX_EXP2_LE; NOT_LT]);;

let WORD_EXTRACT_LSL2 = prove
 (`!h l n (w:A word).
     dimindex(:B) + l <= h + n ==>
     word_shl (word_extract h l w) n:B word =
     word_shl (word_extract ((dimindex(:B) + l) - (n + 1)) l w) n`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_SHL; BIT_WORD_EXTRACT] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `n <= i` THEN ASM_REWRITE_TAC[] THEN
  BIT_ATOM_CASES_TAC `bit (i - n + l) (w:A word)` THEN ASM_ARITH_TAC);;

(* (h >< 0) w is w2w w when h covers the target width *)

let WORD_EXTRACT_ZX = prove
 (`!h (w:A word). dimindex(:B) - 1 <= h ==> word_extract h 0 w:B word = word_zx w`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_EXTRACT; BIT_WORD_ZX] THEN
  REWRITE_TAC[ADD_CLAUSES] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(TAUT `p ==> (p /\ q <=> q)`) THEN ASM_ARITH_TAC);;

let WORD_EXTRACT_OVER_ADD = prove
 (`!a b:A word h.
     dimindex(:B) - 1 <= h /\ dimindex(:B) <= dimindex(:A) ==>
     word_extract h 0 (word_add a b):B word =
     word_add (word_extract h 0 a) (word_extract h 0 b)`,
  SIMP_TAC[WORD_EXTRACT_ZX; WORD_ZX_ADD]);;

let WORD_EXTRACT_OVER_MUL = prove
 (`!a b:A word h.
     dimindex(:B) - 1 <= h /\ dimindex(:B) <= dimindex(:A) ==>
     word_extract h 0 (word_mul a b):B word =
     word_mul (word_extract h 0 a) (word_extract h 0 b)`,
  SIMP_TAC[WORD_EXTRACT_ZX; WORD_ZX_MUL]);;

let WORD_EXTRACT_OVER_BITWISE = prove
 (`(!h l v w:A word.
      word_and (word_extract h l v) (word_extract h l w):B word =
      word_extract h l (word_and v w)) /\
   (!h l v w:A word.
      word_or (word_extract h l v) (word_extract h l w):B word =
      word_extract h l (word_or v w)) /\
   (!h l v w:A word.
      word_xor (word_extract h l v) (word_extract h l w):B word =
      word_extract h l (word_xor v w))`,
  REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_EXTRACT; BIT_WORD_AND_ALT; BIT_WORD_OR_ALT;
              BIT_WORD_XOR_ALT] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC TAUT);;

let WORD_w2w_OVER_BITWISE = prove
 (`(!v w:A word. word_and (word_zx v) (word_zx w) = word_zx (word_and v w):B word) /\
   (!v w:A word. word_or (word_zx v) (word_zx w) = word_zx (word_or v w):B word) /\
   (!v w:A word. word_xor (word_zx v) (word_zx w) = word_zx (word_xor v w):B word)`,
  REWRITE_TAC[WORD_ZX_AND; WORD_ZX_OR; WORD_ZX_XOR]);;

let WORD_w2w_OVER_MUL = prove
 (`!a b:A word.
     word_zx (word_mul a b):B word =
     word_bits (dimindex(:A) - 1) 0 (word_mul (word_zx a) (word_zx b))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_BITS; BITS_THM; VAL_WORD_ZX_GEN; VAL_WORD_MUL;
              CONJUNCT1 EXP; DIV_1; SUB_0; MOD_MULT_MOD2] THEN
  SUBGOAL_THEN `SUC (dimindex(:A) - 1) = dimindex(:A)` SUBST1_TAC THENL
   [MP_TAC(ISPEC `(:A)` DIMINDEX_GE_1) THEN ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[MOD_MOD_EXP_MIN] THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC);;

let word_lsr_n2w = prove
 (`!w:N word n. word_ushr w n = word_bits (dimindex(:N) - 1) n w`,
  REPEAT GEN_TAC THEN REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_USHR; BIT_WORD_BITS] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  BIT_ATOM_CASES_TAC `bit (i + n) (w:N word)` THEN ARITH_TAC);;

let WORD_BITS_LSL = prove
 (`!h l n (w:N word).
     h < dimindex(:N) ==>
     word_bits h l (word_shl w n) =
     if n <= h then word_shl (word_bits (h - n) (l - n) w) (n - l) else word 0`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[WORD_EQ_BITS_ALT] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  REWRITE_TAC[BIT_WORD_BITS; BIT_WORD_SHL] THEN COND_CASES_TAC THENL
   [ALL_TAC; REWRITE_TAC[BIT_WORD_0] THEN ASM_ARITH_TAC] THEN
  REWRITE_TAC[BIT_WORD_SHL; BIT_WORD_BITS] THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `n <= i + l` THEN ASM_REWRITE_TAC[] THENL
   [ALL_TAC; ASM_ARITH_TAC] THEN
  SUBGOAL_THEN `(i - (n - l)) + (l - n) = (i + l) - n` SUBST1_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  BIT_ATOM_CASES_TAC `bit ((i + l) - n) (w:N word)` THEN ASM_ARITH_TAC);;

let w2w_LSL = prove
 (`!w:A word n.
     word_zx (word_shl w n):B word =
     if n < dimindex(:A)
     then word_shl (word_zx (word_bits ((dimindex(:A) - 1) - n) 0 w)) n
     else word 0`,
  REPEAT GEN_TAC THEN REWRITE_TAC[WORD_EQ_BITS_ALT] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  REWRITE_TAC[BIT_WORD_ZX; BIT_WORD_SHL] THEN COND_CASES_TAC THENL
   [ALL_TAC; REWRITE_TAC[BIT_WORD_0] THEN ASM_ARITH_TAC] THEN
  REWRITE_TAC[BIT_WORD_SHL; BIT_WORD_ZX; BIT_WORD_BITS; ADD_CLAUSES] THEN
  ASM_REWRITE_TAC[] THEN
  BIT_ATOM_CASES_TAC `bit (i - n) (w:A word)` THEN ASM_ARITH_TAC);;

let WORD_AND_EXP_SUB1 = prove
 (`!m n. word_and (word n) (word (2 EXP m - 1)):N word = word (n MOD 2 EXP m)`,
  REWRITE_TAC[WORD_AND_MASK_WORD; VAL_WORD; MOD_MOD_EXP_MIN] THEN
  ONCE_REWRITE_TAC[GSYM WORD_MOD_SIZE] THEN REWRITE_TAC[MOD_MOD_EXP_MIN] THEN
  REPEAT GEN_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  ARITH_TAC);;

(* bit: SBIT and BITWISE *)

let SBIT_def = new_definition
  `SBIT b n = if b then 2 EXP n else 0`;;

let BITWISE_def = new_recursive_definition num_RECURSION
  `(BITWISE 0 (op:bool->bool->bool) x y = 0) /\
   (BITWISE (SUC n) op x y = BITWISE n op x y + SBIT (op (numbit n x) (numbit n y)) n)`;;

let BITWISE_LT_2EXP = prove
 (`!n op x y. BITWISE n op x y < 2 EXP n`,
  INDUCT_TAC THEN REWRITE_TAC[BITWISE_def; SBIT_def; EXP; ARITH] THEN
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN
  ASM_SIMP_TAC[ARITH_RULE `a < n ==> a + n < 2 * n`;
               ARITH_RULE `a < n ==> a + 0 < 2 * n`]);;

let NUMBIT_ADD_2EXP = prove
 (`!k a i. a < 2 EXP k ==> (numbit i (a + 2 EXP k) <=> i = k \/ numbit i a)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`2 EXP k * 1`; `a:num`] BITS_OF_NUM_ADD) THEN
  ASM_SIMP_TAC[DISJOINT_BITS_HILO; MULT_CLAUSES; BITS_OF_NUM_POW2] THEN
  DISCH_THEN(MP_TAC o AP_TERM `\s:num->bool. i IN s`) THEN
  REWRITE_TAC[IN_BITS_OF_NUM; GSYM numbit; IN_UNION; IN_SING; ADD_SYM]);;

let NUMBIT_BITWISE = prove
 (`!n op x y i. numbit i (BITWISE n op x y) <=> i < n /\ op (numbit i x) (numbit i y)`,
  INDUCT_TAC THEN REWRITE_TAC[BITWISE_def; BIT_ZERO; LT] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[SBIT_def] THEN
  COND_CASES_TAC THEN
  ASM_SIMP_TAC[ADD_CLAUSES; NUMBIT_ADD_2EXP; BITWISE_LT_2EXP] THEN
  ASM_CASES_TAC `i:num = n` THEN ASM_REWRITE_TAC[LT_REFL]);;

let word_and_n2w = prove
 (`!n m. word_and (word n) (word m):N word =
         word (BITWISE (dimindex(:N)) (/\) n m)`,
  REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_AND; BIT_WORD; GSYM numbit; NUMBIT_BITWISE] THEN
  MESON_TAC[]);;

(* the concatenation; HOL4 'a + 'b is (M,N)finite_sum *)

let word_concat_def = prove
 (`!(v:M word) (w:N word).
     word_join v w:P word = word_zx (word_join v w:((M,N)finite_sum)word)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN] THEN
  SIMP_TAC[VAL_WORD_JOIN_SIMPLE; DIMINDEX_FINITE_SUM] THEN
  REWRITE_TAC[VAL_WORD_JOIN]);;

let word_join_def = prove
 (`!(v:M word) (w:N word).
     word_join v w:((M,N)finite_sum)word =
     word_or (word_shl (word_zx v) (dimindex(:N))) (word_zx w)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[WORD_EQ_BITS_ALT] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[BIT_WORD_JOIN; BIT_WORD_OR_ALT; BIT_WORD_SHL; BIT_WORD_ZX] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[DIMINDEX_FINITE_SUM]) THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL
   [ASM_SIMP_TAC[ARITH_RULE `i < n ==> ~(n <= i)`]; ALL_TAC] THEN
  SUBGOAL_THEN `~bit i (w:N word)` (fun th -> REWRITE_TAC[th]) THENL
   [ONCE_REWRITE_TAC[BIT_GUARD] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  BIT_ATOM_CASES_TAC `bit (i - dimindex(:N)) (v:M word)` THEN
  REWRITE_TAC[DIMINDEX_FINITE_SUM] THEN ASM_ARITH_TAC);;

let word_add_n2w = prove
 (`!m n. word_add (word m) (word n):N word = word (m + n)`,
  REWRITE_TAC[WORD_ADD]);;

let word_mul_n2w = prove
 (`!m n. word_mul (word m) (word n):N word = word (m * n)`,
  REWRITE_TAC[WORD_MUL]);;

let word_ror_n2w = prove
 (`!n a. word_ror (word a:N word) n =
         let x = n MOD dimindex(:N) in
         word (BITS (dimindex(:N) - 1) x a + BITS (x - 1) 0 a * 2 EXP (dimindex(:N) - x))`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[WORD_ROR_MOD] THEN
  CONV_TAC(RAND_CONV let_CONV) THEN
  MP_TAC(SPECL [`n:num`; `dimindex(:N)`] MOD_LT_EQ) THEN
  REWRITE_TAC[DIMINDEX_NONZERO] THEN
  SPEC_TAC(`n MOD dimindex(:N)`,`x:num`) THEN GEN_TAC THEN DISCH_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM WORD_VAL] THEN
  ASM_SIMP_TAC[VAL_WORD_ROR; LT_IMP_LE; VAL_WORD; BITS_THM] THEN
  REWRITE_TAC[CONJUNCT1 EXP; DIV_1; SUB_0] THEN
  SUBGOAL_THEN `SUC (dimindex(:N) - 1) - x = dimindex(:N) - x` SUBST1_TAC THENL
   [MP_TAC(ISPEC `(:N)` DIMINDEX_GE_1) THEN ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[MOD_MOD_EXP_MIN] THEN
  SUBGOAL_THEN `(a MOD 2 EXP dimindex(:N)) DIV 2 EXP x =
                (a DIV 2 EXP x) MOD 2 EXP (dimindex(:N) - x)`
  SUBST1_TAC THENL
   [REWRITE_TAC[DIV_MOD; GSYM EXP_ADD] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `x = 0` THENL
   [ASM_REWRITE_TAC[CONJUNCT1 EXP; MOD_1; MULT_CLAUSES; ADD_CLAUSES; SUB_0] THEN
    ONCE_REWRITE_TAC[GSYM WORD_MOD_SIZE] THEN AP_TERM_TAC THEN
    REWRITE_TAC[DIV_1; MOD_MULT_ADD; MOD_MOD_REFL];
    AP_TERM_TAC THEN
    SUBGOAL_THEN `SUC (x - 1) = x /\ MIN (dimindex(:N)) x = x` (fun th -> REWRITE_TAC[th]) THENL
     [ASM_ARITH_TAC; ARITH_TAC]]);;

let IVAL_NEG_VAL = prove
 (`!a:N word. ival a < &0 ==> &(val (word_neg a)) = --(ival a)`,
  GEN_TAC THEN REWRITE_TAC[GSYM MSB_IVAL; IVAL_VAL] THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[BITVAL_CLAUSES; VAL_WORD_NEG_CASES] THEN
  UNDISCH_TAC `bit (dimindex(:N) - 1) (a:N word)` THEN
  REWRITE_TAC[MSB_VAL] THEN DISCH_TAC THEN
  MP_TAC(ISPEC `a:N word` VAL_BOUND) THEN
  MP_TAC(SPEC `dimindex(:N) - 1` EXP_2_NE_0) THEN
  COND_CASES_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  REPEAT DISCH_TAC THEN ASM_SIMP_TAC[GSYM INT_OF_NUM_SUB; LT_IMP_LE] THEN
  REWRITE_TAC[INT_OF_NUM_POW] THEN INT_ARITH_TAC);;

let IVAL_POS_VAL = prove
 (`!a:N word. &0 <= ival a ==> &(val a) = ival a`,
  GEN_TAC THEN REWRITE_TAC[GSYM INT_NOT_LT; GSYM MSB_IVAL; IVAL_VAL] THEN
  SIMP_TAC[BITVAL_CLAUSES] THEN INT_ARITH_TAC);;

let word_quot_def = prove
 (`!a b:N word.
     word_jdiv a b =
     if word_msb a then
       if word_msb b then word_udiv (word_neg a) (word_neg b)
       else word_neg (word_udiv (word_neg a) b)
     else if word_msb b then word_neg (word_udiv a (word_neg b))
     else word_udiv a b`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[word_jdiv; imodular; word_div_def; word_msb_def; MSB_IVAL] THEN
  REWRITE_TAC[WORD_IWORD; GSYM INT_OF_NUM_DIV; GSYM IWORD_INT_NEG] THEN
  MP_TAC(ISPEC `a:N word` IVAL_NEG_VAL) THEN MP_TAC(ISPEC `b:N word` IVAL_NEG_VAL) THEN
  MP_TAC(ISPEC `a:N word` IVAL_POS_VAL) THEN MP_TAC(ISPEC `b:N word` IVAL_POS_VAL) THEN
  SPEC_TAC(`&(val(word_neg(a:N word))):int`,`na:int`) THEN
  SPEC_TAC(`&(val(word_neg(b:N word))):int`,`nb:int`) THEN
  SPEC_TAC(`&(val(a:N word)):int`,`va:int`) THEN
  SPEC_TAC(`&(val(b:N word)):int`,`vb:int`) THEN
  SPEC_TAC(`ival(a:N word)`,`x:int`) THEN SPEC_TAC(`ival(b:N word)`,`y:int`) THEN
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `x:int < &0` THEN ASM_CASES_TAC `y:int < &0` THEN
  ASM_REWRITE_TAC[GSYM INT_NOT_LT] THEN
  REPEAT DISCH_TAC THEN ASM_REWRITE_TAC[] THEN AP_TERM_TAC THEN
  REWRITE_TAC[INT_SGN; INT_ABS] THEN
  ASM_REWRITE_TAC[GSYM INT_NOT_LT] THEN
  ASM_CASES_TAC `x:int = &0` THEN ASM_CASES_TAC `y:int = &0` THEN
  ASM_REWRITE_TAC[INT_DIV_0; INT_DIV_ZERO; INT_NEG_0; INT_LT_REFL] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[INT_NOT_LT]) THEN
  ASM_SIMP_TAC[INT_ARITH `x:int < &0 ==> ~(&0 < x)`;
               INT_ARITH `&0 <= x /\ ~(x = &0) ==> &0 < x`] THEN
  REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  TRY INT_ARITH_TAC THEN ASM_INT_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* integer: HOL4 src/integer/integerScript.sml, the rows the closure uses.   *)
(* Mostly HOL4 names of int.ml theorems.  HOL4's / and % on int are floor    *)
(* division and its remainder (the remainder has the sign of the divisor);   *)
(* HOL Light's div and rem are Euclidean (they agree for divisors > 0), so   *)
(* HOL4's / is int_div and % is integer_int_mod (HOL Light's int_mod is the  *)
(* congruence).  HOL4 leaves i / 0 unspecified; here i / 0 = 0.             *)
(* ------------------------------------------------------------------------- *)

let int_div_DEF = new_definition
  `int_div (i:int) j = if j < &0 then (--i) div (--j) else i div j`;;

let integer_int_mod_DEF = new_definition
  `integer_int_mod (i:int) j = i - int_div i j * j`;;

let int_mod = prove
 (`!i j. ~(j = &0) ==> integer_int_mod i j = i - int_div i j * j`,
  REWRITE_TAC[integer_int_mod_DEF]);;

let INT_DIV = prove
 (`!n m. ~(m = 0) ==> int_div (&n) (&m) = &(n DIV m)`,
  REWRITE_TAC[int_div_DEF; INT_ARITH `~(&m:int < &0)`; INT_OF_NUM_DIV]);;

let INT_DIV_NEG = prove
 (`!p q. ~(q = &0) ==> int_div p (--q) = int_div (--p) q`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[int_div_DEF; INT_NEG_NEG] THEN
  ASM_CASES_TAC `q:int < &0` THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[INT_ARITH `q:int < &0 ==> ~(--q < &0)`] THEN
  ASM_SIMP_TAC[INT_ARITH `~(q:int < &0) /\ ~(q = &0) ==> --q < &0`]);;

let INT_DIV_UNIQUE = prove
 (`!i j q. (?r. i = q * j + r /\
                (if j < &0 then j < r /\ r <= &0 else &0 <= r /\ r < j))
           ==> int_div i j = q`,
  REPEAT GEN_TAC THEN DISCH_THEN(X_CHOOSE_THEN `r:int` MP_TAC) THEN
  REWRITE_TAC[int_div_DEF] THEN ASM_CASES_TAC `j:int < &0` THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN MATCH_MP_TAC INT_DIV_UNIQ THENL
   [EXISTS_TAC `--r:int`; EXISTS_TAC `r:int`] THEN
  ASM_REWRITE_TAC[] THEN ASM_INT_ARITH_TAC);;

let INT_DIV_LMUL = prove
 (`!i j. ~(i = &0) ==> int_div (i * j) i = j`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[int_div_DEF] THEN COND_CASES_TAC THEN
  ASM_SIMP_TAC[INT_NEG_LMUL; INT_DIV_MUL; INT_NEG_EQ_0]);;

let INT_MOD = prove
 (`!n m. ~(m = 0) ==> integer_int_mod (&n) (&m) = &(n MOD m)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[integer_int_mod_DEF; int_div_DEF] THEN
  REWRITE_TAC[INT_ARITH `~(&m:int < &0)`; GSYM INT_OF_NUM_REM] THEN
  MP_TAC(SPECL [`&n:int`; `&m:int`] INT_DIVISION) THEN
  ASM_REWRITE_TAC[INT_OF_NUM_EQ] THEN INT_ARITH_TAC);;

let INT_MOD0 = prove
 (`!p. ~(p = &0) ==> integer_int_mod (&0) p = &0`,
  REWRITE_TAC[integer_int_mod_DEF; int_div_DEF; INT_NEG_0; INT_DIV_ZERO] THEN
  REWRITE_TAC[COND_ID] THEN INT_ARITH_TAC);;

let INT_DIV_CALCULATE = prove
 (`(!n m. ~(m = 0) ==> int_div (&n) (&m) = &(n DIV m)) /\
   (!p q. ~(q = &0) ==> int_div p (--q) = int_div (--p) q) /\
   (!m n. &m:int = &n <=> m = n) /\
   (!x:int. --x = &0 <=> x = &0) /\
   (!x:int. --(--x) = x)`,
  REWRITE_TAC[INT_DIV; INT_DIV_NEG; INT_OF_NUM_EQ; INT_NEG_EQ_0; INT_NEG_NEG]);;

let INT_MUL_CALCULATE = prove
 (`(!m n. &m * &n:int = &(m * n)) /\
   (!x y:int. --x * y = --(x * y)) /\
   (!x y:int. x * --y = --(x * y)) /\
   (!x:int. --(--x) = x)`,
  REWRITE_TAC[INT_OF_NUM_MUL; INT_MUL_LNEG; INT_MUL_RNEG; INT_NEG_NEG]);;

let INT_ADD = INT_OF_NUM_ADD;;

let INT_MUL = INT_OF_NUM_MUL;;

let INT_MUL_COMM = INT_MUL_SYM;;

let INT_EQ_NEG = INT_EQ_NEG2;;

let INT_ABS_EQ_ID = INT_ABS_REFL;;

(* HOL Light's NUM_OF_INT, INT_LT, INT_SUB, INT_ABS, int_le, int_ge, int_gt *)
(* and int_sub have other statements: the HOL4 ones get the prefix integer_ *)

let integer_NUM_OF_INT = NUM_OF_INT_OF_NUM;;

let integer_INT_LT = prove
 (`!m n. &m:int < &n <=> m < n`,
  REWRITE_TAC[INT_OF_NUM_LT]);;

let integer_INT_SUB = prove
 (`!n m. m <= n ==> &n - &m:int = &(n - m)`,
  SIMP_TAC[INT_OF_NUM_SUB]);;

let integer_INT_ABS = prove
 (`!n:int. abs n = if n < &0 then --n else n`,
  INT_ARITH_TAC);;

let integer_int_le = prove
 (`!x y:int. x <= y <=> ~(y < x)`,
  INT_ARITH_TAC);;

let integer_int_ge = INT_GE;;

let integer_int_gt = INT_GT;;

let integer_int_sub = INT_SUB;;

let INT_OF_NUM = prove
 (`!i. &(num_of_int i) = i <=> &0 <= i`,
  MESON_TAC[NUM_OF_INT]);;

let NUM_POSINT_EXISTS = prove
 (`!i:int. &0 <= i ==> ?n. i = &n`,
  REWRITE_TAC[GSYM INT_OF_NUM_EXISTS]);;

let INT_LDISTRIB = prove
 (`!z y x:int. x * (y + z) = x * y + x * z`,
  REWRITE_TAC[INT_ADD_LDISTRIB]);;

let INT_LE_LT1 = prove
 (`!x y:int. x <= y <=> x < y + &1`,
  INT_ARITH_TAC);;

let INT = prove
 (`!n. &(SUC n):int = &n + &1`,
  REWRITE_TAC[INT_OF_NUM_SUC]);;

let EQ_ADDL = prove
 (`!x y. x = x + y <=> y = 0`,
  ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* integer_word: port of HOL4 src/integer/integer_wordScript.sml (the rows   *)
(* the closure uses).  w2i = ival, i2w = iword.  HOL4's integer_word INT_MIN *)
(* INT_MAX UINT_MAX are the ints of the type: integer_word_INT_MIN etc.       *)
(* ------------------------------------------------------------------------- *)

let integer_word_UINT_MAX_DEF = new_definition
  `integer_word_UINT_MAX (s:A->bool) = &(dimword(:A)) - &1:int`;;

let integer_word_UINT_MAX_def = prove
 (`integer_word_UINT_MAX(:A) = &(dimword(:A)) - &1`,
  REWRITE_TAC[integer_word_UINT_MAX_DEF]);;

let integer_word_INT_MAX_DEF = new_definition
  `integer_word_INT_MAX (s:A->bool) = &(INT_MIN(:A)) - &1:int`;;

let integer_word_INT_MAX_def = prove
 (`integer_word_INT_MAX(:A) = &(INT_MIN(:A)) - &1`,
  REWRITE_TAC[integer_word_INT_MAX_DEF]);;

let integer_word_INT_MIN_DEF = new_definition
  `integer_word_INT_MIN (s:A->bool) = --integer_word_INT_MAX(:A) - &1`;;

let integer_word_INT_MIN_def = prove
 (`integer_word_INT_MIN(:A) = --integer_word_INT_MAX(:A) - &1`,
  REWRITE_TAC[integer_word_INT_MIN_DEF]);;

let IVAL_IWORD_INT_RANGE = prove
 (`!i. integer_word_INT_MIN(:N) <= i /\ i <= integer_word_INT_MAX(:N) <=>
       --(&2 pow (dimindex(:N) - 1)) <= i /\ i < &2 pow (dimindex(:N) - 1)`,
  REWRITE_TAC[integer_word_INT_MIN_def; integer_word_INT_MAX_def; INT_MIN_def] THEN
  REWRITE_TAC[GSYM INT_OF_NUM_POW] THEN INT_ARITH_TAC);;

let i2w_def = prove
 (`!i. iword i:N word =
       if i < &0 then word_neg (word (num_of_int (--i))) else word (num_of_int i)`,
  GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[WORD_IWORD] THENL
   [SUBGOAL_THEN `&(num_of_int(--i)) = --i` SUBST1_TAC THENL
     [MATCH_MP_TAC INT_OF_NUM_OF_INT THEN ASM_INT_ARITH_TAC;
      REWRITE_TAC[GSYM IWORD_INT_NEG; INT_NEG_NEG]];
    SUBGOAL_THEN `&(num_of_int i) = i` SUBST1_TAC THENL
     [MATCH_MP_TAC INT_OF_NUM_OF_INT THEN ASM_INT_ARITH_TAC; REFL_TAC]]);;

let w2i_def = prove
 (`!w:N word. ival w = if word_msb w then --(&(val (word_neg w))) else &(val w)`,
  GEN_TAC THEN REWRITE_TAC[word_msb_def; MSB_IVAL] THEN COND_CASES_TAC THEN
  ASM_SIMP_TAC[IVAL_NEG_VAL; INT_NEG_NEG] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC IVAL_POS_VAL THEN ASM_INT_ARITH_TAC);;

let w2i_i2w = prove
 (`!i. integer_word_INT_MIN(:N) <= i /\ i <= integer_word_INT_MAX(:N)
       ==> ival (iword i:N word) = i`,
  REWRITE_TAC[IVAL_IWORD_INT_RANGE; IVAL_IWORD]);;

let word_0_w2i = IVAL_WORD_0;;

let word_i2w_add = prove
 (`!a b. word_add (iword a) (iword b):N word = iword (a + b)`,
  REWRITE_TAC[IWORD_INT_ADD]);;

let word_i2w_mul = prove
 (`!a b. word_mul (iword a) (iword b):N word = iword (a * b)`,
  REWRITE_TAC[IWORD_INT_MUL]);;

let i2w_pos = prove
 (`!n. iword (&n):N word = word n`,
  REWRITE_TAC[WORD_IWORD]);;

let i2w_w2n_w2w = prove
 (`!w:A word. iword (&(val w)):B word = word_zx w`,
  REWRITE_TAC[GSYM WORD_IWORD; word_zx]);;

let MULT_MINUS_ONE = prove
 (`!i. word_mul (word_neg (word 1)) (iword i):N word = iword (--i)`,
  REWRITE_TAC[IWORD_INT_NEG] THEN CONV_TAC WORD_RULE);;

let w2n_i2w = prove
 (`!n. &(val (iword n:N word)) = integer_int_mod n (&(dimword(:N)))`,
  GEN_TAC THEN REWRITE_TAC[integer_int_mod_DEF; int_div_DEF; dimword_def] THEN
  REWRITE_TAC[INT_ARITH `~(&m:int < &0)`; GSYM INT_OF_NUM_POW] THEN
  MP_TAC(SPECL [`n:int`; `(&2:int) pow dimindex(:N)`] INT_DIVISION) THEN
  REWRITE_TAC[INT_POW_EQ_0; INT_OF_NUM_EQ; ARITH_EQ] THEN
  REWRITE_TAC[INT_ABS_POW; INT_ABS_NUM] THEN STRIP_TAC THEN
  MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `n rem (&2:int) pow dimindex(:N)` THEN
  CONJ_TAC THENL [ALL_TAC; ASM_INT_ARITH_TAC] THEN
  REWRITE_TAC[iword; VAL_WORD] THEN
  MP_TAC(SPEC `n rem (&2:int) pow dimindex(:N)` INT_OF_NUM_OF_INT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> GEN_REWRITE_TAC RAND_CONV [SYM th]) THEN
  AP_TERM_TAC THEN MATCH_MP_TAC MOD_LT THEN
  REWRITE_TAC[GSYM INT_OF_NUM_LT; GSYM INT_OF_NUM_POW] THEN
  ASM_SIMP_TAC[INT_OF_NUM_OF_INT]);;

let w2w_i2w = prove
 (`!i. dimindex(:A) <= dimindex(:B)
       ==> word_zx (iword i:B word):A word = iword i`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[word_zx; WORD_IWORD; IWORD_EQ] THEN
  MP_TAC(ISPEC `i:int` (INST_TYPE [`:B`,`:N`] VAL_IWORD_CONG)) THEN
  SUBGOAL_THEN `(&2:int) pow dimindex(:A) divides &2 pow dimindex(:B)` MP_TAC THENL
   [REWRITE_TAC[int_divides] THEN EXISTS_TAC `(&2:int) pow (dimindex(:B) - dimindex(:A))` THEN
    REWRITE_TAC[GSYM INT_POW_ADD] THEN AP_TERM_TAC THEN ASM_ARITH_TAC;
    CONV_TAC INTEGER_RULE]);;

let i2w_DIV = prove
 (`!n i.
     n < dimindex(:N) /\ integer_word_INT_MIN(:N) <= i /\ i <= integer_word_INT_MAX(:N)
     ==> iword (int_div i (&2 pow n)):N word = word_ishr (iword i) n`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[word_ishr] THEN
  SUBGOAL_THEN `ival(iword i:N word) = i` SUBST1_TAC THENL
   [ASM_SIMP_TAC[w2i_i2w]; ALL_TAC] THEN
  REWRITE_TAC[int_div_DEF] THEN
  SIMP_TAC[INT_ARITH `&0 < x ==> ~(x:int < &0)`; INT_LT_POW2]);;

(* ------------------------------------------------------------------------- *)
(* byte: port of HOL4 src/n-bit/byteScript.sml (the rows the closure uses).  *)
(* Get and set bytes in a word; HOL4 word8 is byte = (8)word.                *)
(* ------------------------------------------------------------------------- *)

let byte_index_DEF = new_definition
  `byte_index (a:N word) is_bigendian =
     let d = dimindex(:N) DIV 8 in
     if is_bigendian then 8 * ((d - 1) - val a MOD d) else 8 * (val a MOD d)`;;

let byte_index_def = prove
 (`!(a:N word) is_bigendian.
     byte_index a is_bigendian =
     let d = dimindex(:N) DIV 8 in
     if is_bigendian then 8 * ((d - 1) - val a MOD d) else 8 * (val a MOD d)`,
  REWRITE_TAC[byte_index_DEF]);;

let get_byte_DEF = new_definition
  `get_byte (a:N word) (w:N word) is_bigendian =
     word_zx (word_ushr w (byte_index a is_bigendian)):byte`;;

let get_byte_def = prove
 (`!(a:N word) (w:N word) is_bigendian.
     get_byte a w is_bigendian =
     word_zx (word_ushr w (byte_index a is_bigendian)):byte`,
  REWRITE_TAC[get_byte_DEF]);;

let word_slice_alt_DEF = new_definition
  `word_slice_alt h l (w:N word) = word_of_bits (\i. l <= i /\ i < h /\ bit i w):N word`;;

let word_slice_alt_def = prove
 (`!h l (w:N word).
     word_slice_alt h l w = word_of_bits (\i. l <= i /\ i < h /\ bit i w):N word`,
  REWRITE_TAC[word_slice_alt_DEF]);;

let BIT_WORD_SLICE_ALT = prove
 (`!h l (w:N word) i. bit i (word_slice_alt h l w) <=> l <= i /\ i < h /\ bit i w`,
  REPEAT GEN_TAC THEN REWRITE_TAC[word_slice_alt_DEF; BIT_WORD_OF_BITS; IN] THEN
  MESON_TAC[BIT_GUARD]);;

let set_byte_DEF = new_definition
  `set_byte (a:N word) (b:byte) (w:N word) is_bigendian =
     let i = byte_index a is_bigendian in
     word_or (word_slice_alt (dimindex(:N)) (i + 8) w)
             (word_or (word_shl (word_zx b) i) (word_slice_alt i 0 w))`;;

let set_byte_def = prove
 (`!(a:N word) (b:byte) (w:N word) is_bigendian.
     set_byte a b w is_bigendian =
     let i = byte_index a is_bigendian in
     word_or (word_slice_alt (dimindex(:N)) (i + 8) w)
             (word_or (word_shl (word_zx b) i) (word_slice_alt i 0 w))`,
  REWRITE_TAC[set_byte_DEF]);;

let bytes_in_word_def = new_definition
  `bytes_in_word = word (dimindex(:N) DIV 8):N word`;;

let word_of_bytes_DEF = new_recursive_definition list_RECURSION
  `(word_of_bytes be (a:N word) [] = word 0:N word) /\
   (word_of_bytes be a (CONS (b:byte) bs) =
      set_byte a b (word_of_bytes be (word_add a (word 1)) bs) be)`;;

let word_of_bytes_def = prove
 (`(!be (a:N word). word_of_bytes be a [] = word 0:N word) /\
   (!be (a:N word) (b:byte) bs.
      word_of_bytes be a (CONS b bs) =
      set_byte a b (word_of_bytes be (word_add a (word 1)) bs) be)`,
  REWRITE_TAC[word_of_bytes_DEF]);;

let bytes_to_word_DEF = cake_def
  `bytes_to_word k (a:N word) (bs:byte list) (w:N word) be =
     if k = 0 then w else
     match bs with
       [] -> w
     | CONS b bs -> set_byte a b (bytes_to_word (k - 1) (word_add a (word 1)) bs w be) be`;;

let bytes_to_word_def = prove
 (`!k (a:N word) (bs:byte list) (w:N word) be.
     bytes_to_word k a bs w be =
     if k = 0 then w
     else list_CASE bs w
            (\b bs. set_byte a b (bytes_to_word (k - 1) (word_add a (word 1)) bs w be) be)`,
  REWRITE_TAC[GSYM bytes_to_word_DEF]);;

let set_byte_change_a = prove
 (`!(a:N word) a' (b:byte) (w:N word) be.
     val a MOD (dimindex(:N) DIV 8) = val a' MOD (dimindex(:N) DIV 8)
     ==> set_byte a b w be = set_byte a' b w be`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[set_byte_DEF; byte_index_DEF] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN ASM_REWRITE_TAC[]);;

let bytes_to_word_eq = prove
 (`!k (a:N word) (b:byte) bs (w:N word) be.
     bytes_to_word 0 a bs w be = w /\
     bytes_to_word k a [] w be = w /\
     bytes_to_word (SUC k) a (CONS b bs) w be =
     set_byte a b (bytes_to_word k (word_add a (word 1)) bs w be) be`,
  REPEAT GEN_TAC THEN REPEAT CONJ_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [bytes_to_word_def] THEN
  REWRITE_TAC[NOT_SUC; SUC_SUB1; list_CASE] THEN COND_CASES_TAC THEN
  REWRITE_TAC[list_CASE]);;

let bytes_to_word_same = prove
 (`!bw (k:N word) (b1:byte list) (w:N word) be b2.
     (!n. n < bw ==> n < LENGTH b1 /\ n < LENGTH b2 /\ EL n b1 = EL n b2)
     ==> bytes_to_word bw k b1 w be = bytes_to_word bw k b2 w be`,
  INDUCT_TAC THENL [REWRITE_TAC[bytes_to_word_eq]; ALL_TAC] THEN
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `b1:byte list` list_CASES) THEN
  STRUCT_CASES_TAC(ISPEC `b2:byte list` list_CASES) THEN
  REWRITE_TAC[LENGTH] THEN DISCH_TAC THEN
  TRY(FIRST_X_ASSUM(MP_TAC o SPEC `0`) THEN REWRITE_TAC[LT_0; LT_REFL] THEN NO_TAC) THEN
  REWRITE_TAC[bytes_to_word_eq] THEN
  FIRST_ASSUM(MP_TAC o SPEC `0`) THEN REWRITE_TAC[LT_0; EL; HD] THEN
  DISCH_THEN SUBST1_TAC THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `SUC n`) THEN
  ASM_REWRITE_TAC[LT_SUC; EL; TL]);;

let BYTE_INDEX_BOUND = prove
 (`!(a:N word) be.
     8 <= dimindex(:N) ==> byte_index a be + 8 <= dimindex(:N)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[byte_index_DEF] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  MP_TAC(SPECL [`dimindex(:N)`; `8`] DIVISION) THEN
  MP_TAC(SPECL [`val(a:N word)`; `dimindex(:N) DIV 8`] MOD_LT_EQ) THEN
  SUBGOAL_THEN `~(dimindex(:N) DIV 8 = 0)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[DIV_EQ_0; ARITH_EQ] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[ARITH_EQ] THEN
  SPEC_TAC(`val(a:N word) MOD (dimindex(:N) DIV 8)`,`r:num`) THEN
  SPEC_TAC(`dimindex(:N) DIV 8`,`q:num`) THEN REPEAT GEN_TAC THEN
  REPEAT DISCH_TAC THEN COND_CASES_TAC THEN ASM_ARITH_TAC);;

let get_byte_set_byte = prove
 (`!(a:N word) (b:byte) (w:N word) be.
     8 <= dimindex(:N) ==> get_byte a (set_byte a b w be) be = b`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPECL [`a:N word`; `be:bool`] o MATCH_MP
   (MESON[BYTE_INDEX_BOUND]
     `8 <= dimindex(:N) ==> !a:N word be. byte_index a be + 8 <= dimindex(:N)`)) THEN
  REWRITE_TAC[get_byte_DEF; set_byte_DEF] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  SPEC_TAC(`byte_index (a:N word) be`,`k:num`) THEN GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[WORD_EQ_BITS_ALT; DIMINDEX_8] THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[BIT_WORD_ZX; BIT_WORD_USHR; BIT_WORD_OR_ALT; BIT_WORD_SLICE_ALT;
                  BIT_WORD_SHL; DIMINDEX_8] THEN
  ASM_SIMP_TAC[ARITH_RULE `i < 8 ==> ~(k + 8 <= i + k) /\ ~(i + k < k) /\ k <= i + k`;
               ARITH_RULE `i < 8 /\ k + 8 <= n ==> i + k < n`; ADD_SUB] THEN
  ASM_SIMP_TAC[ARITH_RULE `i < 8 /\ 8 <= n ==> i < n`]);;

let word_to_bytes_aux_DEF = new_recursive_definition num_RECURSION
  `(word_to_bytes_aux 0 (w:N word) be = []:byte list) /\
   (word_to_bytes_aux (SUC n) w be =
      APPEND (word_to_bytes_aux n w be) [get_byte (word n:N word) w be])`;;

let word_to_bytes_aux_def = prove
 (`(!(w:N word) be. word_to_bytes_aux 0 w be = []:byte list) /\
   (!n (w:N word) be.
      word_to_bytes_aux (SUC n) w be =
      APPEND (word_to_bytes_aux n w be) [get_byte (word n:N word) w be])`,
  REWRITE_TAC[word_to_bytes_aux_DEF]);;

let word_to_bytes_DEF = new_definition
  `word_to_bytes (w:N word) be = word_to_bytes_aux (dimindex(:N) DIV 8) w be`;;

let word_to_bytes_def = prove
 (`!(w:N word) be. word_to_bytes w be = word_to_bytes_aux (dimindex(:N) DIV 8) w be`,
  REWRITE_TAC[word_to_bytes_DEF]);;

(* ------------------------------------------------------------------------- *)
(* alignment: port of HOL4 src/n-bit/alignmentScript.sml.  HOL4 aligned is   *)
(* alignment_aligned here: HOL Light's aligned n w means n divides val w     *)
(* (alignment_aligned p w is aligned (2 EXP p) w when p <= dimindex(:N)).    *)
(* ------------------------------------------------------------------------- *)

let align_DEF = new_definition
  `align p (w:N word) = word_slice (dimindex(:N) - 1) p w`;;

let align_def = prove
 (`!p (w:N word). align p w = word_slice (dimindex(:N) - 1) p w`,
  REWRITE_TAC[align_DEF]);;

let aligned_DEF = new_definition
  `alignment_aligned p (w:N word) <=> align p w = w`;;

let aligned_def = prove
 (`!p (w:N word). alignment_aligned p w <=> align p w = w`,
  REWRITE_TAC[aligned_DEF]);;

let byte_align_DEF = new_definition
  `byte_align (w:N word) = align (LOG2 (dimindex(:N) DIV 8)) w`;;

let byte_align_def = prove
 (`!w:N word. byte_align w = align (LOG2 (dimindex(:N) DIV 8)) w`,
  REWRITE_TAC[byte_align_DEF]);;

let byte_aligned_DEF = new_definition
  `byte_aligned (w:N word) <=> alignment_aligned (LOG2 (dimindex(:N) DIV 8)) w`;;

let byte_aligned_def = prove
 (`!w:N word. byte_aligned w <=> alignment_aligned (LOG2 (dimindex(:N) DIV 8)) w`,
  REWRITE_TAC[byte_aligned_DEF]);;

let NUMBIT_MUL_2EXP = prove
 (`!i k n. numbit i (n * 2 EXP k) <=> k <= i /\ numbit (i - k) n`,
  REPEAT GEN_TAC THEN
  MP_TAC(AP_TERM `\s:num->bool. i IN s` (SPECL [`n:num`; `k:num`]
    (CONJUNCT2 BITS_OF_NUM_MUL))) THEN
  REWRITE_TAC[IN_BITS_OF_NUM; GSYM numbit; IN_IMAGE] THEN
  DISCH_THEN SUBST1_TAC THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `j:num` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[ADD_SUB2; LE_ADD];
    STRIP_TAC THEN EXISTS_TAC `i - k:num` THEN ASM_REWRITE_TAC[] THEN
    ASM_ARITH_TAC]);;

let BIT_ALIGN = prove
 (`!p (w:N word) i. bit i (align p w) <=> p <= i /\ bit i w`,
  REWRITE_TAC[align_DEF; BIT_WORD_SLICE] THEN
  REPEAT GEN_TAC THEN BIT_ATOM_CASES_TAC `bit i (w:N word)` THEN ARITH_TAC);;

let align_w2n = prove
 (`!p (w:N word). align p w = word (val w DIV 2 EXP p * 2 EXP p)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_ALIGN; BIT_WORD] THEN
  REWRITE_TAC[GSYM numbit; NUMBIT_MUL_2EXP; NUMBIT_DIV_2EXP; NUMBIT_VAL] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `p:num <= i` THEN ASM_SIMP_TAC[ARITH_RULE `p <= i ==> p + i - p = i`]);;

let align_shift = prove
 (`!p (w:N word). align p w = word_shl (word_ushr w p) p`,
  REPEAT GEN_TAC THEN REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_ALIGN; BIT_WORD_SHL; BIT_WORD_USHR] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `p:num <= i` THEN ASM_SIMP_TAC[SUB_ADD]);;

let aligned_w2n = prove
 (`!k (w:N word). alignment_aligned k w <=> val w MOD 2 EXP k = 0`,
  REPEAT GEN_TAC THEN REWRITE_TAC[aligned_DEF; align_w2n] THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [GSYM WORD_VAL] THEN
  REWRITE_TAC[WORD_EQ; CONG] THEN
  SUBGOAL_THEN `val (w:N word) DIV 2 EXP k * 2 EXP k < 2 EXP dimindex(:N)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC LET_TRANS THEN EXISTS_TAC `val(w:N word)` THEN
    REWRITE_TAC[VAL_BOUND] THEN
    MP_TAC(SPECL [`val(w:N word)`; `2 EXP k`] DIVISION) THEN
    REWRITE_TAC[EXP_2_NE_0] THEN ARITH_TAC;
    ASM_SIMP_TAC[MOD_LT; VAL_BOUND]] THEN
  MP_TAC(SPECL [`val(w:N word)`; `2 EXP k`] DIVISION) THEN
  REWRITE_TAC[EXP_2_NE_0] THEN ARITH_TAC);;

let align_align_MAX = prove
 (`!k l (w:N word). align k (align l w) = align (MAX k l) w`,
  REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_ALIGN] THEN REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `bit i (w:N word)` THEN ASM_REWRITE_TAC[] THEN ARITH_TAC);;

let align_align = prove
 (`!p (w:N word). align p (align p w) = align p w`,
  REWRITE_TAC[align_align_MAX; ARITH_RULE `MAX p p = p`]);;

let aligned_align = prove
 (`!p (w:N word). alignment_aligned p (align p w)`,
  REWRITE_TAC[aligned_DEF; align_align]);;

let align_aligned = prove
 (`!p (w:N word). alignment_aligned p w ==> align p w = w`,
  REWRITE_TAC[aligned_DEF]);;

let aligned_0 = prove
 (`(!p. alignment_aligned p (word 0:N word)) /\
   (!w:N word. alignment_aligned 0 w)`,
  REWRITE_TAC[aligned_DEF; WORD_EQ_BITS_ALT; BIT_ALIGN; BIT_WORD_0; LE_0]);;

let aligned_extract = prove
 (`!p (w:N word).
     alignment_aligned p w <=> p = 0 \/ word_extract (p - 1) 0 w = word 0:N word`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[aligned_DEF; WORD_EQ_BITS_ALT; BIT_ALIGN; BIT_WORD_EXTRACT; BIT_WORD_0] THEN
  ASM_CASES_TAC `p = 0` THEN ASM_REWRITE_TAC[LE_0; ADD_CLAUSES] THEN
  EQ_TAC THEN REPEAT STRIP_TAC THENL
   [ASM_MESON_TAC[ARITH_RULE `~(p = 0) /\ i <= p - 1 ==> ~(p <= i)`];
    ASM_CASES_TAC `bit i (w:N word)` THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[] THEN
    ASM_ARITH_TAC]);;

let aligned_bitwise_and = prove
 (`!p (w:N word).
     alignment_aligned p w <=> word_and w (word (2 EXP p - 1)) = word 0`,
  REPEAT GEN_TAC THEN REWRITE_TAC[aligned_w2n; WORD_AND_MASK_WORD] THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD; VAL_WORD_0] THEN
  CONV_TAC SYM_CONV THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  MATCH_MP_TAC MOD_LT THEN MATCH_MP_TAC LET_TRANS THEN
  EXISTS_TAC `val(w:N word)` THEN REWRITE_TAC[MOD_LE; VAL_BOUND]);;

let MOD_0_aligned = prove
 (`!n p. n MOD 2 EXP p = 0 ==> alignment_aligned p (word n:N word)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[aligned_w2n; VAL_WORD; MOD_MOD_EXP_MIN] THEN
  UNDISCH_TAC `n MOD 2 EXP p = 0` THEN REWRITE_TAC[MOD_EQ_0] THEN
  DISCH_THEN(X_CHOOSE_THEN `q:num` SUBST1_TAC) THEN
  EXISTS_TAC `q * 2 EXP (p - MIN (dimindex(:N)) p)` THEN
  REWRITE_TAC[GSYM MULT_ASSOC; GSYM EXP_ADD] THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC);;

let aligned_lsl_leq = prove
 (`!k l (w:N word). k <= l ==> alignment_aligned k (word_shl w l)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[word_shl] THEN MATCH_MP_TAC MOD_0_aligned THEN
  REWRITE_TAC[MOD_EQ_0] THEN EXISTS_TAC `val(w:N word) * 2 EXP (l - k)` THEN
  REWRITE_TAC[GSYM MULT_ASSOC; GSYM EXP_ADD] THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN ASM_ARITH_TAC);;

(* the HOL4 lemma aligned_ge_dim: beyond the width only 0w is aligned *)

let aligned_ge_dim = prove
 (`!p (w:N word). dimindex(:N) <= p ==> (alignment_aligned p w <=> w = word 0)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[aligned_w2n; GSYM VAL_EQ_0] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC MOD_LT THEN
  TRANS_TAC LTE_TRANS `2 EXP dimindex(:N)` THEN
  ASM_REWRITE_TAC[VAL_BOUND; WORDSAUX_EXP2_LE]);;

(* below the width, alignment_aligned p is HOL Light's aligned (2 EXP p) *)

let aligned_hol_light = prove
 (`!p (w:N word).
     p <= dimindex(:N) ==> (alignment_aligned p w <=> aligned (2 EXP p) w)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[aligned_w2n; aligned] THEN
  SUBGOAL_THEN `2 EXP p divides 2 EXP dimindex(:N)` (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[divides] THEN EXISTS_TAC `2 EXP (dimindex(:N) - p)` THEN
    REWRITE_TAC[GSYM EXP_ADD] THEN AP_TERM_TAC THEN ASM_ARITH_TAC;
    SIMP_TAC[DIVIDES_MOD; EXP_2_NE_0]]);;

let aligned_add_sub = prove
 (`!p (a:N word) b.
     alignment_aligned p b ==>
     (alignment_aligned p (word_add a b) <=> alignment_aligned p a) /\
     (alignment_aligned p (word_sub a b) <=> alignment_aligned p a)`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `dimindex(:N) <= p` THENL
   [ASM_SIMP_TAC[aligned_ge_dim] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[WORD_ADD_0; WORD_SUB_0];
    RULE_ASSUM_TAC(REWRITE_RULE[NOT_LE]) THEN
    ASM_SIMP_TAC[aligned_hol_light; LT_IMP_LE] THEN
    MESON_TAC[ALIGNED_WORD_ADD_EQ; ALIGNED_WORD_SUB_EQ]]);;

let aligned_add_sub_cor = prove
 (`!p (a:N word) b.
     alignment_aligned p a /\ alignment_aligned p b ==>
     alignment_aligned p (word_add a b) /\ alignment_aligned p (word_sub a b)`,
  MESON_TAC[aligned_add_sub]);;

let byte_aligned_add = prove
 (`!x y:N word. byte_aligned x /\ byte_aligned y ==> byte_aligned (word_add x y)`,
  REWRITE_TAC[byte_aligned_DEF] THEN MESON_TAC[aligned_add_sub_cor]);;

let aligned_mul_shift_1 = prove
 (`!p (w:N word). alignment_aligned p (word_mul (word_shl (word 1) p) w)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[word_1_lsl] THEN
  ASM_CASES_TAC `p <= dimindex(:N)` THENL
   [ASM_SIMP_TAC[aligned_hol_light] THEN MATCH_MP_TAC ALIGNED_WORD_MUL THEN
    DISJ1_TAC THEN REWRITE_TAC[ALIGNED_WORD; NUMBER_RULE `n divides n`] THEN
    REWRITE_TAC[divides] THEN EXISTS_TAC `2 EXP (dimindex(:N) - p)` THEN
    REWRITE_TAC[GSYM EXP_ADD] THEN AP_TERM_TAC THEN ASM_ARITH_TAC;
    SUBGOAL_THEN `word (2 EXP p):N word = word 0` SUBST1_TAC THENL
     [ONCE_REWRITE_TAC[GSYM WORD_MOD_SIZE] THEN AP_TERM_TAC THEN
      REWRITE_TAC[MOD_0; MOD_EQ_0] THEN EXISTS_TAC `2 EXP (p - dimindex(:N))` THEN
      REWRITE_TAC[GSYM EXP_ADD] THEN AP_TERM_TAC THEN ASM_ARITH_TAC;
      REWRITE_TAC[WORD_MUL_0; aligned_0]]]);;

let aligned_pow2 = prove
 (`!k. alignment_aligned k (word (2 EXP k):N word)`,
  GEN_TAC THEN MATCH_MP_TAC MOD_0_aligned THEN REWRITE_TAC[MOD_REFL]);;

let aligned_add_pow = prove
 (`(!k (w:N word).
      alignment_aligned k (word_add w (word (2 EXP k))) <=> alignment_aligned k w) /\
   (!k n (w:N word).
      alignment_aligned k (word_add w (word (n * 2 EXP k))) <=> alignment_aligned k w)`,
  SUBGOAL_THEN `!k n. alignment_aligned k (word (n * 2 EXP k):N word)` ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN MATCH_MP_TAC MOD_0_aligned THEN REWRITE_TAC[MOD_EQ_0] THEN MESON_TAC[];
    ASM_SIMP_TAC[aligned_add_sub; aligned_pow2]]);;

let align_ls = prove
 (`!p (n:N word). word_ule (align p n) n`,
  REPEAT GEN_TAC THEN REWRITE_TAC[WORD_ULE; align_w2n; VAL_WORD] THEN
  MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `val(n:N word) DIV 2 EXP p * 2 EXP p` THEN
  REWRITE_TAC[MOD_LE] THEN
  MP_TAC(SPECL [`val(n:N word)`; `2 EXP p`] DIVISION) THEN
  REWRITE_TAC[EXP_2_NE_0] THEN ARITH_TAC);;

let VAL_ALIGN = prove
 (`!p (w:N word). val(align p w) = val w DIV 2 EXP p * 2 EXP p`,
  REPEAT GEN_TAC THEN REWRITE_TAC[align_w2n; VAL_WORD] THEN
  MATCH_MP_TAC MOD_LT THEN MATCH_MP_TAC LET_TRANS THEN
  EXISTS_TAC `val(w:N word)` THEN REWRITE_TAC[VAL_BOUND] THEN
  MP_TAC(SPECL [`val(w:N word)`; `2 EXP p`] DIVISION) THEN
  REWRITE_TAC[EXP_2_NE_0] THEN ARITH_TAC);;

let aligned_between = prove
 (`!p (n:N word) m.
     ~alignment_aligned p n /\ alignment_aligned p m /\ word_ult (align p n) m
     ==> word_ult n m`,
  REPEAT GEN_TAC THEN REWRITE_TAC[aligned_w2n; WORD_ULT; VAL_ALIGN] THEN
  REWRITE_TAC[MOD_EQ_0] THEN STRIP_TAC THEN REWRITE_TAC[GSYM NOT_LE] THEN
  DISCH_TAC THEN UNDISCH_TAC `val(n:N word) DIV 2 EXP p * 2 EXP p < val(m:N word)` THEN
  REWRITE_TAC[NOT_LT] THEN ASM_REWRITE_TAC[LE_MULT_RCANCEL] THEN DISJ1_TAC THEN
  ASM_SIMP_TAC[LE_RDIV_EQ; EXP_2_NE_0] THEN ASM_ARITH_TAC);;

let align_add_aligned = prove
 (`!p (a:N word) b.
     alignment_aligned p a /\ val b < 2 EXP p ==> align p (word_add a b) = a`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `dimindex(:N) <= p` THENL
   [ASM_SIMP_TAC[aligned_ge_dim] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[WORD_ADD_0; align_w2n] THEN
    ASM_SIMP_TAC[DIV_LT; MULT_CLAUSES];
    ALL_TAC] THEN
  REWRITE_TAC[aligned_w2n; MOD_EQ_0] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `q:num`) ASSUME_TAC) THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_ALIGN] THEN
  SUBGOAL_THEN `val(word_add a b:N word) = q * 2 EXP p + val(b:N word)` SUBST1_TAC THENL
   [REWRITE_TAC[VAL_WORD_ADD] THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOD_LT THEN
    SUBGOAL_THEN `2 EXP dimindex(:N) = 2 EXP (dimindex(:N) - p) * 2 EXP p` SUBST1_TAC THENL
     [REWRITE_TAC[GSYM EXP_ADD] THEN AP_TERM_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `q < 2 EXP (dimindex(:N) - p)` MP_TAC THENL
     [MP_TAC(SPECL [`q:num`; `2 EXP (dimindex(:N) - p)`; `2 EXP p`] LT_MULT_RCANCEL) THEN
      REWRITE_TAC[EXP_2_NE_0; GSYM EXP_ADD] THEN
      SUBGOAL_THEN `(dimindex(:N) - p) + p = dimindex(:N)` SUBST1_TAC THENL
       [ASM_ARITH_TAC; DISCH_THEN(SUBST1_TAC o SYM)] THEN
      UNDISCH_TAC `val (a:N word) = q * 2 EXP p` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[VAL_BOUND];
      DISCH_THEN(X_CHOOSE_THEN `d:num` SUBST1_TAC o GEN_REWRITE_RULE I [LT_EXISTS]) THEN
      REWRITE_TAC[RIGHT_ADD_DISTRIB; MULT_CLAUSES] THEN ASM_ARITH_TAC];
    ASM_SIMP_TAC[DIV_MULT_ADD; EXP_2_NE_0; DIV_LT; ADD_CLAUSES]]);;

let align_add_aligned_gen = prove
 (`!p (a:N word) b.
     alignment_aligned p a ==> align p (word_add a b) = word_add a (align p b)`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `c:N word = word_add a (word (val(b:N word) DIV 2 EXP p * 2 EXP p))` THEN
  SUBGOAL_THEN `word_add a b:N word = word_add c (word (val(b:N word) MOD 2 EXP p))`
  SUBST1_TAC THENL
   [EXPAND_TAC "c" THEN REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
    AP_TERM_TAC THEN GEN_REWRITE_TAC LAND_CONV [GSYM WORD_VAL] THEN AP_TERM_TAC THEN
    MP_TAC(SPECL [`val(b:N word)`; `2 EXP p`] DIVISION) THEN
    REWRITE_TAC[EXP_2_NE_0] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `align p (word_add c (word (val(b:N word) MOD 2 EXP p))):N word = c`
  SUBST1_TAC THENL
   [MATCH_MP_TAC align_add_aligned THEN CONJ_TAC THENL
     [EXPAND_TAC "c" THEN MATCH_MP_TAC(MESON[aligned_add_sub_cor]
       `!p (a:N word) b. alignment_aligned p a /\ alignment_aligned p b
                         ==> alignment_aligned p (word_add a b)`) THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOD_0_aligned THEN REWRITE_TAC[MOD_EQ_0] THEN MESON_TAC[];
      REWRITE_TAC[VAL_WORD] THEN MATCH_MP_TAC LET_TRANS THEN
      EXISTS_TAC `val(b:N word) MOD 2 EXP p` THEN
      REWRITE_TAC[MOD_LE; MOD_LT_EQ; EXP_2_NE_0]];
    EXPAND_TAC "c" THEN REWRITE_TAC[align_w2n]]);;

(* ------------------------------------------------------------------------- *)
(* words: the HOL4 [simp] theorems of wordsScript (HOL4's srw_ss uses them;  *)
(* registered in the project simpset at the end of this file).               *)
(* ------------------------------------------------------------------------- *)

let ZERO_LT_INT_MIN = prove
 (`0 < INT_MIN(:N)`,
  REWRITE_TAC[INT_MIN_def; ZERO_LT_TWOEXP]);;

let ZERO_LT_UINT_MAX = prove
 (`0 < UINT_MAX(:N)`,
  REWRITE_TAC[UINT_MAX_def] THEN MP_TAC ONE_LT_dimword THEN ARITH_TAC);;

let w2n_eq_0 = prove
 (`!w:N word. val w = 0 <=> w = word 0`,
  REWRITE_TAC[VAL_EQ_0]);;

let FCP_T_F = prove
 (`word_of_bits (K T) = word_UINT_MAX:N word /\ word_of_bits (K F) = word 0:N word`,
  REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_OF_BITS; IN; K_THM; BIT_WORD_0] THEN
  REWRITE_TAC[word_UINT_MAX; BIT_WORD; GSYM numbit; BIT_EXP_SUB1]);;

let WORD_NOT_XOR = prove
 (`!a b:N word.
     word_xor (word_not a) (word_not b) = word_xor a b /\
     word_xor a (word_not b) = word_not (word_xor a b) /\
     word_xor (word_not a) b = word_not (word_xor a b)`,
  REPEAT GEN_TAC THEN REPEAT CONJ_TAC THEN WORD_BITWISE_TAC);;

let WORD_AND_ABSORD = prove
 (`!a b:N word. word_or a (word_and a b) = a`,
  WORD_BITWISE_TAC);;

let WORD_AND_COMP = prove
 (`!a:N word. word_and a (word_not a) = word 0`,
  WORD_BITWISE_TAC);;

let w2w_id = WORD_ZX_TRIVIAL;;

let sw2sw_id = WORD_SX_TRIVIAL;;

let WORD_SUB_RZERO = WORD_SUB_0;;

let WORD_LCANCEL_SUB = prove
 (`!v w x:N word. word_sub v w = word_sub x w <=> v = x`,
  MESON_TAC[WORD_RULE `!v w:N word. word_add (word_sub v w) w = v`]);;

let WORD_RCANCEL_SUB = prove
 (`!v w x:N word. word_sub v w = word_sub v x <=> w = x`,
  MESON_TAC[WORD_RULE `!v w:N word. word_sub v (word_sub v w) = w`]);;

let WORD_ADD_LID_UNIQ = prove
 (`!v w:N word. word_add v w = w <=> v = word 0`,
  REWRITE_TAC[WORD_ADD_EQ_SUB; WORD_SUB_REFL]);;

let WORD_ADD_RID_UNIQ = prove
 (`!v w:N word. word_add v w = v <=> w = word 0`,
  REWRITE_TAC[WORD_ADD_INV_0_EQ]);;

let WORD_NEG1_MUL_LCANCEL = prove
 (`!v w:N word.
     word_mul (word_neg (word 1)) v = word_mul (word_neg (word 1)) w <=> v = w`,
  REWRITE_TAC[GSYM WORD_NEG_MUL; WORD_EQ_NEG]);;

let WORD_NEG1_MUL_RCANCEL = prove
 (`!v w:N word.
     word_mul v (word_neg (word 1)) = word_mul w (word_neg (word 1)) <=> v = w`,
  ONCE_REWRITE_TAC[WORD_MUL_SYM] THEN REWRITE_TAC[WORD_NEG1_MUL_LCANCEL]);;

let WORD_LESS_EQ_REFL = prove
 (`!a:N word. word_ile a a`,
  REWRITE_TAC[WORD_ILE; INT_LE_REFL]);;

let WORD_LOWER_EQ_REFL = prove
 (`!a:N word. word_ule a a`,
  REWRITE_TAC[WORD_ULE; LE_REFL]);;

let WORD_LS_word_0 = prove
 (`!n:N word. word_ule n (word 0) <=> n = word 0`,
  REWRITE_TAC[WORD_ULE; VAL_WORD_0; GSYM VAL_EQ_0] THEN ARITH_TAC);;

let WORD_LO_word_0R = CONJUNCT2 WORD_LO_word_0;;

let word_T_not_zero = prove
 (`~(word_neg (word 1):N word = word 0)`,
  REWRITE_TAC[WORD_NEG_EQ_0; GSYM VAL_EQ_0; VAL_WORD_1; ARITH_EQ]);;

let WORD_LS_word_T = prove
 (`(!n:N word. word_ule (word_neg (word 1)) n <=> n = word_neg (word 1)) /\
   (!n:N word. word_ule n (word_neg (word 1)))`,
  REWRITE_TAC[WORD_ULE; GSYM VAL_EQ; VAL_WORD_NEG_1] THEN
  CONJ_TAC THEN GEN_TAC THEN MP_TAC(ISPEC `n:N word` VAL_BOUND) THEN ARITH_TAC);;

let WORD_LO_word_T_L = CONJUNCT1 WORD_LO_word_T;;

let WORD_LO_word_T_R = prove
 (`!n:N word. ~(word_ult n (word_neg (word 1))) <=> n = word_neg (word 1)`,
  REWRITE_TAC[WORD_LO_word_T] THEN MESON_TAC[]);;

let WORD_LESS_0_word_T = prove
 (`~(word_ilt (word 0) (word_neg (word 1):N word)) /\
   ~(word_ile (word 0) (word_neg (word 1):N word)) /\
   word_ilt (word_neg (word 1)) (word 0:N word) /\
   word_ile (word_neg (word 1)) (word 0:N word)`,
  REWRITE_TAC[WORD_ILT; WORD_ILE; IVAL_WORD_0; IVAL_WORD_NEG_1] THEN INT_ARITH_TAC);;

(* HOL4's SIZES_ss (in srw_ss with wordsLib) evaluates dimindex, dimword,  *)
(* INT_MIN, INT_MAX and UINT_MAX of numeral types: here as rewrites over   *)
(* the binary numeral types (registered in the simpset below).             *)

let SIZES_DIMWORD = prove
 (`dimword(:1) = 2 /\
   dimword(:(A)tybit0) = dimword(:A) * dimword(:A) /\
   dimword(:(A)tybit1) = 2 * dimword(:A) * dimword(:A)`,
  REWRITE_TAC[dimword_def; DIMINDEX_1; DIMINDEX_TYBIT0; DIMINDEX_TYBIT1] THEN
  REWRITE_TAC[ARITH_RULE `2 * d = d + d`; EXP_ADD; EXP_1] THEN CONV_TAC NUM_RING);;

let SIZES_INT_MIN = prove
 (`INT_MIN(:1) = 1 /\
   INT_MIN(:(A)tybit0) = dimword(:(A)tybit0) DIV 2 /\
   INT_MIN(:(A)tybit1) = dimword(:(A)tybit1) DIV 2`,
  REWRITE_TAC[dimword_IS_TWICE_INT_MIN; ARITH_RULE `(2 * n) DIV 2 = n`] THEN
  REWRITE_TAC[INT_MIN_def; DIMINDEX_1] THEN CONV_TAC NUM_REDUCE_CONV);;

let SIZES_THMS = prove
 (`dimindex(:1) = 1 /\
   dimindex(:(A)tybit0) = 2 * dimindex(:A) /\
   dimindex(:(A)tybit1) = 2 * dimindex(:A) + 1 /\
   dimword(:1) = 2 /\
   dimword(:(A)tybit0) = dimword(:A) * dimword(:A) /\
   dimword(:(A)tybit1) = 2 * dimword(:A) * dimword(:A) /\
   INT_MIN(:1) = 1 /\
   INT_MIN(:(A)tybit0) = dimword(:(A)tybit0) DIV 2 /\
   INT_MIN(:(A)tybit1) = dimword(:(A)tybit1) DIV 2 /\
   INT_MAX(:1) = 0 /\
   INT_MAX(:(A)tybit0) = INT_MIN(:(A)tybit0) - 1 /\
   INT_MAX(:(A)tybit1) = INT_MIN(:(A)tybit1) - 1 /\
   UINT_MAX(:1) = 1 /\
   UINT_MAX(:(A)tybit0) = dimword(:(A)tybit0) - 1 /\
   UINT_MAX(:(A)tybit1) = dimword(:(A)tybit1) - 1`,
  REWRITE_TAC[DIMINDEX_1; DIMINDEX_TYBIT0; DIMINDEX_TYBIT1; SIZES_DIMWORD;
              SIZES_INT_MIN; INT_MAX_def; UINT_MAX_def] THEN
  CONV_TAC NUM_REDUCE_CONV);;

(* HOL4 nzcv (the flags of a - b), used by word_lo_def and word_lt_def *)

let nzcv_DEF = new_definition
  `nzcv (a:N word) (b:N word) =
     let q = val a + val (word_neg b) in
     let r = word q:N word in
     (word_msb r, (r = word 0), (numbit (dimindex(:N)) q \/ b = word 0),
      (~(word_msb a <=> word_msb b) /\ ~(word_msb r <=> word_msb a)))`;;

let word_lo_def = prove
 (`!a b:N word. word_ult a b <=> let (n,z,c,v) = nzcv a b in ~c`,
  REPEAT GEN_TAC THEN REWRITE_TAC[nzcv_DEF] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[WORD_ULT] THEN
  ASM_CASES_TAC `b:N word = word 0` THEN ASM_REWRITE_TAC[VAL_WORD_0; LT] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM VAL_EQ_0]) THEN
  ASM_REWRITE_TAC[VAL_WORD_NEG_CASES; numbit] THEN
  MP_TAC(ISPEC `a:N word` VAL_BOUND) THEN MP_TAC(ISPEC `b:N word` VAL_BOUND) THEN
  REPEAT DISCH_TAC THEN ASM_CASES_TAC `val(b:N word) <= val(a:N word)` THENL
   [SUBGOAL_THEN `(val(a:N word) + 2 EXP dimindex(:N) - val(b:N word)) DIV
                  2 EXP dimindex(:N) = 1` SUBST1_TAC THENL
     [MATCH_MP_TAC DIV_UNIQ THEN EXISTS_TAC `val(a:N word) - val(b:N word)` THEN
      ASM_ARITH_TAC;
      REWRITE_TAC[ARITH] THEN ASM_ARITH_TAC];
    SUBGOAL_THEN `(val(a:N word) + 2 EXP dimindex(:N) - val(b:N word)) DIV
                  2 EXP dimindex(:N) = 0` SUBST1_TAC THENL
     [MATCH_MP_TAC DIV_LT THEN ASM_ARITH_TAC;
      REWRITE_TAC[ARITH] THEN ASM_ARITH_TAC]]);;

let word_lt_def = prove
 (`!a b:N word. word_ilt a b <=> let (n,z,c,v) = nzcv a b in ~(n <=> v)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[nzcv_DEF] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[] THEN
  SUBGOAL_THEN `word (val(a:N word) + val(word_neg b:N word)):N word = word_sub a b`
  SUBST1_TAC THENL
   [REWRITE_TAC[WORD_ADD; WORD_VAL; word_sub_def]; ALL_TAC] THEN
  REWRITE_TAC[word_msb_def] THEN WORD_ARITH_TAC);;

(* LOG2_CONV evaluates LOG2 of a positive numeral, e.g. |- LOG2 8 = 3     *)

let LOG2_CONV tm =
  match tm with
    Comb(Const("LOG2",_),n) when is_numeral n ->
      let v = dest_numeral n in
      if v =/ Num.num_of_int 0 then failwith "LOG2_CONV" else
      let rec find k =
        if power_num (Num.num_of_int 2) (Num.num_of_int (k + 1)) >/ v then k
        else find (k + 1) in
      let th = SPECL [n; mk_small_numeral (find 0)] LOG2_UNIQUE in
      MP th (EQT_ELIM(NUM_REDUCE_CONV(lhand(concl th))))
  | _ -> failwith "LOG2_CONV";;

(* ------------------------------------------------------------------------- *)
(* The HOL4 [simp] theorems of these theories, for the project simpset.      *)
(* ------------------------------------------------------------------------- *)

let _ = cake_add_simps
 [SIZES_THMS; DIMINDEX_GT_0;
  ZERO_LT_dimword; ONE_LT_dimword; ZERO_LT_INT_MIN; ZERO_LT_UINT_MAX;
  w2n_n2w; n2w_w2n; n2w_11; w2n_11; w2n_eq_0; VAL_WORD_0; FCP_T_F;
  WORD_NOT_NOT; WORD_NOT_XOR; WORD_AND_ABSORD; WORD_AND_COMP; w2w_id; sw2sw_id;
  WORD_EQ_ADD_LCANCEL; WORD_EQ_ADD_RCANCEL; WORD_NEG_NEG; WORD_LCANCEL_SUB;
  WORD_RCANCEL_SUB; WORD_SUB_RZERO; WORD_ADD_LID_UNIQ; WORD_ADD_RID_UNIQ;
  WORD_EQ_NEG; WORD_NEG_EQ_0; WORD_NEG1_MUL_LCANCEL; WORD_NEG1_MUL_RCANCEL;
  WORD_LESS_EQ_REFL; WORD_LESS_REFL; WORD_LOWER_EQ_REFL; WORD_LOWER_REFL;
  WORD_LS_word_0; WORD_LO_word_0R; word_T_not_zero; WORD_LS_word_T;
  WORD_LO_word_T_L; WORD_LO_word_T_R; WORD_LESS_0_word_T; WORD_FINITE;
  ZERO_LT_TWOEXP; aligned_add_pow; i2w_w2n_w2w;
  integer_NUM_OF_INT; INT_OF_NUM; INT_ABS_NUM; INT_ABS_EQ_ID; integer_INT_LT;
  INT_EQ_NEG];;

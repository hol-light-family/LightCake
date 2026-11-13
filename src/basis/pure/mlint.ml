(* ========================================================================= *)
(* mlint: port of HOL4 basis/pure/mlintScript.sml (CakeML v3479).            *)
(* Pure functions for the Int module.                                        *)
(*                                                                           *)
(* Notes on the rendering:                                                   *)
(* - HOL4 character literals are CHR n (hol4/string4.ml): #"0" is CHR 48,    *)
(*   #"A" CHR 65, #"~" CHR 126, #"-" CHR 45, #"+" CHR 43; HOL4 strlit is    *)
(*   implode, STRLEN is LENGTH, STRCAT is APPEND, STRING is CONS, EVERY is  *)
(*   ALL.                                                                    *)
(* - Integers: HOL4 Num is num_of_int (only used on non-negative values),    *)
(*   ABS is abs, ~&n is --(&n); HOL4 gcd a b is num_gcd(a,b).                *)
(* - HOL4 Overload toString = num_to_str: written num_to_str; on num with a  *)
(*   string result, HOL4 toString (ASCIInumbers) is num_to_dec_string.       *)
(* - Names (notes/naming/names.tsv): HOL4 fromString, int_cmp, num_gcd and   *)
(*   int_gcd are mlint_fromString, mlint_int_cmp, mlint_num_gcd and         *)
(*   mlint_int_gcd.  Helper lemmas that are not HOL4 theorems are PURE2AUX_. *)
(* - The free variables of a HOL4 statement are universally quantified.      *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "basis/pure/mlstring.ml";;
needs "hol4/gcd.ml";;
needs "hol4/ASCIInumbers.ml";;

type_invention_error := true;;

let toChar_def = cake_def
  `toChar digit =
     if digit < 10 then CHR (ORD (CHR 48) + digit)
     else CHR ((ORD (CHR 65) + digit) - 10)`;;

let toChar_HEX = prove
 (`!d. d < 16 ==> toChar d = HEX d`,
  GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[toChar_def; HEX] THEN
  ASM_REWRITE_TAC[] THEN
  SIMP_TAC[ORD_CHR_RWT; ARITH_RULE `48 < 256 /\ 65 < 256`] THEN
  COND_CASES_TAC THEN REWRITE_TAC[] THEN AP_TERM_TAC THEN ASM_ARITH_TAC);;

(* decimal encoding is very slightly faster if we avoid dividing large     *)
(* big-ints by 10, and instead divide them by a power of 10 that fits in   *)
(* 28 bits                                                                 *)

let exp_for_dec_enc_def = cake_def
  `exp_for_dec_enc = 8`;;

(* compatibility with previous version *)

let padLen_DEC_def = cake_def
  `padLen_DEC = exp_for_dec_enc`;;

(* HOL4: Theorem padLen_DEC_eq = EVAL of padLen_DEC *)

let padLen_DEC_eq = prove
 (`padLen_DEC = 8`,
  REWRITE_TAC[padLen_DEC_def; exp_for_dec_enc_def]);;

let maxSmall_DEC_def1 = cake_def
  `maxSmall_DEC = 10 EXP exp_for_dec_enc`;;

(* HOL4: Theorem maxSmall_DEC_def = EVAL of maxSmall_DEC *)

let maxSmall_DEC_def = prove
 (`maxSmall_DEC = 100000000`,
  REWRITE_TAC[maxSmall_DEC_def1; exp_for_dec_enc_def] THEN
  CONV_TAC NUM_REDUCE_CONV);;

(* HOL4 writes ^exp_tm for 100000000, the value of 10 ** exp_for_dec_enc.  *)
(* Termination: in the first clause the first component of the measure    *)
(* stays the same and the second one decreases, in the second clause the  *)
(* first one decreases (PURE2AUX_NUM_TO_CHARS_DEC).                        *)

let PURE2AUX_NUM_TO_CHARS_DEC = prove
 (`!i j k. ~(k < 10 /\ i = 0) ==> i * 10 EXP j + k DIV 10 < i * 10 EXP SUC j + k`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `(i = 0 <=> i * 10 EXP j = 0)` ASSUME_TAC THENL
   [REWRITE_TAC[MULT_EQ_0; EXP_EQ_0] THEN ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[EXP; ARITH_RULE `i * 10 * n = 10 * i * n`] THEN
  MP_TAC(SPECL [`k:num`; `10`] DIVISION) THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_ARITH_TAC);;

let num_to_chars_def = cake_def_wf
  `inv_image (measure (I:num->num) LEX measure (I:num->num))
     (\p:num#num#num#string. (FST p * 10 EXP FST (SND p) + FST (SND (SND p)),
                              exp_for_dec_enc - FST (SND p)))`
  (REWRITE_TAC[inv_image_THM; I_THM; FST; SND; exp_for_dec_enc_def] THEN
   REWRITE_TAC[LEX_THM; measure_THM; I_THM] THEN REPEAT GEN_TAC THEN
   ((MP_TAC(SPECL [`i:num`; `100000000`] DIVISION) THEN
     CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC) ORELSE
    (DISCH_TAC THEN REPEAT GEN_TAC THEN
     MP_TAC(SPECL [`i:num`; `j:num`; `k:num`] PURE2AUX_NUM_TO_CHARS_DEC) THEN
     ASM_REWRITE_TAC[] THEN ARITH_TAC)))
  `(num_to_chars i 0 k (acc:string) =
      num_to_chars (i DIV 100000000) exp_for_dec_enc ((i MOD 100000000) + k) acc) /\
   (num_to_chars i (SUC j) k acc =
      if k < 10 /\ i = 0 then CONS (toChar k) acc
      else num_to_chars i j (k DIV 10) (CONS (toChar (k MOD 10)) acc))`;;

let num_to_chars_ind = cake_ind "num_to_chars";;

let add_lt_divisible_iff = prove
 (`!y n x. y MOD n = 0 ==> (x + y < n <=> x < n /\ y = 0)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN EQ_TAC THENL
   [DISCH_TAC THEN SUBGOAL_THEN `y < n:num` ASSUME_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `y = 0` SUBST_ALL_TAC THENL
     [ASM_MESON_TAC[MOD_LT]; ASM_ARITH_TAC];
    ARITH_TAC]);;

(* the decimal digits of n, the last one split off *)

let PURE2AUX_DEC_STRING_DIGIT = prove
 (`!n. n < 10 ==> num_to_dec_string n = [HEX n]`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[num_to_dec_string_def; n2s_def] THEN
  ONCE_REWRITE_TAC[n2l_def] THEN ASM_SIMP_TAC[MOD_LT; MAP; REVERSE; APPEND]);;

let PURE2AUX_DEC_STRING_STEP = prove
 (`!n. 10 <= n ==>
       num_to_dec_string n = APPEND (num_to_dec_string (n DIV 10)) [HEX (n MOD 10)]`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[num_to_dec_string_def; n2s_def] THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o RAND_CONV) [n2l_def] THEN
  ASM_SIMP_TAC[ARITH_RULE `10 <= n ==> ~(n < 10 \/ 10 < 2)`; MAP; REVERSE]);;

let num_to_chars_thm = prove
 (`!i j k acc.
     num_to_chars i j k acc = APPEND (num_to_dec_string (k + i * 10 EXP j)) acc`,
  MATCH_MP_TAC num_to_chars_ind THEN CONJ_TAC THEN REPEAT GEN_TAC THEN
  DISCH_TAC THEN ONCE_REWRITE_TAC[num_to_chars_def] THENL
   [ASM_REWRITE_TAC[] THEN AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[exp_for_dec_enc_def] THEN
    MP_TAC(SPECL [`i:num`; `100000000`] DIVISION) THEN
    CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC;
    ALL_TAC] THEN
  COND_CASES_TAC THENL
   [FIRST_X_ASSUM(CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC) THEN
    REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES] THEN
    ASM_SIMP_TAC[PURE2AUX_DEC_STRING_DIGIT; toChar_HEX; APPEND;
                 ARITH_RULE `k < 10 ==> k < 16`];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[EXP; ARITH_RULE `k + i * 10 * m = (i * m) * 10 + k`] THEN
  SUBGOAL_THEN `10 <= (i * 10 EXP j) * 10 + k` ASSUME_TAC THENL
   [ASM_CASES_TAC `i = 0` THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `~(i * 10 EXP j = 0)` MP_TAC THENL
     [ASM_REWRITE_TAC[MULT_EQ_0; EXP_EQ_0] THEN ARITH_TAC; ARITH_TAC];
    ALL_TAC] THEN
  ASM_SIMP_TAC[PURE2AUX_DEC_STRING_STEP] THEN
  SUBGOAL_THEN `((i * 10 EXP j) * 10 + k) DIV 10 = k DIV 10 + i * 10 EXP j /\
                ((i * 10 EXP j) * 10 + k) MOD 10 = k MOD 10`
   (CONJUNCTS_THEN SUBST1_TAC) THENL
   [SIMP_TAC[DIV_MULT_ADD; MOD_MULT_ADD; ARITH_EQ] THEN ARITH_TAC;
    ALL_TAC] THEN
  SIMP_TAC[GSYM APPEND_ASSOC; APPEND; toChar_HEX; MOD_LT_EQ;
           ARITH_RULE `k MOD 10 < 10 ==> k MOD 10 < 16`; ARITH_EQ]);;

let int_to_string_def = cake_def
  `int_to_string (neg_char:char) (i:int) =
     if &0 <= i then implode (num_to_chars (num_of_int i) 0 0 [])
     else implode (CONS neg_char (num_to_chars (num_of_int (abs i)) 0 0 []))`;;

let toString_def1 = cake_def
  `toString (i:int) = int_to_string (CHR 126) i`;;

(* HOL4: toString_def1 |> REWRITE_RULE [int_to_string_def] *)

let toString_def = REWRITE_RULE[int_to_string_def] toString_def1;;

let int_to_string_thm = prove
 (`!neg_char i.
     int_to_string neg_char i =
     implode (APPEND (if i < &0 then [neg_char] else [])
                     (num_to_dec_string (num_of_int (abs i))))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[int_to_string_def; num_to_chars_thm; EXP; MULT_CLAUSES;
              ADD_CLAUSES; APPEND_NIL] THEN
  COND_CASES_TAC THEN
  ASM_SIMP_TAC[INT_ARITH `!i:int. &0 <= i ==> ~(i < &0)`;
               INT_ARITH `!i:int. &0 <= i ==> abs i = i`;
               INT_ARITH `!i:int. ~(&0 <= i) ==> i < &0`; APPEND]);;

let toString_thm = prove
 (`!i. toString i =
       implode (APPEND (if i < &0 then "~" else "")
                       (num_to_dec_string (num_of_int (abs i))))`,
  GEN_TAC THEN REWRITE_TAC[toString_def1; int_to_string_thm] THEN
  COND_CASES_TAC THEN REWRITE_TAC[] THEN
  AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[CONS_11; CHR_DEF] THEN CONV_TAC NUM_REDUCE_CONV);;

let num_to_str_def = cake_def
  `num_to_str (n:num) = toString (&n)`;;

(* HOL4: Overload toString = num_to_str (written num_to_str here) *)

let num_to_str_thm = prove
 (`!n. num_to_str n = implode (num_to_dec_string n)`,
  REWRITE_TAC[num_to_str_def; toString_thm; INT_ABS_NUM; NUM_OF_INT_OF_NUM;
              INT_OF_NUM_LT; LT; APPEND]);;

let fromChar_unsafe_def = cake_def
  `fromChar_unsafe char = ORD char - ORD (CHR 48)`;;

let fromChar_def = cake_def
  `fromChar char =
     match char with
       CHR 48 -> SOME 0
     | CHR 49 -> SOME 1
     | CHR 50 -> SOME 2
     | CHR 51 -> SOME 3
     | CHR 52 -> SOME 4
     | CHR 53 -> SOME 5
     | CHR 54 -> SOME 6
     | CHR 55 -> SOME 7
     | CHR 56 -> SOME 8
     | CHR 57 -> SOME 9
     | _ -> NONE`;;

let fromChar_eq_unsafe = prove
 (`!char. isDigit char ==> fromChar char = SOME (fromChar_unsafe char)`,
  GEN_TAC THEN REWRITE_TAC[isDigit_def] THEN
  MP_TAC(SPEC `char:char` CHR_ORD) THEN SPEC_TAC(`ORD char`,`n:num`) THEN
  GEN_TAC THEN DISCH_THEN(SUBST1_TAC o SYM) THEN DISCH_TAC THEN
  SUBGOAL_THEN `n = 48 \/ n = 49 \/ n = 50 \/ n = 51 \/ n = 52 \/ n = 53 \/
                n = 54 \/ n = 55 \/ n = 56 \/ n = 57` MP_TAC THENL
   [ASM_ARITH_TAC; DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC)] THEN
  SIMP_TAC[fromChar_def; fromChar_unsafe_def; CHR_11; ORD_CHR_RWT; ARITH]);;

let fromChars_range_unsafe_def = cake_def
  `(fromChars_range_unsafe l 0 (str:mlstring) = 0) /\
   (fromChars_range_unsafe l (SUC n) str =
      fromChars_range_unsafe l n str * 10 + fromChar_unsafe (strsub str (l + n)))`;;

let fromChars_range_def = cake_def
  `(fromChars_range l 0 (str:mlstring) = SOME 0) /\
   (fromChars_range l (SUC n) str =
      let rest = OPTION_MAP ((*) 10) (fromChars_range l n str)
      and head = fromChar (strsub str (l + n)) in
      OPTION_MAP2 (+) rest head)`;;

let fromChars_range_eq_unsafe = prove
 (`!str l r. ALL isDigit str /\ l + r <= LENGTH str ==>
     fromChars_range l r (implode str) =
     SOME (fromChars_range_unsafe l r (implode str))`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
  REWRITE_TAC[fromChars_range_def; fromChars_range_unsafe_def] THEN
  STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  SUBGOAL_THEN `isDigit (EL (l + r) (str:string))` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [EVERY_EL]) THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[LET_DEF; LET_END_DEF; OPTION_MAP_DEF; strsub_def;
               fromChar_eq_unsafe; OPTION_MAP2_THM] THEN
  REWRITE_TAC[MULT_SYM]);;

let fromChars_unsafe_def = cake_def_wf
  `measure (FST:num#mlstring->num)`
  (REWRITE_TAC(WF_REL_THMS @ [FST; SND; padLen_DEC_eq]) THEN
   REPEAT STRIP_TAC THEN ASM_ARITH_TAC)
  `(fromChars_unsafe 0 (str:mlstring) = 0) /\
   (fromChars_unsafe n str =
      if n <= padLen_DEC then fromChars_range_unsafe 0 n str
      else let n' = n - padLen_DEC in
           let front = fromChars_unsafe n' str * maxSmall_DEC in
           let back = fromChars_range_unsafe n' padLen_DEC str in
           front + back)`;;

let fromChars_unsafe_ind = cake_ind "fromChars_unsafe";;

let fromChars_def = cake_def_wf
  `measure (FST:num#mlstring->num)`
  (REWRITE_TAC(WF_REL_THMS @ [FST; SND; padLen_DEC_eq]) THEN
   REPEAT STRIP_TAC THEN ASM_ARITH_TAC)
  `(fromChars 0 (str:mlstring) = NONE) /\
   (fromChars n str =
      if n <= padLen_DEC then fromChars_range 0 n str
      else let n' = n - padLen_DEC in
           let front = OPTION_MAP ((*) maxSmall_DEC) (fromChars n' str) in
           let back = fromChars_range n' padLen_DEC str in
           OPTION_MAP2 (+) front back)`;;

let fromChars_ind = cake_ind "fromChars";;

let fromChars_eq_unsafe = prove
 (`!n s. ALL isDigit (explode s) /\ n <= strlen s /\ n >= 1 ==>
         fromChars n s = SOME (fromChars_unsafe n s)`,
  MATCH_MP_TAC fromChars_ind THEN CONJ_TAC THENL
   [ARITH_TAC; ALL_TAC] THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN STRIP_TAC THEN
  ONCE_REWRITE_TAC[fromChars_def; fromChars_unsafe_def] THEN
  CASES_ON `str:mlstring` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[explode_thm; strlen_def]) THEN
  REWRITE_TAC[strlen_def] THEN COND_CASES_TAC THEN REWRITE_TAC[] THENL
   [MATCH_MP_TAC fromChars_range_eq_unsafe THEN ASM_REWRITE_TAC[ADD_CLAUSES];
    ALL_TAC] THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[padLen_DEC_eq]) THEN
    REWRITE_TAC[padLen_DEC_eq] THEN ASM_ARITH_TAC;
    DISCH_THEN SUBST1_TAC] THEN
  SUBGOAL_THEN
   `fromChars_range (SUC v2 - padLen_DEC) padLen_DEC (implode a) =
    SOME (fromChars_range_unsafe (SUC v2 - padLen_DEC) padLen_DEC (implode a))`
  SUBST1_TAC THENL
   [MATCH_MP_TAC fromChars_range_eq_unsafe THEN
    RULE_ASSUM_TAC(REWRITE_RULE[padLen_DEC_eq]) THEN
    ASM_REWRITE_TAC[padLen_DEC_eq] THEN ASM_ARITH_TAC;
    REWRITE_TAC[OPTION_MAP_DEF; OPTION_MAP2_THM; MULT_SYM]]);;

let fromString_unsafe_def = cake_def
  `fromString_unsafe str =
     if strlen str = 0 then (&0:int)
     else if strsub str 0 = CHR 126
     then --(&(fromChars_unsafe (strlen str - 1)
                                (substring str 1 (strlen str - 1))))
     else &(fromChars_unsafe (strlen str) str)`;;

(* HOL4: fromString_def; HOL4 $~ o $& is int_neg o int_of_num *)

let mlint_fromString_def = cake_def
  `mlint_fromString str =
     if strlen str = 0 then (NONE:int option)
     else if strsub str 0 = CHR 126 \/ strsub str 0 = CHR 45
     then OPTION_MAP (int_neg o int_of_num)
            (fromChars (strlen str - 1) (substring str 1 (strlen str - 1)))
     else if strsub str 0 = CHR 43
     then OPTION_MAP int_of_num
            (fromChars (strlen str - 1) (substring str 1 (strlen str - 1)))
     else OPTION_MAP int_of_num (fromChars (strlen str) str)`;;

let fromNatString_def = cake_def
  `fromNatString str =
     match mlint_fromString str with
       NONE -> NONE
     | SOME i -> if &0 <= i then SOME (num_of_int i) else NONE`;;

(* fromString auxiliar lemmas *)

let fromChars_range_unsafe_0_substring_thm = prove
 (`!m r s. r <= m ==>
     fromChars_range_unsafe 0 r s = fromChars_range_unsafe 0 r (substring s 0 m)`,
  GEN_TAC THEN INDUCT_TAC THEN REWRITE_TAC[fromChars_range_unsafe_def] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `s:mlstring`) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[ADD_CLAUSES] THEN
  ASM_SIMP_TAC[strsub_substring_0_thm; ARITH_RULE `SUC r <= m ==> r < m`]);;

let fromChars_range_unsafe_split = prove
 (`!m n s. ~(m = 0) /\ m < n ==>
     fromChars_range_unsafe 0 n s =
     10 EXP m * fromChars_range_unsafe 0 (n - m) s +
     fromChars_range_unsafe (n - m) m s`,
  INDUCT_TAC THEN REWRITE_TAC[] THEN INDUCT_TAC THEN
  REWRITE_TAC[CONJUNCT1 LT; LT_SUC] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[fromChars_range_unsafe_def; SUB_SUC] THEN
  ASM_CASES_TAC `m = 0` THENL
   [ASM_REWRITE_TAC[fromChars_range_unsafe_def; SUB_0; EXP; MULT_CLAUSES;
                    ADD_CLAUSES] THEN ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`n:num`; `s:mlstring`]) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  SUBGOAL_THEN `(n - m) + m = n` SUBST1_TAC THENL
   [ASM_ARITH_TAC; REWRITE_TAC[EXP; ADD_CLAUSES] THEN CONV_TAC NUM_RING]);;

(* fromString proofs *)

let fromChar_unsafe_thm = prove
 (`!h. isDigit h ==> fromChar_unsafe h = num_from_dec_string [h]`,
  GEN_TAC THEN REWRITE_TAC[isDigit_def] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[fromChar_unsafe_def; num_from_dec_string_def; s2n_def; REVERSE;
                  APPEND; MAP; l2n_def; UNHEX; MULT_CLAUSES; ADD_CLAUSES] THEN
  SIMP_TAC[ORD_CHR_RWT; ARITH_RULE `48 < 256`] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC);;

let fromChars_range_unsafe_thm = prove
 (`!str. ALL isDigit str ==>
     fromChars_range_unsafe 0 (LENGTH str) (implode str) = num_from_dec_string str`,
  MATCH_MP_TAC SNOC_INDUCT THEN CONJ_TAC THENL
   [REWRITE_TAC[LENGTH; fromChars_range_unsafe_def; num_from_dec_string_def;
                s2n_def; REVERSE; MAP; l2n_def];
    ALL_TAC] THEN
  X_GEN_TAC `l:string` THEN DISCH_TAC THEN X_GEN_TAC `x:char` THEN
  REWRITE_TAC[EVERY_SNOC; LENGTH_SNOC; fromChars_range_unsafe_def; ADD_CLAUSES] THEN
  STRIP_TAC THEN
  MP_TAC(SPECL [`LENGTH (l:string)`; `LENGTH (l:string)`; `implode (SNOC x l)`]
               fromChars_range_unsafe_0_substring_thm) THEN
  REWRITE_TAC[LE_REFL] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[substring_def; strsub_def; LENGTH_SNOC; ADD_CLAUSES;
              ARITH_RULE `!n. n <= SUC n`; SEG_DEF; DROP_0;
              EL_LENGTH_SNOC] THEN
  SUBGOAL_THEN `TAKE (LENGTH l) (SNOC (x:char) l) = l` SUBST1_TAC THENL
   [REWRITE_TAC[SNOC_APPEND; TAKE_LENGTH_APPEND]; ALL_TAC] THEN
  ASM_SIMP_TAC[fromChar_unsafe_thm] THEN
  REWRITE_TAC[num_from_dec_string_def; s2n_def; REVERSE_SNOC; REVERSE; APPEND;
              MAP; l2n_def] THEN
  ARITH_TAC);;

let fromChars_range_unsafe_eq = prove
 (`!n s. n <= strlen s ==> fromChars_unsafe n s = fromChars_range_unsafe 0 n s`,
  MATCH_MP_TAC fromChars_unsafe_ind THEN CONJ_TAC THENL
   [REWRITE_TAC[fromChars_unsafe_def; fromChars_range_unsafe_def]; ALL_TAC] THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN DISCH_TAC THEN
  ONCE_REWRITE_TAC[fromChars_unsafe_def] THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(SPECL [`8`; `SUC v2`; `str:mlstring`] fromChars_range_unsafe_split) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[padLen_DEC_eq]) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[padLen_DEC_eq; maxSmall_DEC_def] THEN CONV_TAC NUM_REDUCE_CONV THEN
  ARITH_TAC);;

(* the tail of a string as a substring, and the digit strings read by      *)
(* fromChars_unsafe and fromChars                                          *)

let PURE2AUX_SUBSTRING_TL = prove
 (`!(h:char) t. substring (implode (CONS h t)) 1 (LENGTH t) = implode t`,
  REWRITE_TAC[substring_def; LENGTH; ARITH_RULE `1 + n <= SUC n`; SEG_DEF] THEN
  REWRITE_TAC[DROP_DEF; ARITH_EQ; SUB_REFL; DROP_0; TAKE_LENGTH_ID]);;

let PURE2AUX_FROMCHARS_UNSAFE_DIGITS = prove
 (`!s. ALL isDigit s ==> fromChars_unsafe (LENGTH s) (implode s) = num_from_dec_string s`,
  SIMP_TAC[fromChars_range_unsafe_eq; strlen_def; LE_REFL; fromChars_range_unsafe_thm]);;

let PURE2AUX_FROMCHARS_DIGITS = prove
 (`!s. ALL isDigit s /\ ~(s = []) ==>
       fromChars (LENGTH s) (implode s) = SOME (num_from_dec_string s)`,
  REPEAT STRIP_TAC THEN
  W(MP_TAC o PART_MATCH (lhand o rand) fromChars_eq_unsafe o lhand o snd) THEN
  ASM_REWRITE_TAC[explode_thm; strlen_def; LE_REFL; GE; LENGTH_EQ_NIL;
                  ARITH_RULE `1 <= n <=> ~(n = 0)`] THEN
  DISCH_THEN SUBST1_TAC THEN ASM_SIMP_TAC[PURE2AUX_FROMCHARS_UNSAFE_DIGITS]);;

let fromString_unsafe_thm = prove
 (`!str. (~(HD str = CHR 126) ==> ALL isDigit str) /\
         (HD str = CHR 126 ==> ALL isDigit (DROP 1 str))
         ==> fromString_unsafe (implode str) =
             if HD str = CHR 126 then --(&(num_from_dec_string (DROP 1 str)))
             else &(num_from_dec_string str)`,
  GEN_TAC THEN STRUCT_CASES_TAC(ISPEC `str:string` list_CASES) THENL
   [REWRITE_TAC[fromString_unsafe_def; strlen_def; LENGTH; DROP_DEF;
                num_from_dec_string_def; s2n_def; REVERSE; MAP; l2n_def] THEN
    REWRITE_TAC[INT_NEG_0; COND_ID];
    ALL_TAC] THEN
  REWRITE_TAC[fromString_unsafe_def; strlen_def; strsub_def; LENGTH; NOT_SUC;
              EL; HD; SUC_SUB1; PURE2AUX_SUBSTRING_TL] THEN
  REWRITE_TAC[DROP_DEF; ARITH_EQ; SUB_REFL; DROP_0] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[PURE2AUX_FROMCHARS_UNSAFE_DIGITS; GSYM LENGTH]);;

(* HOL4: a CONJ of two instances of fromChars_range_unsafe_thm *)

let fromChars_range_lemma = CONJ
  (REWRITE_RULE[LENGTH_DROP] (ISPEC `DROP 1 str':string` fromChars_range_unsafe_thm))
  (REWRITE_RULE[LENGTH] (ISPEC `CONS (h:char) t` fromChars_range_unsafe_thm));;

let fromString_thm = prove
 (`!str. ~(str = "") /\
         (~(HD str = CHR 126) /\ ~(HD str = CHR 45) /\ ~(HD str = CHR 43)
          ==> ALL isDigit str) /\
         (HD str = CHR 126 \/ HD str = CHR 45 \/ HD str = CHR 43
          ==> ALL isDigit (DROP 1 str) /\ LENGTH str >= 2)
         ==> mlint_fromString (implode str) =
             SOME (if HD str = CHR 126 \/ HD str = CHR 45
                   then --(&(num_from_dec_string (DROP 1 str)))
                   else if HD str = CHR 43
                   then &(num_from_dec_string (DROP 1 str))
                   else &(num_from_dec_string str))`,
  GEN_TAC THEN STRUCT_CASES_TAC(ISPEC `str:string` list_CASES) THEN
  REWRITE_TAC[NOT_CONS_NIL] THEN
  REWRITE_TAC[mlint_fromString_def; strlen_def; strsub_def; LENGTH; NOT_SUC;
              EL; HD; SUC_SUB1; PURE2AUX_SUBSTRING_TL] THEN
  REWRITE_TAC[DROP_DEF; ARITH_EQ; SUB_REFL; DROP_0; GE;
              ARITH_RULE `2 <= SUC n <=> ~(n = 0)`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "h1") (LABEL_TAC "h2")) THEN
  ASM_CASES_TAC `h = CHR 126 \/ h = CHR 45` THEN ASM_REWRITE_TAC[] THENL
   [REMOVE_THEN "h2" MP_TAC THEN ANTS_TAC THENL [ASM_MESON_TAC[]; STRIP_TAC] THEN
    ASM_SIMP_TAC[PURE2AUX_FROMCHARS_DIGITS; GSYM LENGTH_EQ_NIL; OPTION_MAP_DEF;
                 o_THM];
    ALL_TAC] THEN
  ASM_CASES_TAC `h = CHR 43` THEN ASM_REWRITE_TAC[] THENL
   [REMOVE_THEN "h2" MP_TAC THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    ASM_SIMP_TAC[PURE2AUX_FROMCHARS_DIGITS; GSYM LENGTH_EQ_NIL; OPTION_MAP_DEF];
    ALL_TAC] THEN
  REMOVE_THEN "h1" MP_TAC THEN ANTS_TAC THENL [ASM_MESON_TAC[]; DISCH_TAC] THEN
  MP_TAC(SPEC `CONS (h:char) t` PURE2AUX_FROMCHARS_DIGITS) THEN
  ASM_REWRITE_TAC[NOT_CONS_NIL; LENGTH] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[OPTION_MAP_DEF]);;

(* HOL4: fromString_thm |> SIMP_RULE std_ss [GSYM fromString_unsafe_thm].   *)
(* The rewrite does not apply (fromString_thm has no subterm                *)
(* if HD str = #"~" then .. else ..), so the theorem is fromString_thm.     *)

let fromString_eq_unsafe = fromString_thm;;

(* a digit is not a sign *)

let PURE2AUX_DIGIT_NOT_SIGN = prove
 (`!c. isDigit c ==> ~(c = CHR 126) /\ ~(c = CHR 45) /\ ~(c = CHR 43)`,
  GEN_TAC THEN REWRITE_TAC[isDigit_def] THEN STRIP_TAC THEN REPEAT CONJ_TAC THEN
  DISCH_THEN SUBST_ALL_TAC THEN REPEAT(POP_ASSUM MP_TAC) THEN
  SIMP_TAC[ORD_CHR_RWT; ARITH]);;

let fromString_toString_Num = prove
 (`!n. &0 <= n ==>
       mlint_fromString (implode (num_to_dec_string (num_of_int n))) = SOME n`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `?h t. num_to_dec_string (num_of_int n) = CONS h t`
   STRIP_ASSUME_TAC THENL
   [MESON_TAC[num_to_dec_string_nil; list_CASES]; ALL_TAC] THEN
  SUBGOAL_THEN `ALL isDigit (CONS h t)` ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[EVERY_isDigit_num_to_dec_string];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(h = CHR 126) /\ ~(h = CHR 45) /\ ~(h = CHR 43)`
   STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC PURE2AUX_DIGIT_NOT_SIGN THEN ASM_MESON_TAC[ALL]; ALL_TAC] THEN
  MP_TAC(SPEC `CONS (h:char) t` fromString_thm) THEN
  ASM_REWRITE_TAC[NOT_CONS_NIL; HD] THEN DISCH_THEN SUBST1_TAC THEN
  UNDISCH_TAC `num_to_dec_string (num_of_int n) = CONS h t` THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  ASM_SIMP_TAC[toNum_toString; INT_OF_NUM_OF_INT]);;

let fromString_helper = prove
 (`!i c. HD (num_to_dec_string i) = c ==> isDigit c`,
  REPEAT GEN_TAC THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MP_TAC(SPEC `i:num` EVERY_isDigit_num_to_dec_string) THEN
  MP_TAC(SPEC `i:num` num_to_dec_string_nil) THEN
  SPEC_TAC(`num_to_dec_string i`,`l:string`) THEN
  LIST_INDUCT_TAC THEN REWRITE_TAC[ALL; HD; NOT_CONS_NIL] THEN SIMP_TAC[]);;

(* HOL4 proves the same statement again under the name fromString_hd *)

let fromString_hd = fromString_helper;;

let toString_len = prove
 (`!i. LENGTH (num_to_dec_string i) + 1 >= 2`,
  GEN_TAC THEN MP_TAC(SPEC `i:num` num_to_dec_string_nil) THEN
  REWRITE_TAC[GSYM LENGTH_EQ_NIL] THEN ARITH_TAC);;

let toString_len_1 = prove
 (`!i. ~(HD (num_to_dec_string i) = CHR 126) /\
       ~(HD (num_to_dec_string i) = CHR 45) /\
       ~(HD (num_to_dec_string i) = CHR 43)`,
  GEN_TAC THEN MATCH_MP_TAC PURE2AUX_DIGIT_NOT_SIGN THEN
  MATCH_MP_TAC fromString_hd THEN MESON_TAC[]);;

let fromString_int_to_string = prove
 (`!neg_char i.
     neg_char = CHR 126 \/ neg_char = CHR 45 ==>
     mlint_fromString (int_to_string neg_char i) = SOME i`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[int_to_string_thm] THEN
  COND_CASES_TAC THEN REWRITE_TAC[APPEND] THENL
   [ALL_TAC;
    ASM_SIMP_TAC[fromString_toString_Num; INT_ABS_POS] THEN
    AP_TERM_TAC THEN ASM_ARITH_TAC] THEN
  MP_TAC(SPEC `CONS (neg_char:char) (num_to_dec_string (num_of_int (abs i)))`
              fromString_thm) THEN
  REWRITE_TAC[NOT_CONS_NIL; HD; DROP_DEF; ARITH_EQ; SUB_REFL; DROP_0; LENGTH] THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[EVERY_isDigit_num_to_dec_string] THEN
    MP_TAC(SPEC `num_of_int (abs i)` num_to_dec_string_nil) THEN
    REWRITE_TAC[GSYM LENGTH_EQ_NIL] THEN ASM_MESON_TAC[ARITH_RULE
     `~(n = 0) ==> SUC n >= 2`];
    DISCH_THEN SUBST1_TAC] THEN
  ASM_REWRITE_TAC[toNum_toString] THEN
  SIMP_TAC[INT_OF_NUM_OF_INT; INT_ABS_POS] THEN AP_TERM_TAC THEN
  ASM_ARITH_TAC);;
let _ = cake_add_simps [fromString_int_to_string];;

let fromString_toString = prove
 (`!i:int. mlint_fromString (toString i) = SOME i`,
  SIMP_TAC[toString_def1; fromString_int_to_string]);;
let _ = cake_add_simps [fromString_toString];;

let fromNatString_toString = prove
 (`!n:num. fromNatString (num_to_str n) = SOME n`,
  SIMP[num_to_str_def; fromNatString_def; fromString_toString; INT_POS;
       NUM_OF_INT_OF_NUM]);;
let _ = cake_add_simps [fromNatString_toString];;

let fromChar_IS_SOME_IFF = prove
 (`!c. IS_SOME (fromChar c) <=> isDigit c`,
  GEN_TAC THEN MP_TAC(SPEC `c:char` ranged_char_nchotomy) THEN
  DISCH_THEN(X_CHOOSE_THEN `n:num` STRIP_ASSUME_TAC) THEN
  ASM_SIMP_TAC[fromChar_def; isDigit_def; CHR_11; ORD_CHR_RWT; ARITH] THEN
  REPEAT COND_CASES_TAC THEN REWRITE_TAC[IS_SOME_DEF] THEN ASM_ARITH_TAC);;

let fromChars_range_IS_SOME_IFF = prove
 (`!s x y. x + y <= strlen s ==>
     (IS_SOME (fromChars_range x y s) <=> ALL isDigit (TAKE y (DROP x (explode s))))`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
  REWRITE_TAC[fromChars_range_def; IS_SOME_DEF; TAKE_0; ALL] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_TAC] THEN
  CASES_ON `s:mlstring` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[strlen_def; explode_thm]) THEN
  REWRITE_TAC[explode_thm; strsub_def; LET_DEF; LET_END_DEF] THEN
  REWRITE_TAC[OPTION_MAP2_DEF; COND_RAND; IS_SOME_DEF; IS_SOME_MAP] THEN
  ASM_REWRITE_TAC[fromChar_IS_SOME_IFF] THEN
  REWRITE_TAC[ADD1; TAKE_SUM; ALL_APPEND] THEN
  SUBGOAL_THEN `TAKE 1 (DROP y (DROP x (a:string))) = [EL (x + y) a]`
   SUBST1_TAC THENL
   [SUBGOAL_THEN `y < LENGTH (DROP x (a:string))` ASSUME_TAC THENL
     [REWRITE_TAC[LENGTH_DROP] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[TAKE1_DROP] THEN REWRITE_TAC[CONS_11] THEN
    ONCE_REWRITE_TAC[ADD_SYM] THEN MATCH_MP_TAC EL_DROP THEN ASM_ARITH_TAC;
    REWRITE_TAC[ALL] THEN CONV_TAC TAUT]);;

let fromChars_IS_SOME_IFF = prove
 (`!n s. n <= strlen s /\ n >= 1 ==>
         (IS_SOME (fromChars n s) <=> ALL isDigit (TAKE n (explode s)))`,
  MATCH_MP_TAC fromChars_ind THEN CONJ_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN STRIP_TAC THEN
  ONCE_REWRITE_TAC[fromChars_def] THEN COND_CASES_TAC THENL
   [MP_TAC(SPECL [`str:mlstring`; `0`; `SUC v2`] fromChars_range_IS_SOME_IFF) THEN
    ASM_REWRITE_TAC[ADD_CLAUSES; DROP_0];
    ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[padLen_DEC_eq]) THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF; padLen_DEC_eq] THEN
  FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_TAC] THEN
  REWRITE_TAC[OPTION_MAP2_DEF; COND_RAND; IS_SOME_DEF; IS_SOME_MAP] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`str:mlstring`; `SUC v2 - 8`; `8`] fromChars_range_IS_SOME_IFF) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[GSYM ALL_APPEND; GSYM TAKE_SUM] THEN
  SUBGOAL_THEN `(SUC v2 - 8) + 8 = SUC v2` SUBST1_TAC THENL
   [ASM_ARITH_TAC; CONV_TAC TAUT]);;

let fromString_EQ_NONE = prove
 (`!c x. ~isDigit c /\ ~(c = CHR 43) /\ ~(c = CHR 126) /\ ~(c = CHR 45) ==>
         mlint_fromString (implode (CONS c x)) = NONE`,
  REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[mlint_fromString_def; strsub_def; strlen_def; LENGTH; NOT_SUC;
                  EL; HD] THEN
  MP_TAC(SPECL [`SUC (LENGTH (x:string))`; `implode (CONS c x)`]
               fromChars_IS_SOME_IFF) THEN
  REWRITE_TAC[strlen_def; explode_thm; LENGTH; LE_REFL; GE;
              ARITH_RULE `1 <= SUC n`; TAKE_DEF; NOT_SUC; ALL] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `fromChars (SUC (LENGTH x)) (implode (CONS c x))` option_nchotomy) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[IS_SOME_DEF; OPTION_MAP_DEF]);;

(* this formulation avoids a comparsion using = for better performance *)

(* HOL4: int_cmp_def *)

let mlint_int_cmp_def = cake_def
  `mlint_int_cmp i (j:int) =
     if i < j then LESS else if j < i then GREATER else EQUAL`;;

(* HOL4: num_gcd_def (termination by HOL4's automatic measure on a) *)

let mlint_num_gcd_def = cake_def_wf
  `measure (FST:num#num->num)`
  (REWRITE_TAC(WF_REL_THMS @ [FST; SND]) THEN REPEAT STRIP_TAC THEN
   MP_TAC(SPECL [`b:num`; `a:num`] MOD_LT_EQ) THEN ASM_ARITH_TAC)
  `mlint_num_gcd a b = if a = 0 then b else mlint_num_gcd (b MOD a) a`;;

let mlint_num_gcd_ind = cake_ind "mlint_num_gcd";;

(* HOL4: num_gcd = gcd, with HOL4's curried gcd a b = num_gcd(a,b) *)

let num_gcd_eq_gcd = prove
 (`!a b. mlint_num_gcd a b = num_gcd(a,b)`,
  MATCH_MP_TAC mlint_num_gcd_ind THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  ONCE_REWRITE_TAC[GCD_EFFICIENTLY; mlint_num_gcd_def] THEN
  COND_CASES_TAC THEN ASM_SIMP_TAC[]);;

(* HOL4: int_gcd_def *)

let mlint_int_gcd_def = cake_def
  `mlint_int_gcd (m:int) (n:int) =
     &(mlint_num_gcd (num_of_int (abs m)) (num_of_int (abs n))):int`;;

(* lemmas *)

let num_to_str_11 = prove
 (`!n0 n1. num_to_str n0 = num_to_str n1 <=> n0 = n1`,
  REWRITE_TAC[num_to_str_thm; injectivity "mlstring"; toString_inj]);;

let num_to_str_not_nil = prove
 (`!i s. num_to_str i = implode s ==> ~(s = "")`,
  REWRITE_TAC[num_to_str_thm; injectivity "mlstring"] THEN
  MESON_TAC[num_to_dec_string_nil]);;

let ORD_HEX_BOUND1 = prove
 (`!i. i < 10 ==> 48 <= ORD (HEX i)`,
  SIMP_TAC[HEX; ORD_CHR_RWT; ARITH_RULE `i < 10 ==> 48 + i < 256`] THEN
  ARITH_TAC);;

let ORD_HEX_BOUND2 = prove
 (`!i. i < 10 ==> ORD (HEX i) <= 57`,
  SIMP_TAC[HEX; ORD_CHR_RWT; ARITH_RULE `i < 10 ==> 48 + i < 256`] THEN
  ARITH_TAC);;

let num_to_str_every = prove
 (`!i s. num_to_str i = implode s ==> ALL (\x. 48 <= ORD x /\ ORD x <= 57) s`,
  REWRITE_TAC[num_to_str_thm; injectivity "mlstring"] THEN
  REPEAT GEN_TAC THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[GSYM isDigit_def; ETA_AX; EVERY_isDigit_num_to_dec_string]);;

let num_to_str_imp_cons = prove
 (`!i s. num_to_str i = implode s ==>
         ?x xs. s = CONS x xs /\ 48 <= ORD x /\ ORD x <= 57 /\
                ALL (\x. 48 <= ORD x /\ ORD x <= 57) xs`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP num_to_str_every) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP num_to_str_not_nil) THEN
  POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN
  STRUCT_CASES_TAC(ISPEC `s:string` list_CASES) THEN
  REWRITE_TAC[ALL; NOT_CONS_NIL; CONS_11] THEN MESON_TAC[]);;

(* two lists of P-elements followed by a non-P element: equal prefixes *)

let PURE2AUX_ALL_APPEND_CONS = prove
 (`!P (s1:A list) s2 x1 xs1 x2 xs2.
     ALL P s1 /\ ALL P s2 /\ ~P x1 /\ ~P x2 /\
     APPEND s1 (CONS x1 xs1) = APPEND s2 (CONS x2 xs2) ==> s1 = s2`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[APPEND; ALL; CONS_11; NOT_CONS_NIL] THEN ASM_MESON_TAC[]);;

let num_to_str_APPEND_11 = prove
 (`!s1 x1 xs1 s2 x2 xs2 n1 n2.
     APPEND s1 (CONS x1 xs1) = APPEND s2 (CONS x2 xs2) /\
     num_to_str n1 = implode s1 /\ num_to_str n2 = implode s2 /\
     ~(48 <= ORD x1 /\ ORD x1 <= 57) /\ ~(48 <= ORD x2 /\ ORD x2 <= 57)
     ==> n1 = n2 /\ CONS x1 xs1 = CONS x2 xs2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `s1:string = s2` SUBST_ALL_TAC THENL
   [MP_TAC(ISPECL [`\x:char. 48 <= ORD x /\ ORD x <= 57`; `s1:string`; `s2:string`;
                   `x1:char`; `xs1:string`; `x2:char`; `xs2:string`]
                  PURE2AUX_ALL_APPEND_CONS) THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[num_to_str_every];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (is_eq o concl) o
                GEN_REWRITE_RULE I [APPEND_LCANCEL]) THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[] THEN
  ASM_MESON_TAC[num_to_str_11]);;

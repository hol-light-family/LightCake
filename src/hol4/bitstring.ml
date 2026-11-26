(* ========================================================================= *)
(* bitstring: port of HOL4 src/n-bit/bitstringScript.sml (the HOL4 library   *)
(* of CakeML v3479), the part the closure uses: boolean lists as bit         *)
(* strings (most significant bit first, e.g. [T; F] represents 2).           *)
(* Words are HOL Light's (Library/words.ml): the HOL4 word type of index A   *)
(* is N word, n2w = word, w2n = val, bit i of w (HOL4 index) = bit i w,      *)
(* FCP i. P i = word_of_bits (the set of i with P i), word_lsl = word_shl,   *)
(* word_or, word_and, word_xor as in HOL4, dimindex of A = dimindex(:N);     *)
(* GENLIST f n = list_of_seq f n, ZIP (l1,l2) = ZIP l1 l2.  A HOL4           *)
(* let l = e in t is written with e substituted (fixwidth, bitwise).         *)
(* Helper lemmas that are not HOL4 theorems have the prefix LSTRAUX_.        *)
(* HOL4 field is bitstring_field (a short or common word; field is also a    *)
(* constant of HOL Light's Library/ringtheory.ml), and field_def is          *)
(* bitstring_field_def.                                                      *)
(* ========================================================================= *)

needs "hol4/vocab.ml";;
needs "hol4/list.ml";;
needs "hol4/numposrep.ml";;

prioritize_num();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Definitions.                                                              *)
(* ------------------------------------------------------------------------- *)

let boolify_def = new_recursive_definition list_RECURSION
  `(!a. boolify a [] = a) /\
   (!a n l. boolify a (CONS n l) = boolify (CONS (~(n = 0)) a) l)`;;

let LSTRAUX_BITIFY = new_recursive_definition list_RECURSION
  `(!a. bitify a [] = a) /\
   (!a b l. bitify a (CONS b l) = bitify (CONS (if b then 1 else 0) a) l)`;;

let bitify_def = prove
 (`(!a. bitify a [] = a) /\
   (!a l. bitify a (CONS F l) = bitify (CONS 0 a) l) /\
   (!a l. bitify a (CONS T l) = bitify (CONS 1 a) l)`,
  REWRITE_TAC[LSTRAUX_BITIFY]);;

let n2v_def = new_definition
  `n2v n = boolify [] (n2l 2 n)`;;

let v2n_def = new_definition
  `v2n l = l2n 2 (bitify [] l)`;;

let zero_extend_def = new_definition
  `zero_extend n v = PAD_LEFT F n v`;;

let sign_extend_def = new_definition
  `sign_extend n v = PAD_LEFT (HD v) n (v:bool list)`;;

let fixwidth_def = new_definition
  `fixwidth n v =
     if LENGTH v < n then zero_extend n v else DROP (LENGTH v - n) v`;;

let shiftl_def = new_definition
  `shiftl v m = PAD_RIGHT F (LENGTH v + m) v`;;

let shiftr_def = new_definition
  `shiftr (v:bool list) m = TAKE (LENGTH v - m) v`;;

let bitstring_field_def = new_definition
  `bitstring_field h l v = fixwidth (SUC h - l) (shiftr v l)`;;

let testbit_def = new_definition
  `testbit b v <=> bitstring_field b b v = [T]`;;

let w2v_def = new_definition
  `w2v (w:N word) = list_of_seq (\i. bit (dimindex(:N) - 1 - i) w) (dimindex(:N))`;;

let v2w_def = new_definition
  `v2w v:N word = word_of_bits {i | testbit i v}`;;

let bitwise_def = new_definition
  `bitwise (f:bool->bool->bool) v1 v2 =
     MAP (UNCURRY f) (ZIP (fixwidth (MAX (LENGTH v1) (LENGTH v2)) v1)
                          (fixwidth (MAX (LENGTH v1) (LENGTH v2)) v2))`;;

let bnot_def = new_definition
  `bnot = MAP (~)`;;

let bor_def = new_definition
  `bor = bitwise (\/)`;;

let band_def = new_definition
  `band = bitwise (/\)`;;

let bxor_def = new_definition
  `bxor = bitwise (\x y. ~(x = y))`;;

(* ------------------------------------------------------------------------- *)
(* List helpers (list and rich_list theorems of other units).                *)
(* ------------------------------------------------------------------------- *)

let LSTRAUX_EL_TAKE = prove
 (`!(l:A list) n i. i < n /\ n <= LENGTH l ==> EL i (TAKE n l) = EL i l`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[TAKE_DEF; LENGTH] THEN
  REPEAT STRIP_TAC THEN
  COND_CASES_TAC THENL [ASM_MESON_TAC[LT]; ALL_TAC] THEN
  REWRITE_TAC[EL_CONS] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC);;

let LSTRAUX_EL_DROP = prove
 (`!(l:A list) n i. i + n < LENGTH l ==> EL i (DROP n l) = EL (i + n) l`,
  LIST_INDUCT_TAC THENL [REWRITE_TAC[LENGTH; LT]; ALL_TAC] THEN
  REWRITE_TAC[DROP_DEF; LENGTH] THEN REPEAT STRIP_TAC THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[ADD_CLAUSES] THEN
  REWRITE_TAC[EL_CONS] THEN
  SUBGOAL_THEN `~(i + n = 0) /\ (i + n) - 1 = i + (n - 1)` STRIP_ASSUME_TAC THENL
   [ASM_ARITH_TAC; ASM_REWRITE_TAC[]] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC);;

let LSTRAUX_DROP_LAST = prove
 (`!(l:A list) k. LENGTH l = SUC k ==> DROP k l = [EL k l]`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[LENGTH; NOT_SUC; SUC_INJ] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[DROP_DEF; EL_CONS] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL
   [UNDISCH_TAC `LENGTH (t:A list) = k` THEN ASM_REWRITE_TAC[LENGTH_EQ_NIL] THEN
    DISCH_THEN SUBST1_TAC THEN REFL_TAC;
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* testbit: bit b of v counts from the end of v.                             *)
(* ------------------------------------------------------------------------- *)

let testbit = prove
 (`!b v. testbit b v <=> b < LENGTH v /\ EL (LENGTH v - 1 - b) v`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[testbit_def; bitstring_field_def; shiftr_def; fixwidth_def; zero_extend_def;
              PAD_LEFT] THEN
  REWRITE_TAC[ARITH_RULE `SUC b - b = 1`] THEN
  SUBGOAL_THEN `LENGTH (TAKE (LENGTH v - b) (v:bool list)) = LENGTH v - b`
  ASSUME_TAC THENL
   [MATCH_MP_TAC LENGTH_TAKE THEN ARITH_TAC; ASM_REWRITE_TAC[]] THEN
  ASM_CASES_TAC `b < LENGTH (v:bool list)` THEN ASM_REWRITE_TAC[] THENL
   [SUBGOAL_THEN `~(LENGTH (v:bool list) - b < 1)` (fun th -> REWRITE_TAC[th]) THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(ISPECL [`TAKE (LENGTH v - b) (v:bool list)`;
                   `(LENGTH (v:bool list) - b) - 1`] LSTRAUX_DROP_LAST) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
    REWRITE_TAC[CONS_11] THEN
    SUBGOAL_THEN `(LENGTH (v:bool list) - b) - 1 = LENGTH v - 1 - b` SUBST1_TAC THENL
     [ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `EL (LENGTH v - 1 - b) (TAKE (LENGTH v - b) (v:bool list)) =
                  EL (LENGTH v - 1 - b) v` SUBST1_TAC THENL
     [MATCH_MP_TAC LSTRAUX_EL_TAKE THEN ASM_ARITH_TAC; ALL_TAC] THEN
    CONV_TAC TAUT;
    SUBGOAL_THEN `LENGTH (v:bool list) - b = 0` SUBST1_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[ARITH_RULE `0 < 1 /\ 1 - 0 = 1`; TAKE_0; APPEND_NIL] THEN
    REWRITE_TAC[num_CONV `1`; list_of_seq; APPEND; K_THM; CONS_11]]);;

let testbit_geq_len = prove
 (`!v i. LENGTH v <= i ==> ~testbit i v`,
  SIMP_TAC[testbit; GSYM NOT_LE]);;

let testbit_el = prove
 (`!v i. i < LENGTH v ==> (testbit i v <=> EL (LENGTH v - 1 - i) v)`,
  SIMP_TAC[testbit]);;

let LSTRAUX_TESTBIT_LT = prove
 (`!i v. testbit i v ==> i < LENGTH v`,
  SIMP_TAC[testbit]);;

let LSTRAUX_TESTBIT_EQ = prove
 (`!u v. LENGTH u = LENGTH v /\ (!i. testbit i u <=> testbit i v) ==> u = v`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[LIST_EQ] THEN
  X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `LENGTH (v:bool list) - 1 - n`) THEN
  ASM_REWRITE_TAC[testbit] THEN
  ASM_SIMP_TAC[ARITH_RULE `n < l ==> l - 1 - n < l /\ l - 1 - (l - 1 - n) = n`] THEN
  CONV_TAC TAUT);;

let LSTRAUX_TESTBIT_APPEND = prove
 (`!i u v. testbit i (APPEND u v) <=>
           if i < LENGTH v then testbit i v else testbit (i - LENGTH v) u`,
  REPEAT GEN_TAC THEN REWRITE_TAC[testbit; LENGTH_APPEND; EL_APPEND] THEN
  ASM_CASES_TAC `i < LENGTH (v:bool list)` THEN ASM_REWRITE_TAC[] THENL
   [SUBGOAL_THEN `i < LENGTH (u:bool list) + LENGTH (v:bool list) /\
                  ~(((LENGTH u + LENGTH v) - 1) - i < LENGTH u) /\
                  (((LENGTH u + LENGTH v) - 1) - i) - LENGTH u = LENGTH v - 1 - i`
     STRIP_ASSUME_TAC THENL [ASM_ARITH_TAC; ASM_REWRITE_TAC[]];
    ASM_CASES_TAC `i < LENGTH (u:bool list) + LENGTH (v:bool list)` THEN
    ASM_REWRITE_TAC[] THENL
     [SUBGOAL_THEN `i - LENGTH (v:bool list) < LENGTH (u:bool list) /\
                    ((LENGTH u + LENGTH v) - 1) - i < LENGTH u /\
                    LENGTH u - 1 - (i - LENGTH v) = ((LENGTH u + LENGTH v) - 1) - i`
       STRIP_ASSUME_TAC THENL [ASM_ARITH_TAC; ASM_REWRITE_TAC[]];
      SUBGOAL_THEN `~(i - LENGTH (v:bool list) < LENGTH (u:bool list))`
        (fun th -> REWRITE_TAC[th]) THEN ASM_ARITH_TAC]]);;

let LSTRAUX_TESTBIT_FALSES = prove
 (`!i k. ~testbit i (list_of_seq (combin_K F) k)`,
  REWRITE_TAC[testbit; LENGTH_LIST_OF_SEQ] THEN REPEAT STRIP_TAC THEN
  POP_ASSUM MP_TAC THEN ASM_SIMP_TAC[EL_LIST_OF_SEQ; K_THM;
    ARITH_RULE `i < k ==> k - 1 - i < k`]);;

let LSTRAUX_TESTBIT_ZERO_EXTEND = prove
 (`!i n v. testbit i (zero_extend n v) <=> testbit i v`,
  REWRITE_TAC[zero_extend_def; PAD_LEFT; LSTRAUX_TESTBIT_APPEND] THEN
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN
  ASM_SIMP_TAC[LSTRAUX_TESTBIT_FALSES; testbit_geq_len; GSYM NOT_LT]);;

let LSTRAUX_TESTBIT_DROP = prove
 (`!i k v. testbit i (DROP k v) <=> i < LENGTH v - k /\ testbit i v`,
  REPEAT GEN_TAC THEN REWRITE_TAC[testbit; LENGTH_DROP] THEN
  ASM_CASES_TAC `i < LENGTH (v:bool list) - k` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `((LENGTH (v:bool list) - k) - 1 - i) + k < LENGTH v /\
                ((LENGTH v - k) - 1 - i) + k = LENGTH v - 1 - i /\
                i < LENGTH v` STRIP_ASSUME_TAC THENL
   [ASM_ARITH_TAC; ASM_SIMP_TAC[LSTRAUX_EL_DROP]]);;

let LSTRAUX_TESTBIT_FIXWIDTH = prove
 (`!i n v. testbit i (fixwidth n v) <=> i < n /\ testbit i v`,
  REPEAT GEN_TAC THEN REWRITE_TAC[fixwidth_def] THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[LSTRAUX_TESTBIT_ZERO_EXTEND; LSTRAUX_TESTBIT_DROP] THENL
   [ASM_MESON_TAC[LSTRAUX_TESTBIT_LT; LT_TRANS];
    SUBGOAL_THEN `LENGTH (v:bool list) - (LENGTH v - n) = n` SUBST1_TAC THENL
     [ASM_ARITH_TAC; REWRITE_TAC[]]]);;

let LSTRAUX_TESTBIT_SHIFTL = prove
 (`!i v n. testbit i (shiftl v n) <=> n <= i /\ testbit (i - n) v`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[shiftl_def; PAD_RIGHT; LSTRAUX_TESTBIT_APPEND] THEN
  REWRITE_TAC[LENGTH_LIST_OF_SEQ; ARITH_RULE `(l + n) - l = n:num`] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[LSTRAUX_TESTBIT_FALSES; GSYM NOT_LT]);;

(* ------------------------------------------------------------------------- *)
(* Lengths, fixwidth.                                                        *)
(* ------------------------------------------------------------------------- *)

let length_fixwidth = prove
 (`!n v. LENGTH (fixwidth n v) = n`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[fixwidth_def; zero_extend_def; PAD_LEFT] THEN
  COND_CASES_TAC THEN
  ASM_REWRITE_TAC[LENGTH_APPEND; LENGTH_LIST_OF_SEQ; LENGTH_DROP] THEN
  ASM_ARITH_TAC);;

let length_field = prove
 (`!h l v. LENGTH (bitstring_field h l v) = SUC h - l`,
  REWRITE_TAC[bitstring_field_def; length_fixwidth]);;

let length_shiftr = prove
 (`!v n. LENGTH (shiftr v n) = LENGTH v - n`,
  REPEAT GEN_TAC THEN REWRITE_TAC[shiftr_def] THEN
  MATCH_MP_TAC LENGTH_TAKE THEN ARITH_TAC);;

let length_w2v = prove
 (`!w:N word. LENGTH (w2v w) = dimindex(:N)`,
  REWRITE_TAC[w2v_def; LENGTH_LIST_OF_SEQ]);;

let fixwidth_id = prove
 (`!w. fixwidth (LENGTH w) w = w`,
  REWRITE_TAC[fixwidth_def; LT_REFL; SUB_REFL; DROP_0]);;

let fixwidth_id_imp = prove
 (`!n w. n = LENGTH w ==> fixwidth n w = w`,
  SIMP_TAC[fixwidth_id]);;

let fixwidth_fixwidth = prove
 (`!n v. fixwidth n (fixwidth n v) = fixwidth n v`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC fixwidth_id_imp THEN
  REWRITE_TAC[length_fixwidth]);;

let LSTRAUX_TESTBIT_BITWISE = prove
 (`!f i v w. testbit i (bitwise f v w) <=>
             i < MAX (LENGTH v) (LENGTH w) /\ f (testbit i v) (testbit i w)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[bitwise_def] THEN
  ABBREV_TAC `m = MAX (LENGTH (v:bool list)) (LENGTH (w:bool list))` THEN
  SUBGOAL_THEN `LENGTH (ZIP (fixwidth m v) (fixwidth m w)) = m` ASSUME_TAC THENL
   [SIMP_TAC[LENGTH_ZIP; length_fixwidth]; ALL_TAC] THEN
  REWRITE_TAC[testbit; LENGTH_MAP] THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `i < m` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `m - 1 - i < m` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[EL_MAP; EL_ZIP; length_fixwidth; UNCURRY_DEF] THEN
  MP_TAC(SPECL [`i:num`; `m:num`; `v:bool list`] LSTRAUX_TESTBIT_FIXWIDTH) THEN
  MP_TAC(SPECL [`i:num`; `m:num`; `w:bool list`] LSTRAUX_TESTBIT_FIXWIDTH) THEN
  ASM_SIMP_TAC[testbit; length_fixwidth]);;

(* ------------------------------------------------------------------------- *)
(* v2w and w2v.                                                              *)
(* ------------------------------------------------------------------------- *)

let bit_v2w = prove
 (`!n v. bit n (v2w v:N word) <=> n < dimindex(:N) /\ testbit n v`,
  REWRITE_TAC[v2w_def; BIT_WORD_OF_BITS; IN_ELIM_THM]);;

let testbit_w2v = prove
 (`!n w:N word. testbit n (w2v w) <=> bit n w`,
  REPEAT GEN_TAC THEN REWRITE_TAC[testbit; length_w2v] THEN
  ASM_CASES_TAC `n < dimindex(:N)` THEN ASM_SIMP_TAC[BIT_TRIVIAL; GSYM NOT_LT] THEN
  MP_TAC(ISPEC `(:N)` DIMINDEX_GE_1) THEN DISCH_TAC THEN
  REWRITE_TAC[w2v_def] THEN
  ASM_SIMP_TAC[EL_LIST_OF_SEQ; ARITH_RULE `1 <= d ==> d - 1 - n < d`] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN ASM_ARITH_TAC);;

let w2v_v2w = prove
 (`!v. w2v (v2w v:N word) = fixwidth (dimindex(:N)) v`,
  GEN_TAC THEN MATCH_MP_TAC LSTRAUX_TESTBIT_EQ THEN
  REWRITE_TAC[length_w2v; length_fixwidth; testbit_w2v; bit_v2w;
              LSTRAUX_TESTBIT_FIXWIDTH]);;

let v2w_w2v = prove
 (`!w:N word. v2w (w2v w) = w`,
  REWRITE_TAC[WORD_EQ_BITS_ALT; bit_v2w; testbit_w2v] THEN MESON_TAC[]);;

let v2w_fixwidth = prove
 (`!v. v2w (fixwidth (dimindex(:N)) v) = v2w v:N word`,
  REWRITE_TAC[WORD_EQ_BITS_ALT; bit_v2w; LSTRAUX_TESTBIT_FIXWIDTH] THEN
  MESON_TAC[]);;

let bitstring_nchotomy = prove
 (`!w:N word. ?v. w = v2w v`,
  MESON_TAC[v2w_w2v]);;

(* ------------------------------------------------------------------------- *)
(* Word operations on v2w.                                                   *)
(* ------------------------------------------------------------------------- *)

let LSTRAUX_BITWISE_V2W_TAC =
  REWRITE_TAC[WORD_EQ_BITS_ALT; bit_v2w; BIT_WORD_OR; BIT_WORD_AND;
              BIT_WORD_XOR; bor_def; band_def; bxor_def;
              LSTRAUX_TESTBIT_BITWISE] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`i:num`; `v:bool list`] LSTRAUX_TESTBIT_LT) THEN
  MP_TAC(SPECL [`i:num`; `w:bool list`] LSTRAUX_TESTBIT_LT) THEN
  REWRITE_TAC[ARITH_RULE `i < MAX a b <=> i < a \/ i < b`] THEN
  CONV_TAC TAUT;;

let word_and_v2w = prove
 (`!v w. word_and (v2w v) (v2w w):N word = v2w (band v w)`,
  LSTRAUX_BITWISE_V2W_TAC);;

let word_or_v2w = prove
 (`!v w. word_or (v2w v) (v2w w):N word = v2w (bor v w)`,
  LSTRAUX_BITWISE_V2W_TAC);;

let word_xor_v2w = prove
 (`!v w. word_xor (v2w v) (v2w w):N word = v2w (bxor v w)`,
  LSTRAUX_BITWISE_V2W_TAC);;

let word_lsl_v2w = prove
 (`!n v. word_shl (v2w v:N word) n = v2w (shiftl v n)`,
  REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_SHL; bit_v2w; LSTRAUX_TESTBIT_SHIFTL] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `n:num <= i` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `i - n < dimindex(:N)` (fun th -> REWRITE_TAC[th]) THEN
  ASM_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* v2n and n2v.                                                              *)
(* ------------------------------------------------------------------------- *)

let bitify_reverse_map = prove
 (`!v a. bitify a v = APPEND (REVERSE (MAP (\b. if b then 1 else 0) v)) a`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[LSTRAUX_BITIFY; MAP; REVERSE; APPEND] THEN
  REWRITE_TAC[GSYM APPEND_ASSOC; APPEND]);;

let boolify_reverse_map = prove
 (`!v a. boolify a v = APPEND (REVERSE (MAP (\n. ~(n = 0)) v)) a`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[boolify_def; MAP; REVERSE; APPEND] THEN
  REWRITE_TAC[GSYM APPEND_ASSOC; APPEND]);;

let length_bitify = prove
 (`!v l. LENGTH (bitify l v) = LENGTH l + LENGTH v`,
  REWRITE_TAC[bitify_reverse_map; LENGTH_APPEND; LENGTH_REVERSE; LENGTH_MAP] THEN
  ARITH_TAC);;

let length_bitify_null = prove
 (`!v. LENGTH (bitify [] v) = LENGTH v`,
  REWRITE_TAC[length_bitify; LENGTH; ADD_CLAUSES]);;

let v2n_lt = prove
 (`!v. v2n v < 2 EXP LENGTH v`,
  GEN_TAC THEN REWRITE_TAC[v2n_def; bitify_reverse_map; APPEND_NIL] THEN
  MP_TAC(ISPECL [`REVERSE (MAP (\b. if b then 1 else 0) (v:bool list))`; `2`]
                l2n_lt) THEN
  REWRITE_TAC[LENGTH_REVERSE; LENGTH_MAP; ARITH]);;

let v2n_APPEND = prove
 (`!a b. v2n (APPEND a b) = v2n b + 2 EXP LENGTH b * v2n a`,
  REWRITE_TAC[v2n_def; bitify_reverse_map; APPEND_NIL; MAP_APPEND;
              REVERSE_APPEND; l2n_APPEND; LENGTH_REVERSE; LENGTH_MAP]);;

let v2n = prove
 (`v2n [] = 0 /\
   (!b bs. v2n (CONS b bs) = if b then 2 EXP LENGTH bs + v2n bs else v2n bs)`,
  CONJ_TAC THENL
   [REWRITE_TAC[v2n_def; bitify_reverse_map; MAP; REVERSE; APPEND; l2n_def];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `CONS (b:bool) bs = APPEND [b] bs` SUBST1_TAC THENL
   [REWRITE_TAC[APPEND]; ALL_TAC] THEN
  REWRITE_TAC[v2n_APPEND] THEN
  REWRITE_TAC[v2n_def; bitify_reverse_map; MAP; REVERSE; APPEND; l2n_def] THEN
  COND_CASES_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC);;

let LSTRAUX_ODD_V2N_DIV = prove
 (`!v i. ODD (v2n v DIV 2 EXP i) <=> testbit i v`,
  LIST_INDUCT_TAC THENL
   [REWRITE_TAC[v2n; DIV_0; ODD; testbit; LENGTH; LT]; ALL_TAC] THEN
  X_GEN_TAC `i:num` THEN
  SUBGOAL_THEN `CONS (h:bool) t = APPEND [h] t` SUBST1_TAC THENL
   [REWRITE_TAC[APPEND]; ALL_TAC] THEN
  REWRITE_TAC[LSTRAUX_TESTBIT_APPEND; v2n_APPEND] THEN
  SUBGOAL_THEN `v2n [h] = bitval h` SUBST1_TAC THENL
   [REWRITE_TAC[v2n; LENGTH; EXP; bitval] THEN COND_CASES_TAC THEN ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPEC `t:bool list` v2n_lt) THEN
  ABBREV_TAC `L = LENGTH (t:bool list)` THEN ABBREV_TAC `r = v2n t` THEN
  DISCH_TAC THEN COND_CASES_TAC THENL
   [FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC RAND_CONV [GSYM th]) THEN
    SUBGOAL_THEN `2 EXP L = 2 EXP i * 2 EXP (L - i)` SUBST1_TAC THENL
     [REWRITE_TAC[GSYM EXP_ADD] THEN AP_TERM_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[ARITH_RULE `r + (a * b) * c = (b * c) * a + r:num`] THEN
    SIMP_TAC[DIV_MULT_ADD; EXP_EQ_0; ARITH_EQ] THEN
    REWRITE_TAC[ODD_ADD; ODD_MULT; ODD_EXP; ARITH] THEN
    ASM_SIMP_TAC[ARITH_RULE `i < L ==> ~(L - i = 0)`];
    ALL_TAC] THEN
  REWRITE_TAC[testbit; LENGTH; GSYM ONE; SUB_REFL; SUB_0; EL; HD] THEN
  REWRITE_TAC[ARITH_RULE `i - L < 1 <=> i - L = 0`] THEN
  SUBGOAL_THEN `2 EXP i = 2 EXP L * 2 EXP (i - L)` SUBST1_TAC THENL
   [REWRITE_TAC[GSYM EXP_ADD] THEN AP_TERM_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[GSYM DIV_DIV] THEN
  REWRITE_TAC[ARITH_RULE `r + a * b = b * a + r:num`] THEN
  SIMP_TAC[DIV_MULT_ADD; EXP_EQ_0; ARITH_EQ] THEN
  ASM_SIMP_TAC[DIV_LT; ADD_CLAUSES] THEN
  ASM_CASES_TAC `i - L = 0` THEN ASM_REWRITE_TAC[EXP; DIV_1; ODD_BITVAL] THEN
  SUBGOAL_THEN `bitval h DIV 2 EXP (i - L) = 0` (fun th -> REWRITE_TAC[th; ODD]) THEN
  MATCH_MP_TAC DIV_LT THEN TRANS_TAC LTE_TRANS `2` THEN
  REWRITE_TAC[BITVAL_BOUND_ALT] THEN
  MATCH_MP_TAC(ARITH_RULE `2 EXP 1 <= x ==> 2 <= x`) THEN
  REWRITE_TAC[LE_EXP] THEN ASM_ARITH_TAC);;

let n2w_v2n = prove
 (`!v. word (v2n v):N word = v2w v`,
  REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD; bit_v2w; LSTRAUX_ODD_V2N_DIV]);;

let v2w_NIL = prove
 (`v2w [] = word 0:N word`,
  REWRITE_TAC[GSYM n2w_v2n; v2n]);;

let LSTRAUX_V2N_N2V_LEM = prove
 (`!l. ALL ((>) 2) l ==>
       MAP ((\b. if b then 1 else 0) o (\n. ~(n = 0))) l = l`,
  LIST_INDUCT_TAC THEN ASM_SIMP_TAC[ALL; MAP; o_THM; CONS_11; GT] THEN
  REPEAT STRIP_TAC THEN ASM_ARITH_TAC);;

let v2n_n2v = prove
 (`!n. v2n (n2v n) = n`,
  GEN_TAC THEN
  REWRITE_TAC[v2n_def; n2v_def; bitify_reverse_map; boolify_reverse_map;
              APPEND_NIL; MAP_REVERSE; REVERSE_REVERSE; GSYM MAP_o] THEN
  MP_TAC(SPECL [`2`; `n:num`] n2l_BOUND) THEN REWRITE_TAC[ARITH] THEN
  DISCH_THEN(SUBST1_TAC o MATCH_MP LSTRAUX_V2N_N2V_LEM) THEN
  SIMP_TAC[l2n_n2l; ARITH]);;

let v2w_n2v = prove
 (`!n. v2w (n2v n) = word n:N word`,
  REWRITE_TAC[GSYM n2w_v2n; v2n_n2v]);;

let w2n_v2w = prove
 (`!v. val (v2w v:N word) = MOD_2EXP (dimindex(:N)) (v2n v)`,
  REWRITE_TAC[GSYM n2w_v2n; VAL_WORD; MOD_2EXP_def]);;

(* ------------------------------------------------------------------------- *)
(* HOL4 export_rewrites.                                                     *)
(* ------------------------------------------------------------------------- *)

let _ = cake_add_simps
  [length_w2v; length_fixwidth; length_field; length_bitify; length_shiftr;
   v2w_w2v; v2n_n2v; v2w_n2v; fixwidth_fixwidth; fixwidth_id_imp];;

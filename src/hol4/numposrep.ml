(* ========================================================================= *)
(* numposrep: port of HOL4 src/list/src/numposrepScript.sml (the HOL4        *)
(* library of CakeML v3479): positional representation of numbers as         *)
(* digit lists, least significant digit first (l2n, n2l).                    *)
(* HOL4 EVERY ($> b) l is ALL ((>) b) l; the HOL4 power of b to n is         *)
(* b EXP n.  LOG (logroot) is the constant of hol4/words4.ml.  Helper lemmas *)
(* that are not HOL4 theorems have the prefix LSTRAUX_.                      *)
(* ========================================================================= *)

needs "hol4/vocab.ml";;
needs "hol4/words4.ml";;

prioritize_num();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* logroot LOG: the recursion equations used below (other unit's theory).    *)
(* ------------------------------------------------------------------------- *)

let LSTRAUX_LOG_UNIQUE = prove
 (`!b n k. 1 < b /\ b EXP k <= n /\ n < b EXP SUC k ==> LOG b n = k`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`b:num`; `n:num`] LOG) THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC LTE_TRANS THEN
    EXISTS_TAC `b EXP k` THEN ASM_REWRITE_TAC[EXP_LT_0] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `b EXP LOG b n < b EXP SUC k /\ b EXP k < b EXP SUC (LOG b n)`
  MP_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[LT_EXP] THEN ASM_ARITH_TAC);;

let LSTRAUX_LOG_LT = prove
 (`!b n. n < b ==> LOG b n = 0`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[LOG_DEF] THEN
  MATCH_MP_TAC MINIMAL_UNIQUE THEN BETA_TAC THEN
  ASM_REWRITE_TAC[EXP; MULT_CLAUSES; LT]);;

let LSTRAUX_LOG_DIV = prove
 (`!b n. 1 < b /\ b <= n ==> LOG b n = SUC (LOG b (n DIV b))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC LSTRAUX_LOG_UNIQUE THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `~(b = 0)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `0 < n DIV b` ASSUME_TAC THENL
   [ASM_SIMP_TAC[LE_RDIV_EQ; ARITH_RULE `0 < m <=> 1 <= m`] THEN
    ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`b:num`; `n DIV b`] LOG) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN ONCE_REWRITE_TAC[EXP] THEN CONJ_TAC THENL
   [TRANS_TAC LE_TRANS `b * n DIV b` THEN
    ASM_REWRITE_TAC[LE_MULT_LCANCEL; DIV_MUL_LE];
    ASM_SIMP_TAC[GSYM RDIV_LT_EQ]]);;

(* ------------------------------------------------------------------------- *)
(* l2n and n2l.                                                              *)
(* ------------------------------------------------------------------------- *)

let l2n_def = new_recursive_definition list_RECURSION
  `(!b. l2n b [] = 0) /\
   (!b h t. l2n b (CONS h t) = h MOD b + b * l2n b t)`;;

let n2l_def = cake_def_wf `MEASURE (SND:num#num->num)`
  (REWRITE_TAC(SND::WF_REL_THMS) THEN REWRITE_TAC[DE_MORGAN_THM; NOT_LT] THEN
   REPEAT STRIP_TAC THEN
   ASM_SIMP_TAC[RDIV_LT_EQ; ARITH_RULE `2 <= b ==> ~(b = 0)`] THEN
   SUBGOAL_THEN `2 * n <= b * n` MP_TAC THENL
    [ASM_REWRITE_TAC[LE_MULT_RCANCEL]; ASM_ARITH_TAC])
  `n2l b n = if n < b \/ b < 2 then [n MOD b]
             else CONS (n MOD b) (n2l b (n DIV b))`;;

let n2l_ind = cake_ind "n2l";;

let num_from_bin_list_def = new_definition
  `num_from_bin_list = l2n 2 o REVERSE`;;

let num_from_oct_list_def = new_definition
  `num_from_oct_list = l2n 8 o REVERSE`;;

let num_from_dec_list_def = new_definition
  `num_from_dec_list = l2n 10 o REVERSE`;;

let num_from_hex_list_def = new_definition
  `num_from_hex_list = l2n 16 o REVERSE`;;

let num_to_bin_list_def = new_definition
  `num_to_bin_list = REVERSE o n2l 2`;;

let num_to_oct_list_def = new_definition
  `num_to_oct_list = REVERSE o n2l 8`;;

let num_to_dec_list_def = new_definition
  `num_to_dec_list = REVERSE o n2l 10`;;

let num_to_hex_list_def = new_definition
  `num_to_hex_list = REVERSE o n2l 16`;;

(* ------------------------------------------------------------------------- *)
(* Basic properties.                                                         *)
(* ------------------------------------------------------------------------- *)

let LENGTH_n2l = prove
 (`!b n. 1 < b ==> LENGTH (n2l b n) = if n = 0 then 1 else SUC (LOG b n)`,
  MATCH_MP_TAC n2l_ind THEN REPEAT GEN_TAC THEN
  DISCH_THEN(LABEL_TAC "ih") THEN DISCH_TAC THEN
  ONCE_REWRITE_TAC[n2l_def] THEN ASM_SIMP_TAC[ARITH_RULE `1 < b ==> ~(b < 2)`] THEN
  ASM_CASES_TAC `n < b` THEN ASM_REWRITE_TAC[LENGTH] THENL
   [COND_CASES_TAC THEN ASM_SIMP_TAC[LSTRAUX_LOG_LT] THEN ARITH_TAC; ALL_TAC] THEN
  REMOVE_THEN "ih" MP_TAC THEN ASM_SIMP_TAC[ARITH_RULE `1 < b ==> ~(b < 2)`] THEN
  DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN `~(n DIV b = 0) /\ ~(n = 0)` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[DIV_EQ_0; ARITH_RULE `1 < b ==> ~(b = 0)`] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[LSTRAUX_LOG_DIV; ARITH_RULE `~(n < b) ==> b <= n`]);;

let l2n_n2l = prove
 (`!b n. 1 < b ==> l2n b (n2l b n) = n`,
  MATCH_MP_TAC n2l_ind THEN REPEAT GEN_TAC THEN
  DISCH_THEN(LABEL_TAC "ih") THEN DISCH_TAC THEN
  SUBGOAL_THEN `~(b = 0)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ONCE_REWRITE_TAC[n2l_def] THEN ASM_SIMP_TAC[ARITH_RULE `1 < b ==> ~(b < 2)`] THEN
  ASM_CASES_TAC `n < b` THEN ASM_SIMP_TAC[l2n_def; MOD_MOD_REFL; MOD_LT] THENL
   [ARITH_TAC; ALL_TAC] THEN
  REMOVE_THEN "ih" MP_TAC THEN ASM_SIMP_TAC[ARITH_RULE `1 < b ==> ~(b < 2)`] THEN
  DISCH_THEN SUBST1_TAC THEN
  MP_TAC(SPECL [`n:num`; `b:num`] DIVISION) THEN ASM_REWRITE_TAC[] THEN
  ARITH_TAC);;

let l2n_lt = prove
 (`!l b. 0 < b ==> l2n b l < b EXP LENGTH l`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[l2n_def; LENGTH; EXP] THEN
  REPEAT STRIP_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `b:num`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `b * (l2n b t + 1) <= b * b EXP LENGTH (t:num list)` MP_TAC THENL
   [ASM_REWRITE_TAC[LE_MULT_LCANCEL] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`h:num`; `b:num`] MOD_LT_EQ) THEN
  ASM_SIMP_TAC[ARITH_RULE `0 < b ==> ~(b = 0)`; LEFT_ADD_DISTRIB] THEN
  ARITH_TAC);;

let n2l_BOUND = prove
 (`!b n. 0 < b ==> ALL ((>) b) (n2l b n)`,
  MATCH_MP_TAC n2l_ind THEN REPEAT GEN_TAC THEN
  DISCH_THEN(LABEL_TAC "ih") THEN DISCH_TAC THEN
  ONCE_REWRITE_TAC[n2l_def] THEN COND_CASES_TAC THEN
  ASM_SIMP_TAC[ALL; GT; MOD_LT_EQ; ARITH_RULE `0 < b ==> ~(b = 0)`] THEN
  REMOVE_THEN "ih" MP_TAC THEN ASM_REWRITE_TAC[]);;

let l2n_APPEND = prove
 (`!b l1 l2. l2n b (APPEND l1 l2) = l2n b l1 + b EXP (LENGTH l1) * l2n b l2`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[APPEND; l2n_def; LENGTH; EXP] THEN ARITH_TAC);;

let LSTRAUX_N2L_LT = prove
 (`!b n. n < b ==> n2l b n = [n]`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[n2l_def] THEN ASM_SIMP_TAC[MOD_LT]);;

let LSTRAUX_N2L_0 = prove
 (`!b. n2l b 0 = [0]`,
  GEN_TAC THEN ONCE_REWRITE_TAC[n2l_def] THEN
  ASM_CASES_TAC `b = 0` THEN ASM_REWRITE_TAC[MOD_ZERO; MOD_0; ARITH] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

let LSTRAUX_N2L_STEP = prove
 (`!b n. 1 < b /\ b <= n ==> n2l b n = CONS (n MOD b) (n2l b (n DIV b))`,
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC LAND_CONV [n2l_def] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

(* HOL4 proves it from l2n_DIGIT and EL_n2l; here by induction on l          *)

let n2l_l2n = prove
 (`!b l. 1 < b /\ ALL ((>) b) l ==>
         n2l b (l2n b l) =
         if l2n b l = 0 then [0] else TAKE (SUC (LOG b (l2n b l))) l`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[l2n_def; LSTRAUX_N2L_0; ALL; GT] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[MOD_LT] THEN
  ABBREV_TAC `m = l2n b t` THEN DISCH_TAC THEN
  ASM_CASES_TAC `h + b * m = 0` THEN ASM_REWRITE_TAC[LSTRAUX_N2L_0] THEN
  REWRITE_TAC[TAKE_DEF; NOT_SUC; SUC_SUB1] THEN
  ASM_CASES_TAC `m = 0` THENL
   [UNDISCH_TAC `~(h + b * m = 0)` THEN ASM_REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES] THEN
    DISCH_TAC THEN ASM_SIMP_TAC[LSTRAUX_N2L_LT; LSTRAUX_LOG_LT] THEN
    REWRITE_TAC[TAKE_DEF] THEN
    STRUCT_CASES_TAC(ISPEC `t:num list` list_CASES) THEN REWRITE_TAC[TAKE_DEF];
    ALL_TAC] THEN
  SUBGOAL_THEN `b <= h + b * m` ASSUME_TAC THENL
   [MATCH_MP_TAC(ARITH_RULE `b * 1 <= b * m ==> b <= h + b * m`) THEN
    REWRITE_TAC[LE_MULT_LCANCEL] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(h + b * m) MOD b = h /\ (h + b * m) DIV b = m` STRIP_ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[ARITH_RULE `h + b * m = m * b + h`] THEN
    ASM_SIMP_TAC[MOD_MULT_ADD; DIV_MULT_ADD; MOD_LT; DIV_LT;
                 ARITH_RULE `1 < b ==> ~(b = 0)`; ADD_CLAUSES];
    ALL_TAC] THEN
  ASM_SIMP_TAC[LSTRAUX_N2L_STEP; LSTRAUX_LOG_DIV; CONS_11]);;

let LSTRAUX_NUM_LIST_TAC =
  REWRITE_TAC[FUN_EQ_THM; o_THM; I_THM; REVERSE_REVERSE;
              num_from_bin_list_def; num_from_oct_list_def;
              num_from_dec_list_def; num_from_hex_list_def;
              num_to_bin_list_def; num_to_oct_list_def;
              num_to_dec_list_def; num_to_hex_list_def] THEN
  SIMP_TAC[l2n_n2l; ARITH];;

let num_bin_list = prove
 (`num_from_bin_list o num_to_bin_list = I`,
  LSTRAUX_NUM_LIST_TAC);;

let num_oct_list = prove
 (`num_from_oct_list o num_to_oct_list = I`,
  LSTRAUX_NUM_LIST_TAC);;

let num_dec_list = prove
 (`num_from_dec_list o num_to_dec_list = I`,
  LSTRAUX_NUM_LIST_TAC);;

let num_hex_list = prove
 (`num_from_hex_list o num_to_hex_list = I`,
  LSTRAUX_NUM_LIST_TAC);;

(* ========================================================================= *)
(* multiword: port of HOL4 examples/machine-code/multiword/multiwordScript.sml *)
(* (HOL4 library used by CakeML v3479): bignum arithmetic on lists of words *)
(* (least significant word first): mw2n, n2mw, i2mw, add, sub, mul, the     *)
(* long division mw_div (Knuth's algorithm D) and the integer operations    *)
(* mwi_op with their correctness theorem mwi_op_thm.                        *)
(*                                                                           *)
(* Vocabulary (words4.ml): 'a word = N word, n2w = word, w2n = val,          *)
(* dimword(:'a) = dimword(:N); HOL4 b2n is HOL Light's bitval; Num (ABS i)   *)
(* is num_of_int (abs i); int / and % are int_div and integer_int_mod.       *)
(* HOL4's let (a,b) = e in t is written with match (pair_CASE).             *)
(* Prefixed names (taken by HOL Light or by CakeML names to come):           *)
(*   multiword_b2w_def (the theory's b2w_def), multiword_LESS_EQ_LENGTH,     *)
(*   multiword_int_op (constant; its definition theorem is int_op_def), and  *)
(*   the constructors of mw_op: multiword_Add multiword_Sub multiword_Mul    *)
(*   multiword_Div multiword_Mod multiword_Lt Eq multiword_Dec.              *)
(* HOL4's variable mod (mw_div, mwi_divmod) is md (mod is a HOL Light        *)
(* constant).  HOL4's induction theorems calc_d_ind and mw_div_test_ind are  *)
(* proved here (the kit gives none for these two definitions).               *)
(* Proof route: the correctness of mw_div is proved directly from an         *)
(* invariant of mw_div_aux and the quotient digit lemma LBIGAUX_DIGIT        *)
(* (guess, test and adjust give exactly the quotient digit), not through     *)
(* HOL4's mw_div_loop (not ported, nor mw_div_by_single, the decimal         *)
(* printing mw_to_dec and the lemmas that only these use).                   *)
(* Helpers are named LBIGAUX_...                                             *)
(* ========================================================================= *)

needs "hol4/vocab.ml";;
needs "hol4/basic.ml";;
needs "hol4/list.ml";;
needs "hol4/rich_list.ml";;
needs "hol4/words4.ml";;

prioritize_num();;
type_invention_error := true;;
(* ------------------------------------------------------------------------- *)
(* general                                                                   *)
(* ------------------------------------------------------------------------- *)

(* HOL4 b2n is HOL Light's bitval (Library/words.ml) *)

let b2n_def = prove
 (`(bitval T = 1) /\ (bitval F = 0)`,
  REWRITE_TAC[bitval]);;

let multiword_b2w_def = new_definition
  `b2w c = word (bitval c):N word`;;

let LBIGAUX_MULT_ADD_LESS_MULT = prove
 (`!m n k l j. m < l /\ n < k /\ j <= k ==> m * j + n < l * k`,
  REPEAT STRIP_TAC THEN TRANS_TAC LTE_TRANS `m * k + k` THEN CONJ_TAC THENL
   [MATCH_MP_TAC(ARITH_RULE `a <= b /\ n < k ==> a + n < b + k`) THEN
    ASM_REWRITE_TAC[LE_MULT_LCANCEL];
    REWRITE_TAC[ARITH_RULE `m * k + k = SUC m * k`; LE_MULT_RCANCEL] THEN
    ASM_ARITH_TAC]);;

let LBIGAUX_MULT_ADD_LESS_MULT_ADD = prove
 (`!m n k l p. m < l /\ n < k /\ p < k ==> m * k + n < l * k + p`,
  REPEAT STRIP_TAC THEN TRANS_TAC LTE_TRANS `m * k + k` THEN CONJ_TAC THENL
   [ASM_ARITH_TAC;
    MATCH_MP_TAC(ARITH_RULE `a <= b ==> a <= b + p`) THEN
    REWRITE_TAC[ARITH_RULE `m * k + k = SUC m * k`; LE_MULT_RCANCEL] THEN
    ASM_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* multiword related general                                                 *)
(* ------------------------------------------------------------------------- *)

let dimwords_def = new_definition
  `dimwords k (n:N->bool) = 2 EXP (k * dimindex n)`;;

let k2mw_def = cake_def
  `(k2mw 0 n = []:(N word)list) /\
   (k2mw (SUC l) n = CONS (word n) (k2mw l (n DIV dimword(:N))))`;;

let mw2n_def = cake_def
  `(mw2n ([]:(N word)list) = 0) /\
   (mw2n (CONS (x:N word) xs) = val x + dimword(:N) * mw2n xs)`;;

let mw2i_DEF = new_definition
  `mw2i (s,xs:(N word)list) = if s then --(&(mw2n xs)) else &(mw2n xs):int`;;

let mw2i_def = prove
 (`(!xs:(N word)list. mw2i (F,xs) = &(mw2n xs)) /\
   (!xs:(N word)list. mw2i (T,xs) = --(&(mw2n xs)))`,
  REWRITE_TAC[mw2i_DEF]);;

let n2mw_def = cake_def_wf `MEASURE (I:num->num)`
  (REWRITE_TAC(I_THM::WF_REL_THMS) THEN REPEAT STRIP_TAC THEN
   MATCH_MP_TAC DIV_LESS THEN REWRITE_TAC[ONE_LT_dimword] THEN ASM_ARITH_TAC)
  `n2mw n = if n = 0 then []:(N word)list
            else CONS (word (n MOD dimword(:N))) (n2mw (n DIV dimword(:N)))`;;

let n2mw_ind = cake_ind "n2mw";;

let i2mw_def = new_definition
  `i2mw i = ((i < &0), (n2mw (num_of_int (abs i)):(N word)list))`;;

let mw_ok_def = new_definition
  `mw_ok (xs:(N word)list) <=> ~(xs = []) ==> ~(LAST xs = word 0)`;;
let LBIGAUX_DIMWORD_NZ = prove
 (`~(dimword(:N) = 0)`,
  MP_TAC ZERO_LT_dimword THEN ARITH_TAC);;

let LBIGAUX_VAL_DIVMOD = prove
 (`!(h:N word) m. (val h + dimword(:N) * m) DIV dimword(:N) = m /\
                  (val h + dimword(:N) * m) MOD dimword(:N) = val h`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC DIVMOD_UNIQ THEN
  REWRITE_TAC[w2n_lt] THEN ARITH_TAC);;

let LBIGAUX_WORD_VAL_ADD = prove
 (`!(h:N word) m. word (val h + dimword(:N) * m):N word = h`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[GSYM n2w_mod] THEN
  REWRITE_TAC[LBIGAUX_VAL_DIVMOD; WORD_VAL]);;

let ZERO_LT_dimwords = prove
 (`!k. 0 < dimwords k (:N)`,
  REWRITE_TAC[dimwords_def; EXP_LT_0] THEN ARITH_TAC);;

let dimwords_SUC = prove
 (`!k. dimwords (SUC k) (:N) = dimwords k (:N) * dimword(:N)`,
  REWRITE_TAC[dimwords_def; dimword_def; MULT_CLAUSES; EXP_ADD]);;

let dimwords_thm = prove
 (`dimwords 0 (:N) = 1 /\
   (!k. dimwords (SUC k) (:N) = dimword(:N) * dimwords k (:N))`,
  REWRITE_TAC[dimwords_SUC; MULT_SYM] THEN
  REWRITE_TAC[dimwords_def; MULT_CLAUSES; EXP]);;

let mw_ok_CLAUSES = prove
 (`mw_ok ([]:(N word)list) /\
   (!(x:N word) xs. mw_ok (CONS x xs) <=> (xs = [] ==> ~(x = word 0)) /\ mw_ok xs)`,
  REWRITE_TAC[mw_ok_def; NOT_CONS_NIL; LAST] THEN REPEAT GEN_TAC THEN
  ASM_CASES_TAC `xs:(N word)list = []` THEN ASM_REWRITE_TAC[]);;

let k2mw_mw2n = prove
 (`!xs:(N word)list. k2mw (LENGTH xs) (mw2n xs) = xs`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[LENGTH; mw2n_def; k2mw_def; LBIGAUX_VAL_DIVMOD; CONS_11;
                  LBIGAUX_WORD_VAL_ADD]);;

let LENGTH_k2mw = prove
 (`!k n. LENGTH (k2mw k n:(N word)list) = k`,
  INDUCT_TAC THEN ASM_REWRITE_TAC[k2mw_def; LENGTH]);;

let k2mw_mod = prove
 (`!k m. k2mw k (m MOD dimwords k (:N)):(N word)list = k2mw k m`,
  INDUCT_TAC THEN REWRITE_TAC[k2mw_def; CONS_11] THEN GEN_TAC THEN
  REWRITE_TAC[dimwords_thm; GSYM DIV_MOD] THEN
  ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[GSYM n2w_mod] THEN
  REWRITE_TAC[MOD_MOD]);;

let mw2n_APPEND = prove
 (`!xs ys. mw2n (APPEND xs ys) =
           mw2n xs + dimwords (LENGTH xs) (:N) * mw2n (ys:(N word)list)`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[APPEND; mw2n_def; LENGTH; dimwords_thm] THEN ARITH_TAC);;

let mw2n_lt = prove
 (`!xs:(N word)list. mw2n xs < dimwords (LENGTH xs) (:N)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[LENGTH; dimwords_thm; mw2n_def] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  MP_TAC(SPECL [`mw2n (t:(N word)list)`; `val (h:N word)`; `dimword(:N)`;
                `dimwords (LENGTH (t:(N word)list)) (:N)`; `dimword(:N)`]
         LBIGAUX_MULT_ADD_LESS_MULT) THEN
  ASM_REWRITE_TAC[w2n_lt; LE_REFL] THEN ARITH_TAC);;
let mw2n_MAP_ZERO = prove
 (`!xs (ys:B list).
     mw2n (APPEND xs (MAP (\x. word 0) ys)) = mw2n (xs:(N word)list)`,
  LIST_INDUCT_TAC THENL
   [REWRITE_TAC[APPEND] THEN LIST_INDUCT_TAC THEN
    ASM_REWRITE_TAC[MAP; mw2n_def; VAL_WORD_0] THEN ARITH_TAC;
    ASM_REWRITE_TAC[APPEND; mw2n_def]]);;

let LBIGAUX_DIMWORDS_LT = prove
 (`!a b. dimwords a (:N) < dimwords b (:N) <=> a < b`,
  REWRITE_TAC[dimwords_def; WORDSAUX_EXP2_LT; LT_MULT_RCANCEL] THEN
  MP_TAC(ISPEC `(:N)` DIMINDEX_GE_1) THEN ARITH_TAC);;

let LBIGAUX_DIMWORDS_LE = prove
 (`!a b. dimwords a (:N) <= dimwords b (:N) <=> a <= b`,
  REWRITE_TAC[GSYM NOT_LT; LBIGAUX_DIMWORDS_LT]);;

let mw2n_gt = prove
 (`!xs:(N word)list.
     mw_ok xs /\ ~(xs = []) ==> dimwords (LENGTH xs - 1) (:N) <= mw2n xs`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[NOT_CONS_NIL; mw_ok_CLAUSES] THEN
  ASM_CASES_TAC `t:(N word)list = []` THEN ASM_REWRITE_TAC[LENGTH; mw2n_def] THENL
   [REWRITE_TAC[ARITH_RULE `SUC 0 - 1 = 0`; dimwords_thm; MULT_CLAUSES;
                ADD_CLAUSES; GSYM VAL_EQ_0] THEN ARITH_TAC;
    STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `SUC (LENGTH (t:(N word)list)) - 1 = SUC (LENGTH t - 1)`
    SUBST1_TAC THENL
     [MP_TAC(ISPEC `t:(N word)list` LENGTH_EQ_NIL) THEN ASM_REWRITE_TAC[] THEN
      ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[dimwords_thm] THEN DISCH_TAC THEN
    MATCH_MP_TAC(ARITH_RULE `a <= b ==> a <= c + b`) THEN
    ASM_REWRITE_TAC[LE_MULT_LCANCEL]]);;

let mw2n_LESS = prove
 (`!(xs:(N word)list) (ys:(N word)list).
     mw_ok xs /\ mw_ok ys /\ mw2n xs <= mw2n ys ==> LENGTH xs <= LENGTH ys`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `xs:(N word)list = []` THEN ASM_REWRITE_TAC[LENGTH; LE_0] THEN
  MP_TAC(ISPEC `xs:(N word)list` mw2n_gt) THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `dimwords (LENGTH (xs:(N word)list) - 1) (:N) <
                dimwords (LENGTH (ys:(N word)list)) (:N)` MP_TAC THENL
   [MP_TAC(ISPEC `ys:(N word)list` mw2n_lt) THEN ASM_ARITH_TAC;
    REWRITE_TAC[LBIGAUX_DIMWORDS_LT] THEN ARITH_TAC]);;

let n2mw_NIL = prove
 (`!n. (n2mw n:(N word)list = []) <=> n = 0`,
  GEN_TAC THEN ONCE_REWRITE_TAC[n2mw_def] THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[NOT_CONS_NIL]);;

let mw_ok_n2mw = prove
 (`!n. mw_ok (n2mw n:(N word)list)`,
  MATCH_MP_TAC n2mw_ind THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  ONCE_REWRITE_TAC[n2mw_def] THEN COND_CASES_TAC THEN
  ASM_SIMP_TAC[mw_ok_CLAUSES; n2mw_NIL; DIV_EQ_0; LBIGAUX_DIMWORD_NZ] THEN
  DISCH_TAC THEN ASM_SIMP_TAC[MOD_LT; n2w_11; MOD_0]);;

let mw2n_n2mw = prove
 (`!n. mw2n (n2mw n:(N word)list) = n`,
  MATCH_MP_TAC n2mw_ind THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  ONCE_REWRITE_TAC[n2mw_def] THEN COND_CASES_TAC THEN
  ASM_SIMP_TAC[mw2n_def; w2n_n2w; MOD_MOD_REFL] THEN
  MP_TAC(SPECL [`n:num`; `dimword(:N)`] DIVISION) THEN
  REWRITE_TAC[LBIGAUX_DIMWORD_NZ] THEN ARITH_TAC);;

let LBIGAUX_NUM_ABS = prove
 (`!i:int. &(num_of_int (abs i)) = abs i`,
  SIMP_TAC[INT_OF_NUM_OF_INT; INT_ABS_POS]);;

let mw2i_i2mw = prove
 (`!i. mw2i (i2mw i:bool#(N word)list) = i`,
  REWRITE_TAC[i2mw_def; mw2i_DEF; mw2n_n2mw; LBIGAUX_NUM_ABS] THEN
  INT_ARITH_TAC);;

let n2mw_11 = prove
 (`!m n. (n2mw m:(N word)list = n2mw n) <=> m = n`,
  MESON_TAC[mw2n_n2mw]);;

let mw_ok_mw_mw2n = prove
 (`!xs:(N word)list. mw_ok xs ==> xs = n2mw (mw2n xs)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[mw2n_def; mw_ok_CLAUSES] THENL
   [ONCE_REWRITE_TAC[n2mw_def] THEN REWRITE_TAC[]; ALL_TAC] THEN
  POP_ASSUM(LABEL_TAC "ih") THEN STRIP_TAC THEN
  REMOVE_THEN "ih" MP_TAC THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  GEN_REWRITE_TAC RAND_CONV [n2mw_def] THEN
  REWRITE_TAC[LBIGAUX_VAL_DIVMOD; WORD_VAL] THEN
  SUBGOAL_THEN `~(val (h:N word) + dimword(:N) * mw2n (t:(N word)list) = 0)`
    (fun th -> REWRITE_TAC[th]) THENL
   [ALL_TAC; ASM_MESON_TAC[]] THEN
  ASM_CASES_TAC `t:(N word)list = []` THENL
   [UNDISCH_TAC `t:(N word)list = [] ==> ~(h:N word = word 0)` THEN
    ASM_REWRITE_TAC[mw2n_def; GSYM VAL_EQ_0] THEN ARITH_TAC;
    SUBGOAL_THEN `~(mw2n (t:(N word)list) = 0)` MP_TAC THENL
     [ASM_MESON_TAC[n2mw_NIL]; ALL_TAC] THEN
    REWRITE_TAC[ADD_EQ_0; MULT_EQ_0; LBIGAUX_DIMWORD_NZ] THEN CONV_TAC TAUT]);;

let IMP_EQ_n2mw = prove
 (`!(xs:(N word)list) i. mw_ok xs /\ mw2n xs = i ==> xs = n2mw i`,
  MESON_TAC[mw_ok_mw_mw2n]);;

let IMP_EQ_n2mw_ALT = prove
 (`!xs ys:(N word)list. mw_ok xs /\ mw_ok ys /\ mw2n xs = mw2n ys ==> xs = ys`,
  MESON_TAC[mw_ok_mw_mw2n]);;

let mw_ok_IMP_EXISTS_n2mw = prove
 (`!xs:(N word)list. mw_ok xs ==> ?n. xs = n2mw n`,
  MESON_TAC[mw_ok_mw_mw2n]);;

let mw2i_EQ_IMP_EQ_i2mw = prove
 (`!(x:bool#(N word)list) i.
     mw_ok (SND x) /\ ~(x = (T,[])) /\ mw2i x = i ==> x = i2mw i`,
  REWRITE_TAC[FORALL_PAIR_THM; PAIR_EQ] THEN
  MAP_EVERY X_GEN_TAC [`s:bool`; `xs:(N word)list`; `i:int`] THEN
  REWRITE_TAC[SND] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[i2mw_def; mw2i_DEF; PAIR_EQ] THEN
  SUBGOAL_THEN `xs = n2mw (mw2n (xs:(N word)list)):(N word)list` ASSUME_TAC THENL
   [ASM_MESON_TAC[mw_ok_mw_mw2n]; ALL_TAC] THEN
  SUBGOAL_THEN `s ==> ~(mw2n (xs:(N word)list) = 0)` ASSUME_TAC THENL
   [ASM_MESON_TAC[n2mw_NIL]; ALL_TAC] THEN
  REWRITE_TAC[COND_RAND; INT_ABS_NEG; INT_ABS_NUM; NUM_OF_INT_OF_NUM; COND_ID] THEN
  CONJ_TAC THENL [ALL_TAC; FIRST_ASSUM ACCEPT_TAC] THEN
  ASM_CASES_TAC `s:bool` THEN
  ASM_REWRITE_TAC[INT_NEG_LT0; INT_OF_NUM_LT; INT_ARITH `~(&n:int < &0)`] THEN
  UNDISCH_TAC `s ==> ~(mw2n (xs:(N word)list) = 0)` THEN ASM_REWRITE_TAC[] THEN
  ARITH_TAC);;

let LENGTH_n2mw_LESS_LENGTH_n2mw = prove
 (`!m n. m <= n ==> LENGTH (n2mw m:(N word)list) <= LENGTH (n2mw n:(N word)list)`,
  MATCH_MP_TAC n2mw_ind THEN X_GEN_TAC `m:num` THEN DISCH_TAC THEN
  X_GEN_TAC `n:num` THEN DISCH_TAC THEN ONCE_REWRITE_TAC[n2mw_def] THEN
  ASM_CASES_TAC `m = 0` THEN ASM_REWRITE_TAC[LENGTH; LE_0] THEN
  SUBGOAL_THEN `~(n = 0)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[LENGTH; LE_SUC] THEN
  FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN MATCH_MP_TAC THEN MATCH_MP_TAC DIV_MONO THEN ASM_REWRITE_TAC[]);;
(* ------------------------------------------------------------------------- *)
(* fix and zerofix                                                           *)
(* ------------------------------------------------------------------------- *)

let mw_fix_def = cake_def_wf `MEASURE (LENGTH:(N word)list->num)`
  (REWRITE_TAC WF_REL_THMS THEN REPEAT STRIP_TAC THEN
   MP_TAC(ISPEC `xs:(N word)list` LENGTH_FRONT) THEN ASM_REWRITE_TAC[] THEN
   FIRST_X_ASSUM(MP_TAC o check (is_neg o concl)) THEN
   REWRITE_TAC[GSYM LENGTH_EQ_NIL] THEN ASM_ARITH_TAC)
  `mw_fix (xs:(N word)list) =
     if xs = [] then [] else
     if LAST xs = word 0 then mw_fix (BUTLAST xs) else xs`;;

let mw_fix_ind = cake_ind "mw_fix";;

let mw_ok_fix = prove
 (`!xs:(N word)list. mw_ok (mw_fix xs)`,
  MATCH_MP_TAC mw_fix_ind THEN X_GEN_TAC `xs:(N word)list` THEN DISCH_TAC THEN
  ONCE_REWRITE_TAC[mw_fix_def] THEN
  ASM_CASES_TAC `xs:(N word)list = []` THEN ASM_REWRITE_TAC[mw_ok_CLAUSES] THEN
  COND_CASES_TAC THEN ASM_SIMP_TAC[] THEN ASM_REWRITE_TAC[mw_ok_def]);;

let mw_ok_mw_fix_ID = prove
 (`!xs:(N word)list. mw_ok xs ==> mw_fix xs = xs`,
  GEN_TAC THEN ONCE_REWRITE_TAC[mw_fix_def] THEN REWRITE_TAC[mw_ok_def] THEN
  ASM_CASES_TAC `xs:(N word)list = []` THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN ASM_REWRITE_TAC[]);;

let mw2n_mw_fix = prove
 (`!xs:(N word)list. mw2n (mw_fix xs) = mw2n xs`,
  MATCH_MP_TAC mw_fix_ind THEN X_GEN_TAC `xs:(N word)list` THEN DISCH_TAC THEN
  ONCE_REWRITE_TAC[mw_fix_def] THEN
  ASM_CASES_TAC `xs:(N word)list = []` THEN ASM_REWRITE_TAC[] THEN
  COND_CASES_TAC THEN ASM_SIMP_TAC[] THEN
  FIRST_ASSUM(fun th -> GEN_REWRITE_TAC (RAND_CONV o RAND_CONV)
    [GSYM(MATCH_MP APPEND_BUTLAST_LAST th)]) THEN
  ASM_REWRITE_TAC[mw2n_APPEND; mw2n_def; VAL_WORD_0] THEN ARITH_TAC);;

let n2mw_mw2n = prove
 (`!xs:(N word)list. mw_fix xs = n2mw (mw2n xs)`,
  MESON_TAC[mw_ok_mw_mw2n; mw_ok_fix; mw2n_mw_fix]);;

let mw_fix_NIL = prove
 (`!xs:(N word)list. mw_fix xs = [] <=> mw2n xs = 0`,
  REWRITE_TAC[n2mw_mw2n; n2mw_NIL]);;

let LENGTH_mw_fix = prove
 (`!xs:(N word)list. LENGTH (mw_fix xs) <= LENGTH xs`,
  MATCH_MP_TAC mw_fix_ind THEN X_GEN_TAC `xs:(N word)list` THEN DISCH_TAC THEN
  ONCE_REWRITE_TAC[mw_fix_def] THEN
  ASM_CASES_TAC `xs:(N word)list = []` THEN ASM_REWRITE_TAC[LE_REFL] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[LE_REFL] THEN
  TRANS_TAC LE_TRANS `LENGTH (BUTLAST (xs:(N word)list))` THEN
  ASM_SIMP_TAC[LENGTH_FRONT] THEN ARITH_TAC);;

let REPLICATE_SNOC = prove
 (`!n (x:A). REPLICATE (SUC n) x = SNOC x (REPLICATE n x)`,
  REWRITE_TAC[SNOC_REPLICATE]);;

let mw_fix_thm = prove
 (`!xs:(N word)list.
     APPEND (mw_fix xs) (REPLICATE (LENGTH xs - LENGTH (mw_fix xs)) (word 0)) = xs`,
  MATCH_MP_TAC mw_fix_ind THEN X_GEN_TAC `xs:(N word)list` THEN DISCH_TAC THEN
  ONCE_REWRITE_TAC[mw_fix_def] THEN
  ASM_CASES_TAC `xs:(N word)list = []` THEN ASM_REWRITE_TAC[] THENL
   [REWRITE_TAC[LENGTH; SUB_REFL; REPLICATE; APPEND]; ALL_TAC] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[SUB_REFL; REPLICATE; APPEND_NIL] THEN
  FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `BUTLAST xs:(N word)list` LENGTH_mw_fix) THEN
  ABBREV_TAC `f = mw_fix (BUTLAST xs:(N word)list)` THEN
  SUBGOAL_THEN `LENGTH (xs:(N word)list) = SUC (LENGTH (BUTLAST xs))`
  SUBST1_TAC THENL
   [ASM_SIMP_TAC[LENGTH_FRONT] THEN UNDISCH_TAC `~(xs:(N word)list = [])` THEN
    REWRITE_TAC[GSYM LENGTH_EQ_NIL] THEN ARITH_TAC; ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[ARITH_RULE `b <= a ==> SUC a - b = SUC (a - b)`;
               REPLICATE_SNOC; SNOC_APPEND; APPEND_ASSOC] THEN
  FIRST_ASSUM(fun th -> GEN_REWRITE_TAC RAND_CONV
    [GSYM(MATCH_MP APPEND_BUTLAST_LAST th)]) THEN
  ASM_REWRITE_TAC[]);;

let mw2n_REPLICATE = prove
 (`!n. mw2n (REPLICATE n (word 0):(N word)list) = 0`,
  INDUCT_TAC THEN ASM_REWRITE_TAC[REPLICATE; mw2n_def; VAL_WORD_0] THEN
  ARITH_TAC);;
(* ------------------------------------------------------------------------- *)
(* add/sub                                                                   *)
(* ------------------------------------------------------------------------- *)

let single_add_def = new_definition
  `single_add (x:N word) (y:N word) c =
     (word_add (word_add x y) (b2w c),
      (dimword(:N) <= val x + val y + bitval c))`;;

let mw_add_def = cake_def
  `(mw_add [] ys c = ([]:(N word)list,c)) /\
   (mw_add (CONS (x:N word) xs) ys c =
      match single_add x (HD ys) c with (z,c1) ->
      match mw_add xs (TL ys) c1 with (zs,c2) -> (CONS z zs,c2))`;;

let single_sub_def = new_definition
  `single_sub (x:N word) (y:N word) c = single_add x (word_not y) c`;;

let mw_sub_def = cake_def
  `(mw_sub [] ys c = ([]:(N word)list,c)) /\
   (mw_sub (CONS (x:N word) xs) [] c =
      match single_sub x (word 0) c with (z,c1) ->
      match mw_sub xs [] c1 with (zs,c2) -> (CONS z zs,c2)) /\
   (mw_sub (CONS x xs) (CONS y ys) c =
      match single_sub x y c with (z,c1) ->
      match mw_sub xs ys c1 with (zs,c2) -> (CONS z zs,c2))`;;
let LBIGAUX_VAL_B2W = prove
 (`!c. val(b2w c:N word) = bitval c`,
  GEN_TAC THEN REWRITE_TAC[multiword_b2w_def; w2n_n2w] THEN
  MATCH_MP_TAC MOD_LT THEN MP_TAC ONE_LT_dimword THEN
  MP_TAC(SPEC `c:bool` BITVAL_BOUND) THEN ARITH_TAC);;

let LBIGAUX_SINGLE_ADD_WORD = prove
 (`!(x:N word) y c.
     word_add (word_add x y) (b2w c) = word (val x + val y + bitval c)`,
  REWRITE_TAC[multiword_b2w_def] THEN CONV_TAC WORD_RULE);;

let single_add_thm = prove
 (`!(x:N word) y z c d.
     single_add x y c = (z,d)
     ==> val z + dimword(:N) * bitval d = val x + val y + bitval c`,
  REWRITE_TAC[single_add_def; PAIR_EQ; LBIGAUX_SINGLE_ADD_WORD] THEN
  REPEAT STRIP_TAC THEN REPEAT(FIRST_X_ASSUM(SUBST1_TAC o SYM)) THEN
  SUBGOAL_THEN `val (x:N word) + val (y:N word) + bitval c < 2 * dimword(:N)`
  ASSUME_TAC THENL
   [MP_TAC(ISPEC `x:N word` w2n_lt) THEN MP_TAC(ISPEC `y:N word` w2n_lt) THEN
    MP_TAC(SPEC `c:bool` BITVAL_BOUND) THEN ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[MOD_CASES; w2n_n2w] THEN REWRITE_TAC[bitval] THEN
  REPEAT COND_CASES_TAC THEN ASM_ARITH_TAC);;
let mw_add_thm = prove
 (`!xs ys c (zs:(N word)list) d.
     mw_add xs ys c = (zs,d) /\ LENGTH xs = LENGTH ys
     ==> mw2n zs + dimwords (LENGTH xs) (:N) * bitval d =
         mw2n xs + mw2n ys + bitval c`,
  LIST_INDUCT_TAC THEN X_GEN_TAC `ys:(N word)list` THEN
  CASES_ON `ys:(N word)list` THEN
  REWRITE_TAC[mw_add_def; LENGTH; HD; TL; ARITH_RULE
    `~(SUC n = 0) /\ ~(0 = SUC n) /\ (SUC m = SUC n <=> m = n)`] THENL
   [REWRITE_TAC[PAIR_EQ] THEN REPEAT STRIP_TAC THEN
    REPEAT(FIRST_X_ASSUM(SUBST1_TAC o SYM)) THEN
    REWRITE_TAC[mw2n_def; dimwords_thm] THEN ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`c:bool`; `zs:(N word)list`; `d:bool`] THEN
  PAIRARG_TAC THEN PAIRARG_TAC THEN REWRITE_TAC[PAIR_EQ] THEN
  STRIP_TAC THEN REPEAT VAR_EQ_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
    [`a1:(N word)list`; `c1:bool`; `zs':(N word)list`; `d:bool`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o AP_TERM `( * ) (dimword(:N))`) THEN
  MP_TAC(SPECL [`h:N word`; `a0:N word`; `z:N word`; `c:bool`; `c1:bool`]
         single_add_thm) THEN
  ASM_REWRITE_TAC[mw2n_def; dimwords_thm] THEN ARITH_TAC);;

let single_sub_thm = prove
 (`!(x:N word) y z c d.
     single_sub x y c = (z,d)
     ==> val z + dimword(:N) * bitval d + val y =
         val x + bitval c + (dimword(:N) - 1)`,
  REWRITE_TAC[single_sub_def] THEN REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP single_add_thm) THEN
  REWRITE_TAC[VAL_WORD_NOT; GSYM dimword_def] THEN
  MP_TAC(ISPEC `y:N word` w2n_lt) THEN ARITH_TAC);;

let LENGTH_mw_sub = prove
 (`!xs1 (ys:(N word)list) c qs1 c1.
     mw_sub xs1 ys c = (qs1,c1) ==> LENGTH xs1 = LENGTH qs1`,
  LIST_INDUCT_TAC THEN X_GEN_TAC `ys:(N word)list` THEN
  CASES_ON `ys:(N word)list` THEN REWRITE_TAC[mw_sub_def] THEN
  REWRITE_TAC[PAIR_EQ] THEN REPEAT GEN_TAC THENL
   [STRIP_TAC THEN REPEAT VAR_EQ_TAC THEN REWRITE_TAC[LENGTH];
    STRIP_TAC THEN REPEAT VAR_EQ_TAC THEN REWRITE_TAC[LENGTH];
    PAIRARG_TAC THEN PAIRARG_TAC THEN REWRITE_TAC[PAIR_EQ] THEN
    STRIP_TAC THEN REPEAT VAR_EQ_TAC THEN REWRITE_TAC[LENGTH; SUC_INJ] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[];
    PAIRARG_TAC THEN PAIRARG_TAC THEN REWRITE_TAC[PAIR_EQ] THEN
    STRIP_TAC THEN REPEAT VAR_EQ_TAC THEN REWRITE_TAC[LENGTH; SUC_INJ] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[]]);;

let mw_sub_lemma = prove
 (`!xs ys c (zs:(N word)list) d.
     mw_sub xs ys c = (zs,d) /\ LENGTH xs = LENGTH ys
     ==> mw2n zs + mw2n ys + dimwords (LENGTH xs) (:N) * bitval d =
         mw2n xs + bitval c + (dimwords (LENGTH xs) (:N) - 1) /\
         LENGTH zs = LENGTH xs`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN CONJ_TAC THENL
   [ALL_TAC; ASM_MESON_TAC[LENGTH_mw_sub]] THEN
  POP_ASSUM MP_TAC THEN MAP_EVERY (fun t -> SPEC_TAC(t,t))
   [`d:bool`; `zs:(N word)list`; `c:bool`; `ys:(N word)list`; `xs:(N word)list`] THEN
  LIST_INDUCT_TAC THEN X_GEN_TAC `ys:(N word)list` THEN
  CASES_ON `ys:(N word)list` THEN
  REWRITE_TAC[mw_sub_def; LENGTH; HD; TL; ARITH_RULE
    `~(SUC n = 0) /\ ~(0 = SUC n) /\ (SUC m = SUC n <=> m = n)`] THENL
   [REWRITE_TAC[PAIR_EQ] THEN REPEAT STRIP_TAC THEN
    REPEAT(FIRST_X_ASSUM(SUBST1_TAC o SYM)) THEN
    REWRITE_TAC[mw2n_def; dimwords_thm; LENGTH] THEN ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`c:bool`; `zs:(N word)list`; `d:bool`] THEN
  PAIRARG_TAC THEN PAIRARG_TAC THEN REWRITE_TAC[PAIR_EQ] THEN
  STRIP_TAC THEN REPEAT VAR_EQ_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
    [`a1:(N word)list`; `c1:bool`; `zs':(N word)list`; `d:bool`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o AP_TERM `( * ) (dimword(:N))`) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP single_sub_thm) THEN
  REWRITE_TAC[mw2n_def; dimwords_thm] THEN
  MP_TAC(SPEC `LENGTH (t:(N word)list)` ZERO_LT_dimwords) THEN
  MP_TAC ZERO_LT_dimword THEN
  SPEC_TAC(`dimwords (LENGTH (t:(N word)list)) (:N)`,`w:num`) THEN
  SPEC_TAC(`dimword(:N)`,`k:num`) THEN
  REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `k <= k * w` MP_TAC THENL
   [GEN_REWRITE_TAC LAND_CONV [ARITH_RULE `k = k * 1`] THEN
    REWRITE_TAC[LE_MULT_LCANCEL] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  POP_ASSUM MP_TAC THEN REWRITE_TAC[LEFT_ADD_DISTRIB; LEFT_SUB_DISTRIB;
    MULT_CLAUSES; MULT_ASSOC] THEN
  ASM_ARITH_TAC);;
let mw_sub_thm = prove
 (`!xs ys:(N word)list.
     LENGTH xs = LENGTH ys /\ mw2n ys <= mw2n xs
     ==> mw2n (FST (mw_sub xs ys T)) = mw2n xs - mw2n ys`,
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(ASSUME_TAC o SYM) THEN
  MP_TAC(ISPEC `mw_sub (xs:(N word)list) ys T` PAIR_SURJECTIVE) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`zs:(N word)list`; `d:bool`] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`xs:(N word)list`; `ys:(N word)list`; `T`; `zs:(N word)list`;
                `d:bool`] mw_sub_lemma) THEN
  ASM_REWRITE_TAC[FST] THEN STRIP_TAC THEN
  MP_TAC(ISPEC `zs:(N word)list` mw2n_lt) THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(SPEC `LENGTH (xs:(N word)list)` ZERO_LT_dimwords) THEN
  POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
  BOOL_CASES_TAC `d:bool` THEN REWRITE_TAC[bitval] THEN ARITH_TAC);;

let mw_addv_def = cake_def
  `(mw_addv [] (ys:(N word)list) c = if c then [word 1] else []) /\
   (mw_addv (CONS (x:N word) xs) ys c =
      match (if ys = [] then (word 0,ys) else (HD ys,TL ys)) with (y,ys2) ->
      match single_add x y c with (z,c1) ->
        CONS z (mw_addv xs ys2 c1))`;;

let LBIGAUX_WORD_NOT_ZERO_ONE = prove
 (`~(word 0:N word = word 1)`,
  REWRITE_TAC[n2w_11] THEN MP_TAC ONE_LT_dimword THEN
  SIMP_TAC[MOD_LT; ARITH_RULE `1 < n ==> 0 < n`] THEN ARITH_TAC);;

let mw_addv_thm = prove
 (`!xs (ys:(N word)list) c.
     LENGTH ys <= LENGTH xs
     ==> mw2n (mw_addv xs ys c) = mw2n xs + mw2n ys + bitval c`,
  LIST_INDUCT_TAC THEN X_GEN_TAC `ys:(N word)list` THEN
  CASES_ON `ys:(N word)list` THEN
  REWRITE_TAC[mw_addv_def; LENGTH; NOT_CONS_NIL; HD; TL;
              ARITH_RULE `~(SUC n <= 0)`; LE_0; LE_SUC] THENL
   [GEN_TAC THEN COND_CASES_TAC THEN
    ASM_REWRITE_TAC[mw2n_def; bitval; VAL_WORD_1] THEN ARITH_TAC;
    X_GEN_TAC `c:bool` THEN CAKE_REWRITE_TAC[] THEN PAIRARG_TAC THEN
    REWRITE_TAC[mw2n_def] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`[]:(N word)list`; `c1:bool`]) THEN
    REWRITE_TAC[LENGTH; LE_0] THEN DISCH_THEN SUBST1_TAC THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP single_add_thm) THEN
    REWRITE_TAC[mw2n_def; VAL_WORD_0] THEN ARITH_TAC;
    X_GEN_TAC `c:bool` THEN DISCH_TAC THEN CAKE_REWRITE_TAC[] THEN
    PAIRARG_TAC THEN REWRITE_TAC[mw2n_def] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`a1:(N word)list`; `c1:bool`]) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP single_add_thm) THEN
    REWRITE_TAC[mw2n_def] THEN ARITH_TAC]);;
let mw_addv_IMP_NIL = prove
 (`!xs (ys:(N word)list) c. mw_addv xs ys c = [] ==> xs = []`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[mw_addv_def] THEN REPEAT GEN_TAC THEN
  PAIRARG_TAC THEN PAIRARG_TAC THEN REWRITE_TAC[NOT_CONS_NIL]);;

let mw_ok_addv = prove
 (`!xs ys c. mw_ok xs /\ mw_ok ys ==> mw_ok (mw_addv xs (ys:(N word)list) c)`,
  LIST_INDUCT_TAC THENL
   [REPEAT GEN_TAC THEN REWRITE_TAC[mw_addv_def] THEN COND_CASES_TAC THEN
    REWRITE_TAC[mw_ok_CLAUSES; LBIGAUX_WORD_NOT_ZERO_ONE];
    ALL_TAC] THEN
  X_GEN_TAC `ys:(N word)list` THEN X_GEN_TAC `c:bool` THEN
  REWRITE_TAC[mw_addv_def; mw_ok_CLAUSES] THEN
  SUBGOAL_THEN `?y ys2. (if ys = [] then (word 0,ys) else (HD ys,TL ys)) =
                        (y:N word,ys2:(N word)list) /\ (mw_ok ys ==> mw_ok ys2)`
  STRIP_ASSUME_TAC THENL
   [CASES_ON `ys:(N word)list` THEN REWRITE_TAC[NOT_CONS_NIL; HD; TL; PAIR_EQ] THENL
     [MAP_EVERY EXISTS_TAC [`word 0:N word`; `[]:(N word)list`];
      MAP_EVERY EXISTS_TAC [`a0:N word`; `a1:(N word)list`]] THEN
    SIMP_TAC[mw_ok_CLAUSES]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN PAIRARG_TAC THEN
  REWRITE_TAC[mw_ok_CLAUSES] THEN STRIP_TAC THEN
  SUBGOAL_THEN `mw_ok (mw_addv t (ys2:(N word)list) c1)` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP mw_addv_IMP_NIL) THEN
  UNDISCH_TAC `mw_addv t (ys2:(N word)list) c1 = []` THEN
  ASM_REWRITE_TAC[mw_addv_def] THEN COND_CASES_TAC THEN
  REWRITE_TAC[NOT_CONS_NIL] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP single_add_thm) THEN
  UNDISCH_TAC `(t:(N word)list) = [] ==> ~(h:N word = word 0)` THEN
  ASM_REWRITE_TAC[BITVAL_CLAUSES; GSYM VAL_EQ_0] THEN ARITH_TAC);;

let mw_sub_SNOC_0 = prove
 (`!xs ys c. mw_sub xs (SNOC (word 0) ys) c = mw_sub (xs:(N word)list) ys c`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[mw_sub_def] THEN
  X_GEN_TAC `ys:(N word)list` THEN CASES_ON `ys:(N word)list` THEN
  ASM_REWRITE_TAC[SNOC; mw_sub_def]);;

let mw_sub_APPEND_0 = prove
 (`!n xs ys c. mw_sub xs (APPEND ys (REPLICATE n (word 0))) c =
               mw_sub (xs:(N word)list) ys c`,
  INDUCT_TAC THEN
  ASM_REWRITE_TAC[REPLICATE_SNOC; APPEND_SNOC; mw_sub_SNOC_0] THEN
  REWRITE_TAC[REPLICATE; APPEND_NIL]);;

let mw_sub_mw_fix = prove
 (`!xs ys c. mw_sub xs (mw_fix ys) c = mw_sub xs (ys:(N word)list) c`,
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC (RAND_CONV o RATOR_CONV o RAND_CONV) [GSYM mw_fix_thm] THEN
  REWRITE_TAC[mw_sub_APPEND_0]);;

let mw2n_APPEND_REPLICATE = prove
 (`!ys n. mw2n ys = mw2n (APPEND ys (REPLICATE n (word 0)):(N word)list)`,
  REWRITE_TAC[mw2n_APPEND; mw2n_REPLICATE] THEN ARITH_TAC);;

let mw_subv_def = new_definition
  `mw_subv (xs:(N word)list) ys = mw_fix (FST (mw_sub xs ys T))`;;

let mw_subv_thm = prove
 (`!xs ys:(N word)list.
     mw2n ys <= mw2n xs /\ LENGTH ys <= LENGTH xs
     ==> mw2n (mw_subv xs ys) = mw2n xs - mw2n ys`,
  REWRITE_TAC[mw_subv_def; mw2n_mw_fix] THEN REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[GSYM(SPEC `LENGTH (xs:(N word)list) - LENGTH (ys:(N word)list)`
    mw_sub_APPEND_0)] THEN
  GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [SPECL
    [`ys:(N word)list`; `LENGTH (xs:(N word)list) - LENGTH (ys:(N word)list)`]
    mw2n_APPEND_REPLICATE] THEN
  MATCH_MP_TAC mw_sub_thm THEN
  ASM_REWRITE_TAC[GSYM mw2n_APPEND_REPLICATE; LENGTH_APPEND; LENGTH_REPLICATE] THEN
  ASM_ARITH_TAC);;
let mwi_add_def = new_definition
  `mwi_add (s,xs:(N word)list) (t,ys) =
     if s = t then
       if LENGTH ys <= LENGTH xs then (s, mw_addv xs ys F)
       else (s, mw_addv ys xs F)
     else if mw2n ys = mw2n xs then (F,[])
     else if mw2n ys <= mw2n xs then (s,mw_subv xs ys)
     else (~s,mw_subv ys xs)`;;

let mwi_sub_def = new_definition
  `mwi_sub (s,xs:(N word)list) (t,ys) = mwi_add (s,xs) (~t,ys)`;;

let mwi_add_lemma = prove
 (`!s t xs ys:(N word)list.
     mw_ok xs /\ mw_ok ys
     ==> mw2i (mwi_add (s,xs) (t,ys)) = mw2i (s,xs) + mw2i (t,ys)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!us vs:(N word)list. mw_ok us /\ mw_ok vs /\ mw2n vs <= mw2n us
      ==> &(mw2n (mw_subv us vs)):int = &(mw2n us) - &(mw2n vs)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(SPECL [`us:(N word)list`; `vs:(N word)list`] mw_subv_thm) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[mw2n_LESS]; ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN ASM_SIMP_TAC[INT_OF_NUM_SUB]; ALL_TAC] THEN
  SUBGOAL_THEN `!us vs:(N word)list. LENGTH vs <= LENGTH us
      ==> &(mw2n (mw_addv us vs F)):int = &(mw2n us) + &(mw2n vs)`
  ASSUME_TAC THENL
   [SIMP_TAC[mw_addv_thm; BITVAL_CLAUSES; ADD_CLAUSES; INT_OF_NUM_ADD];
    ALL_TAC] THEN
  MAP_EVERY BOOL_CASES_TAC [`s:bool`; `t:bool`] THEN
  REWRITE_TAC[mwi_add_def; mw2i_DEF] THEN
  REPEAT COND_CASES_TAC THEN
  ASM_SIMP_TAC[mw2n_def; mw2i_DEF; ARITH_RULE `~(a <= b) ==> b <= a`] THEN
  INT_ARITH_TAC);;
let LBIGAUX_MWI_ADD_I2MW = prove
 (`!s t xs ys:(N word)list.
     mw_ok xs /\ mw_ok ys /\ ~(s /\ xs = [])
     ==> mwi_add (s,xs) (t,ys) = i2mw (mw2i (s,xs) + mw2i (t,ys))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC mw2i_EQ_IMP_EQ_i2mw THEN
  ASM_SIMP_TAC[mwi_add_lemma] THEN
  SUBGOAL_THEN `!us vs:(N word)list.
      mw_ok us /\ mw_ok vs /\ mw2n vs < mw2n us ==> ~(mw_subv us vs = [])`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(SPECL [`us:(N word)list`; `vs:(N word)list`] mw_subv_thm) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[mw2n_LESS; LT_IMP_LE]; ALL_TAC] THEN
    ASM_REWRITE_TAC[mw2n_def] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[mwi_add_def] THEN REPEAT COND_CASES_TAC THEN
    ASM_SIMP_TAC[SND; mw_ok_CLAUSES; mw_subv_def; mw_ok_fix; mw_ok_addv];
    REWRITE_TAC[mwi_add_def] THEN REPEAT COND_CASES_TAC THEN
    ASM_REWRITE_TAC[PAIR_EQ] THEN
    ASM_MESON_TAC[mw_addv_IMP_NIL; LENGTH; LE_0; LT_LE; NOT_LE]]);;

let mwi_add_thm = prove
 (`!i j. mwi_add (i2mw i) (i2mw j):bool#(N word)list = i2mw (i + j)`,
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o BINOP_CONV) [i2mw_def] THEN
  W(fun (asl,w) -> MP_TAC(PART_MATCH (lhand o rand) LBIGAUX_MWI_ADD_I2MW (lhand w))) THEN
  REWRITE_TAC[mw_ok_n2mw; GSYM i2mw_def; mw2i_i2mw] THEN
  DISCH_THEN MATCH_MP_TAC THEN REWRITE_TAC[n2mw_NIL] THEN
  REWRITE_TAC[GSYM INT_OF_NUM_EQ; LBIGAUX_NUM_ABS] THEN INT_ARITH_TAC);;

let mwi_sub_thm = prove
 (`!i j. mwi_sub (i2mw i) (i2mw j):bool#(N word)list = i2mw (i - j)`,
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o BINOP_CONV) [i2mw_def] THEN
  REWRITE_TAC[mwi_sub_def] THEN
  W(fun (asl,w) -> MP_TAC(PART_MATCH (lhand o rand) LBIGAUX_MWI_ADD_I2MW (lhand w))) THEN
  REWRITE_TAC[mw_ok_n2mw; GSYM i2mw_def; mw2i_i2mw] THEN ANTS_TAC THENL
   [REWRITE_TAC[n2mw_NIL; GSYM INT_OF_NUM_EQ; LBIGAUX_NUM_ABS] THEN INT_ARITH_TAC;
    DISCH_THEN SUBST1_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[mw2i_DEF; mw2n_n2mw; LBIGAUX_NUM_ABS] THEN INT_ARITH_TAC]);;

let n2mw_1 = prove
 (`n2mw 1 = [word 1:N word]`,
  ONCE_REWRITE_TAC[n2mw_def] THEN REWRITE_TAC[ARITH_RULE `~(1 = 0)`] THEN
  MP_TAC ONE_LT_dimword THEN SIMP_TAC[MOD_LT; DIV_LT; CONS_11] THEN
  DISCH_TAC THEN ONCE_REWRITE_TAC[n2mw_def] THEN REWRITE_TAC[]);;
(* ------------------------------------------------------------------------- *)
(* mul                                                                       *)
(* ------------------------------------------------------------------------- *)

let single_mul_def = new_definition
  `single_mul (x:N word) (y:N word) (c:N word) =
     (word_add (word_mul x y) c,
      (word ((val x * val y + val c) DIV dimword(:N)):N word))`;;

let single_mul_add_def = cake_def
  `single_mul_add (p:N word) q k s =
     match single_mul p q k with (x,kc) ->
     match mw_add [x;kc] [s;word 0] F with (zs,c) -> (HD zs, HD (TL zs))`;;

let mw_mul_pass_def = cake_def
  `(mw_mul_pass (x:N word) [] zs k = [k]) /\
   (mw_mul_pass x (CONS y ys) zs k =
      match single_mul_add x y k (HD zs) with (y1,k1) ->
        CONS y1 (mw_mul_pass x ys (TL zs) k1))`;;

let mw_mul_def = cake_def
  `(mw_mul [] (ys:(N word)list) zs = zs) /\
   (mw_mul (CONS (x:N word) xs) ys zs =
      let zs2 = mw_mul_pass x ys zs (word 0) in
        CONS (HD zs2) (mw_mul xs ys (TL zs2)))`;;

let mwi_mul_def = new_definition
  `mwi_mul (s:bool,xs:(N word)list) (t:bool,ys:(N word)list) =
     if xs = [] \/ ys = [] then (F,[]) else
       (~(s = t), mw_fix (mw_mul xs ys (MAP (\x. word 0) ys)))`;;
let LBIGAUX_VAL_LE_PRED = prove
 (`!w:N word. val w <= dimword(:N) - 1`,
  GEN_TAC THEN MP_TAC(ISPEC `w:N word` w2n_lt) THEN ARITH_TAC);;

let LBIGAUX_MUL_ADD_BOUND = prove
 (`!(a:N word) (b:N word) (c:N word) (d:N word).
     val a * val b + val c + val d < dimword(:N) * dimword(:N)`,
  REPEAT GEN_TAC THEN
  MP_TAC(SPECL [`val (a:N word)`; `dimword(:N) - 1`; `val (b:N word)`;
                `dimword(:N) - 1`] LE_MULT2) THEN
  REWRITE_TAC[LBIGAUX_VAL_LE_PRED] THEN
  MP_TAC(ISPEC `c:N word` LBIGAUX_VAL_LE_PRED) THEN
  MP_TAC(ISPEC `d:N word` LBIGAUX_VAL_LE_PRED) THEN
  MP_TAC ZERO_LT_dimword THEN
  SPEC_TAC(`dimword(:N)`,`k:num`) THEN INDUCT_TAC THEN
  REWRITE_TAC[ARITH_RULE `SUC k - 1 = k`] THEN ARITH_TAC);;

let LBIGAUX_WORD_MUL_ADD = prove
 (`!(x:N word) y c. word_add (word_mul x y) c = word (val x * val y + val c)`,
  REWRITE_TAC[WORD_ADD; WORD_MUL; WORD_VAL]);;

let single_mul_thm = prove
 (`!(x:N word) y k z l.
     single_mul x y k = (z,l)
     ==> val z + dimword(:N) * val l = val x * val y + val k`,
  REWRITE_TAC[single_mul_def; PAIR_EQ; LBIGAUX_WORD_MUL_ADD] THEN
  REPEAT STRIP_TAC THEN REPEAT(FIRST_X_ASSUM(SUBST1_TAC o SYM)) THEN
  REWRITE_TAC[w2n_n2w] THEN
  SUBGOAL_THEN `(val (x:N word) * val (y:N word) + val (k:N word)) DIV dimword(:N)
                < dimword(:N)` ASSUME_TAC THENL
   [SIMP_TAC[RDIV_LT_EQ; LBIGAUX_DIMWORD_NZ] THEN
    MP_TAC(SPECL [`x:N word`; `y:N word`; `k:N word`; `word 0:N word`]
      LBIGAUX_MUL_ADD_BOUND) THEN REWRITE_TAC[VAL_WORD_0] THEN ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[MOD_LT] THEN
  MP_TAC(SPECL [`val (x:N word) * val (y:N word) + val (k:N word)`; `dimword(:N)`]
    DIVISION) THEN
  REWRITE_TAC[LBIGAUX_DIMWORD_NZ] THEN ARITH_TAC);;

let LBIGAUX_MW_ADD_2 = prove
 (`!(x:N word) y u v c zs d.
     mw_add [x;y] [u;v] c = (zs,d) ==> ?z1 z2. zs = [z1;z2:N word]`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mw_add_def; HD; TL] THEN
  REPEAT PAIRARG_TAC THEN REWRITE_TAC[PAIR_EQ] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[PAIR_EQ]) THEN ASM_MESON_TAC[]);;

let single_mul_add_thm = prove
 (`!(p:N word) q k1 k2 x1 x2.
     single_mul_add p q k1 k2 = (x1,x2)
     ==> val x1 + dimword(:N) * val x2 = val p * val q + val k1 + val k2`,
  REPEAT GEN_TAC THEN REWRITE_TAC[single_mul_add_def] THEN
  PAIRARG_TAC THEN PAIRARG_TAC THEN REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP single_mul_thm) THEN
  MP_TAC(SPECL [`[x;kc]:(N word)list`; `[k2;word 0]:(N word)list`; `F`;
                `zs:(N word)list`; `c:bool`] mw_add_thm) THEN
  ASM_REWRITE_TAC[LENGTH] THEN
  SUBGOAL_THEN `?z1 z2. zs = [z1;z2:N word]` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[LBIGAUX_MW_ADD_2]; ALL_TAC] THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o
    check (fun th -> is_var(rhs(concl th))))) THEN
  REWRITE_TAC[HD; TL; mw2n_def; dimwords_thm; VAL_WORD_0; BITVAL_CLAUSES] THEN
  MP_TAC(SPECL [`p:N word`; `q:N word`; `k1:N word`; `k2:N word`]
    LBIGAUX_MUL_ADD_BOUND) THEN
  BOOL_CASES_TAC `c:bool` THEN REWRITE_TAC[BITVAL_CLAUSES] THEN ARITH_TAC);;
let mw_mul_pass_thm = prove
 (`!ys zs (x:N word) k.
     LENGTH ys = LENGTH zs
     ==> mw2n (mw_mul_pass x ys zs k) = val x * mw2n ys + mw2n zs + val k /\
         LENGTH (mw_mul_pass x ys zs k) = LENGTH ys + 1`,
  LIST_INDUCT_TAC THEN X_GEN_TAC `zs:(N word)list` THEN
  CASES_ON `zs:(N word)list` THEN
  REWRITE_TAC[mw_mul_pass_def; LENGTH; HD; TL; ARITH_RULE
    `~(SUC n = 0) /\ ~(0 = SUC n) /\ (SUC m = SUC n <=> m = n)`] THENL
   [REWRITE_TAC[mw2n_def; LENGTH] THEN ARITH_TAC; ALL_TAC] THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN PAIRARG_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`a1:(N word)list`; `x:N word`; `k1:N word`]) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[mw2n_def; LENGTH; ADD1] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP single_mul_add_thm) THEN ARITH_TAC);;

let mw_mul_thm = prove
 (`!xs ys (zs:(N word)list).
     LENGTH ys = LENGTH zs
     ==> mw2n (mw_mul xs ys zs) = mw2n xs * mw2n ys + mw2n zs`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[mw_mul_def; mw2n_def; LET_DEF; LET_END_DEF] THEN
  REPEAT STRIP_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`ys:(N word)list`; `zs:(N word)list`; `h:N word`; `word 0:N word`]
    mw_mul_pass_thm) THEN
  ASM_REWRITE_TAC[] THEN
  SPEC_TAC(`mw_mul_pass (h:N word) ys zs (word 0)`,`qs:(N word)list`) THEN
  X_GEN_TAC `qs:(N word)list` THEN CASES_ON `qs:(N word)list` THEN
  REWRITE_TAC[LENGTH; ARITH_RULE `~(0 = n + 1)`] THEN
  REWRITE_TAC[HD; TL; mw2n_def; VAL_WORD_0; ARITH_RULE `SUC m = n + 1 <=> m = n`] THEN
  STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPECL [`ys:(N word)list`; `a1:(N word)list`]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN REWRITE_TAC[RIGHT_ADD_DISTRIB] THEN
  ARITH_TAC);;
let LBIGAUX_NUM_ABS_EQ_0 = prove
 (`!i:int. num_of_int (abs i) = 0 <=> i = &0`,
  GEN_TAC THEN REWRITE_TAC[GSYM INT_OF_NUM_EQ; LBIGAUX_NUM_ABS] THEN
  INT_ARITH_TAC);;

let n2mw_0 = prove
 (`n2mw 0 = []:(N word)list`,
  REWRITE_TAC[n2mw_NIL]);;

let LBIGAUX_MW2N_MAP_ZERO = prove
 (`!ys:B list. mw2n (MAP (\x. word 0) ys:(N word)list) = 0`,
  MP_TAC(ISPEC `[]:(N word)list` mw2n_MAP_ZERO) THEN
  REWRITE_TAC[APPEND; mw2n_def]);;

let mwi_mul_thm = prove
 (`!i j. mwi_mul (i2mw i) (i2mw j):bool#(N word)list = i2mw (i * j)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[i2mw_def; mwi_mul_def; n2mw_NIL; LBIGAUX_NUM_ABS_EQ_0] THEN
  ASM_CASES_TAC `i:int = &0` THEN
  ASM_REWRITE_TAC[INT_MUL_LZERO; INT_LT_REFL; INT_ABS_NUM; NUM_OF_INT_OF_NUM;
                  n2mw_0] THEN
  ASM_CASES_TAC `j:int = &0` THEN
  ASM_REWRITE_TAC[INT_MUL_RZERO; INT_LT_REFL; INT_ABS_NUM; NUM_OF_INT_OF_NUM;
                  n2mw_0; PAIR_EQ] THEN
  CONJ_TAC THENL
   [MP_TAC(SPECL [`i:int`; `j:int`] INT_MUL_POS_LT) THEN
    MP_TAC(SPECL [`i:int`; `j:int`] INT_ENTIRE) THEN
    ASM_REWRITE_TAC[] THEN ASM_INT_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[n2mw_mw2n; n2mw_11] THEN
  SIMP_TAC[mw_mul_thm; LENGTH_MAP; LBIGAUX_MW2N_MAP_ZERO; mw2n_n2mw; ADD_CLAUSES] THEN
  REWRITE_TAC[GSYM INT_OF_NUM_EQ; GSYM INT_OF_NUM_MUL; LBIGAUX_NUM_ABS; INT_ABS_MUL]);;
(* ------------------------------------------------------------------------- *)
(* div by 2                                                                  *)
(* ------------------------------------------------------------------------- *)

let LBIGAUX_SHIFT_AND = prove
 (`!w x:N word. word_and (word_ushr w 1) (word_shl x (dimindex(:N) - 1)) = word 0`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_AND; BIT_WORD_USHR; BIT_WORD_SHL;
              BIT_WORD_0] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  ASM_CASES_TAC `dimindex(:N) <= i + 1` THEN ASM_SIMP_TAC[BIT_TRIVIAL] THEN
  MATCH_MP_TAC(TAUT `~b ==> ~(a /\ b /\ c)`) THEN ASM_ARITH_TAC);;

let LBIGAUX_DIMWORD_HALF = prove
 (`dimword(:N) = 2 * 2 EXP (dimindex(:N) - 1)`,
  REWRITE_TAC[dimword_def; GSYM(CONJUNCT2 EXP)] THEN AP_TERM_TAC THEN
  MP_TAC(ISPEC `(:N)` DIMINDEX_GE_1) THEN ARITH_TAC);;

let LBIGAUX_SHIFT_OR = prove
 (`!w x:N word.
     val (word_or (word_ushr w 1) (word_shl x (dimindex(:N) - 1))) =
     val w DIV 2 + 2 EXP (dimindex(:N) - 1) * (val x MOD 2)`,
  REPEAT GEN_TAC THEN SIMP_TAC[VAL_WORD_OR_DISJOINT; LBIGAUX_SHIFT_AND] THEN
  REWRITE_TAC[VAL_WORD_USHR; VAL_WORD_SHL; GSYM dimword_def; EXP_1] THEN
  AP_TERM_TAC THEN REWRITE_TAC[LBIGAUX_DIMWORD_HALF] THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [MULT_SYM] THEN
  REWRITE_TAC[MOD_MULT2]);;

let mw_shift_def = cake_def
  `(mw_shift [] = []:(N word)list) /\
   (mw_shift [w:N word] = [word_ushr w 1]) /\
   (mw_shift (CONS (w:N word) (CONS x xs)) =
      CONS (word_or (word_ushr w 1) (word_shl x (dimindex(:N) - 1)))
           (mw_shift (CONS x xs)))`;;

let LBIGAUX_DIV2_ADD = prove
 (`!a b. (a + 2 * b) DIV 2 = a DIV 2 + b`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[ADD_SYM] THEN
  SIMP_TAC[DIV_MULT_ADD; ARITH_RULE `~(2 = 0)`] THEN ARITH_TAC);;

let mw_shift_thm = prove
 (`!xs:(N word)list. mw2n (mw_shift xs) = mw2n xs DIV 2`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[mw_shift_def; mw2n_def] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  POP_ASSUM MP_TAC THEN SPEC_TAC(`t:(N word)list`,`t:(N word)list`) THEN
  LIST_INDUCT_TAC THEN
  REWRITE_TAC[mw_shift_def; mw2n_def; VAL_WORD_USHR; EXP_1; MULT_CLAUSES;
              ADD_CLAUSES] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[LBIGAUX_SHIFT_OR; LBIGAUX_DIMWORD_HALF] THEN
  SPEC_TAC(`2 EXP (dimindex(:N) - 1)`,`k:num`) THEN GEN_TAC THEN
  REWRITE_TAC[GSYM MULT_ASSOC; LBIGAUX_DIV2_ADD] THEN
  MP_TAC(SPECL [`val(h':N word)`; `2`] DIVISION) THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  ABBREV_TAC `q = val(h':N word) DIV 2` THEN
  ABBREV_TAC `r = val(h':N word) MOD 2` THEN
  DISCH_THEN(CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC) THEN ARITH_TAC);;

let LENGTH_mw_shift = prove
 (`!xs:(N word)list. LENGTH (mw_shift xs) = LENGTH xs`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[mw_shift_def; LENGTH] THEN
  POP_ASSUM MP_TAC THEN SPEC_TAC(`t:(N word)list`,`t:(N word)list`) THEN
  LIST_INDUCT_TAC THEN SIMP_TAC[mw_shift_def; LENGTH]);;
(* ------------------------------------------------------------------------- *)
(* compare                                                                   *)
(* ------------------------------------------------------------------------- *)

let mw_cmp_def = cake_def_wf
  `MEASURE ((LENGTH:(N word)list->num) o (FST:(N word)list#(N word)list->(N word)list))`
  (REWRITE_TAC(o_THM::WF_REL_THMS) THEN REPEAT STRIP_TAC THEN
   MP_TAC(ISPEC `xs:(N word)list` LENGTH_FRONT) THEN ASM_REWRITE_TAC[] THEN
   FIRST_X_ASSUM(MP_TAC o check (is_neg o concl)) THEN
   REWRITE_TAC[GSYM LENGTH_EQ_NIL] THEN ASM_ARITH_TAC)
  `mw_cmp (xs:(N word)list) (ys:(N word)list) =
     if xs = [] then NONE else
     if LAST xs = LAST ys then mw_cmp (BUTLAST xs) (BUTLAST ys)
     else SOME (word_ult (LAST xs) (LAST ys))`;;

let mw_cmp_ind = cake_ind "mw_cmp";;
let mw_compare_def = new_definition
  `mw_compare (xs:(N word)list) (ys:(N word)list) =
     if LENGTH xs < LENGTH ys then SOME (0 < 1) else
     if LENGTH ys < LENGTH xs then SOME (1 < 0) else mw_cmp xs ys`;;

let option_eq_def = cake_def
  `(option_eq b NONE = NONE) /\
   (option_eq b (SOME x) = SOME (~(b <=> x)))`;;

let mwi_compare_def = new_definition
  `mwi_compare (s,xs:(N word)list) (t,ys:(N word)list) =
     if s = t then option_eq s (mw_compare xs ys) else SOME s`;;

let mwi_lt_def = new_definition
  `mwi_lt (s_xs:bool#(N word)list) t_ys <=> mwi_compare s_xs t_ys = SOME T`;;

let mwi_eq_def = new_definition
  `mwi_eq (s_xs:bool#(N word)list) t_ys <=> mwi_compare s_xs t_ys = NONE`;;

let LAST_IMP_mw2n_LESS_mw2n = prove
 (`!xs ys:(N word)list.
     LENGTH xs = LENGTH ys /\ word_ult (LAST xs) (LAST ys) /\ ~(xs = [])
     ==> mw2n xs < mw2n ys`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPEC `xs:(N word)list` SNOC_CASES) THEN
  MP_TAC(ISPEC `ys:(N word)list` SNOC_CASES) THEN
  STRIP_TAC THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[LENGTH_SNOC; LENGTH; NOT_SUC; ARITH_RULE `~(0 = SUC n)`;
                  LAST_SNOC; NOT_SNOC_NIL; SUC_INJ] THEN
  REWRITE_TAC[SNOC_APPEND; mw2n_APPEND; mw2n_def; WORD_ULT] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES] THEN
  ONCE_REWRITE_TAC[ADD_SYM] THEN ONCE_REWRITE_TAC[MULT_SYM] THEN
  MATCH_MP_TAC LBIGAUX_MULT_ADD_LESS_MULT_ADD THEN
  ASM_MESON_TAC[mw2n_lt]);;
let LBIGAUX_MW2N_FRONT_LAST = prove
 (`!xs:(N word)list.
     ~(xs = [])
     ==> mw2n xs = mw2n (BUTLAST xs) +
                   dimwords (LENGTH (BUTLAST xs)) (:N) * val (LAST xs)`,
  GEN_TAC THEN DISCH_THEN(fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV)
    [GSYM(MATCH_MP APPEND_BUTLAST_LAST th)]) THEN
  REWRITE_TAC[mw2n_APPEND; mw2n_def] THEN ARITH_TAC);;

let mw_cmp_thm = prove
 (`!xs ys:(N word)list.
     LENGTH ys = LENGTH xs
     ==> mw_cmp xs ys = if mw2n xs = mw2n ys then NONE
                        else SOME (mw2n xs < mw2n ys)`,
  MATCH_MP_TAC mw_cmp_ind THEN REPEAT GEN_TAC THEN DISCH_TAC THEN DISCH_TAC THEN
  ONCE_REWRITE_TAC[mw_cmp_def] THEN
  ASM_CASES_TAC `xs:(N word)list = []` THENL
   [UNDISCH_TAC `LENGTH (ys:(N word)list) = LENGTH (xs:(N word)list)` THEN
    ASM_REWRITE_TAC[LENGTH; LENGTH_EQ_NIL] THEN DISCH_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(ys:(N word)list = [])` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM LENGTH_EQ_NIL] THEN UNDISCH_TAC `~(xs:(N word)list = [])` THEN
    REWRITE_TAC[GSYM LENGTH_EQ_NIL] THEN
    UNDISCH_TAC `LENGTH (ys:(N word)list) = LENGTH (xs:(N word)list)` THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `LENGTH (BUTLAST (ys:(N word)list)) = LENGTH (BUTLAST (xs:(N word)list))`
  ASSUME_TAC THENL [ASM_SIMP_TAC[LENGTH_FRONT]; ALL_TAC] THEN
  ASM_SIMP_TAC[LBIGAUX_MW2N_FRONT_LAST] THEN
  MP_TAC(ISPEC `BUTLAST (xs:(N word)list)` mw2n_lt) THEN
  MP_TAC(ISPEC `BUTLAST (ys:(N word)list)` mw2n_lt) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `w = dimwords (LENGTH (BUTLAST (xs:(N word)list))) (:N)` THEN
  REPEAT DISCH_TAC THEN COND_CASES_TAC THENL
   [ASM_SIMP_TAC[EQ_ADD_RCANCEL; LT_ADD_RCANCEL]; ALL_TAC] THEN
  REWRITE_TAC[WORD_ULT] THEN
  SUBGOAL_THEN `~(val (LAST (xs:(N word)list)) = val (LAST (ys:(N word)list)))`
  MP_TAC THENL [ASM_REWRITE_TAC[VAL_EQ]; ALL_TAC] THEN
  REWRITE_TAC[ARITH_RULE `~(a = b) <=> a < b \/ b < a`] THEN STRIP_TAC THENL
   [MP_TAC(SPECL [`val (LAST (xs:(N word)list))`; `mw2n (BUTLAST (xs:(N word)list))`;
                  `w:num`; `val (LAST (ys:(N word)list))`;
                  `mw2n (BUTLAST (ys:(N word)list))`] LBIGAUX_MULT_ADD_LESS_MULT_ADD);
    MP_TAC(SPECL [`val (LAST (ys:(N word)list))`; `mw2n (BUTLAST (ys:(N word)list))`;
                  `w:num`; `val (LAST (xs:(N word)list))`;
                  `mw2n (BUTLAST (xs:(N word)list))`] LBIGAUX_MULT_ADD_LESS_MULT_ADD)] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[ARITH_RULE `a * w + b = b + w * a`] THEN
  SIMP_TAC[ARITH_RULE `a < b ==> ~(a = b) /\ ~(b < a)`; LT_IMP_NE] THEN
  ASM_SIMP_TAC[ARITH_RULE `a < b ==> ~(b < a)`] THEN
  MESON_TAC[LT_REFL; LT_TRANS]);;
let LENGTH_LESS_IMP_mw2n_LESS = prove
 (`!(xs:(N word)list) (ys:(N word)list).
     mw_ok xs /\ mw_ok ys /\ LENGTH xs < LENGTH ys ==> mw2n xs < mw2n ys`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(ys:(N word)list = [])` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `LENGTH (xs:(N word)list) < LENGTH (ys:(N word)list)` THEN
    ASM_REWRITE_TAC[LENGTH] THEN ARITH_TAC; ALL_TAC] THEN
  TRANS_TAC LTE_TRANS `dimwords (LENGTH (xs:(N word)list)) (:N)` THEN
  REWRITE_TAC[mw2n_lt] THEN
  TRANS_TAC LE_TRANS `dimwords (LENGTH (ys:(N word)list) - 1) (:N)` THEN
  ASM_SIMP_TAC[mw2n_gt; LBIGAUX_DIMWORDS_LE] THEN ASM_ARITH_TAC);;

let mw2n_LESS_IMP_LENGTH_LESS_EQ = prove
 (`!(xs:(N word)list) (ys:(N word)list).
     mw_ok xs /\ mw_ok ys /\ mw2n xs < mw2n ys ==> LENGTH xs <= LENGTH ys`,
  REWRITE_TAC[GSYM NOT_LT] THEN REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`ys:(N word)list`; `xs:(N word)list`] LENGTH_LESS_IMP_mw2n_LESS) THEN
  ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

let mw_compare_thm = prove
 (`!xs ys:(N word)list.
     mw_ok xs /\ mw_ok ys
     ==> mw_compare xs ys = if mw2n xs = mw2n ys then NONE
                            else SOME (mw2n xs < mw2n ys)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mw_compare_def] THEN
  ASM_CASES_TAC `LENGTH (xs:(N word)list) = LENGTH (ys:(N word)list)` THEN
  ASM_SIMP_TAC[mw_cmp_thm; LT_REFL] THEN
  FIRST_X_ASSUM(DISJ_CASES_TAC o MATCH_MP (ARITH_RULE
    `~(m = n) ==> m < n \/ n < m`)) THEN
  FIRST_ASSUM(fun th -> ASSUME_TAC(MATCH_MP (ARITH_RULE `m < n ==> ~(n < m)`) th)) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THENL
   [MP_TAC(SPECL [`xs:(N word)list`; `ys:(N word)list`] LENGTH_LESS_IMP_mw2n_LESS);
    MP_TAC(SPECL [`ys:(N word)list`; `xs:(N word)list`] LENGTH_LESS_IMP_mw2n_LESS)] THEN
  ASM_REWRITE_TAC[] THEN
  SIMP_TAC[ARITH_RULE `a < b ==> ~(a = b) /\ ~(b < a)`; LT_IMP_NE] THEN
  SIMP_TAC[ARITH_RULE `b < a ==> ~(a = b) /\ ~(a < b)`]);;

let mwi_compare_thm = prove
 (`!i j. mwi_compare (i2mw i:bool#(N word)list) (i2mw j) =
         if i = j then NONE else SOME (i < j)`,
  REWRITE_TAC[i2mw_def; mwi_compare_def] THEN
  SIMP_TAC[mw_compare_thm; mw_ok_n2mw; mw2n_n2mw] THEN
  REPEAT GEN_TAC THEN
  REWRITE_TAC[GSYM INT_OF_NUM_EQ; GSYM INT_OF_NUM_LT; LBIGAUX_NUM_ABS] THEN
  ASM_CASES_TAC `i:int = j` THEN ASM_REWRITE_TAC[option_eq_def] THEN
  ASM_CASES_TAC `(i:int) < &0` THEN ASM_CASES_TAC `(j:int) < &0` THEN
  ASM_REWRITE_TAC[option_eq_def; option_INJ] THEN
  REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[option_eq_def; option_INJ;
    option_DISTINCT] THEN
  ASM_INT_ARITH_TAC);;
(* alternative compare *)

let mw_cmp_alt_def = cake_def
  `(mw_cmp_alt [] (ys:(N word)list) b = b) /\
   (mw_cmp_alt (CONS (x:N word) xs) ys b =
      mw_cmp_alt xs (TL ys) (if x = HD ys then b else
                             if word_ult x (HD ys) then SOME T else SOME F))`;;

(* HOL4 mw_cmp_alt_lemma, stated with the values of the lists *)

let mw_cmp_alt_lemma = prove
 (`!xs ys:(N word)list res.
     LENGTH xs = LENGTH ys
     ==> mw_cmp_alt xs ys res =
         if mw2n xs = mw2n ys then res else SOME (mw2n xs < mw2n ys)`,
  LIST_INDUCT_TAC THEN X_GEN_TAC `ys:(N word)list` THEN
  CASES_ON `ys:(N word)list` THEN
  REWRITE_TAC[mw_cmp_alt_def; LENGTH; HD; TL; mw2n_def; ARITH_RULE
    `~(SUC n = 0) /\ ~(0 = SUC n) /\ (SUC m = SUC n <=> m = n)`] THEN
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[] THEN
  MP_TAC(ISPEC `h:N word` w2n_lt) THEN MP_TAC(ISPEC `a0:N word` w2n_lt) THEN
  REWRITE_TAC[GSYM VAL_EQ; WORD_ULT] THEN
  ASM_CASES_TAC `mw2n (t:(N word)list) = mw2n (a1:(N word)list)` THEN
  ASM_REWRITE_TAC[EQ_ADD_RCANCEL; LT_ADD_RCANCEL] THENL
   [REPEAT DISCH_TAC THEN REPEAT COND_CASES_TAC THEN
    ASM_REWRITE_TAC[option_INJ] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(DISJ_CASES_TAC o MATCH_MP (ARITH_RULE
    `~(m = n) ==> m < n \/ n < m`)) THENL
   [MP_TAC(SPECL [`mw2n (t:(N word)list)`; `val (h:N word)`; `dimword(:N)`;
                  `mw2n (a1:(N word)list)`; `val (a0:N word)`]
     LBIGAUX_MULT_ADD_LESS_MULT_ADD);
    MP_TAC(SPECL [`mw2n (a1:(N word)list)`; `val (a0:N word)`; `dimword(:N)`;
                  `mw2n (t:(N word)list)`; `val (h:N word)`]
     LBIGAUX_MULT_ADD_LESS_MULT_ADD)] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[ARITH_RULE `a * w + b = b + w * a`] THEN
  REPEAT STRIP_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[option_INJ] THEN
  ASM_ARITH_TAC);;

let mw_cmp_alt_thm = prove
 (`!xs ys:(N word)list.
     LENGTH xs = LENGTH ys ==> mw_cmp xs ys = mw_cmp_alt xs ys NONE`,
  SIMP_TAC[mw_cmp_alt_lemma; mw_cmp_thm]);;
(* ------------------------------------------------------------------------- *)
(* Division (Knuth's algorithm D); the digits of the inputs of mw_div_test,  *)
(* mw_div_guess and single_div are most significant first.                   *)
(* ------------------------------------------------------------------------- *)

let mw_mul_by_single_def = new_definition
  `mw_mul_by_single (x:N word) (ys:(N word)list) =
     mw_mul_pass x ys (k2mw (LENGTH ys) 0) (word 0)`;;

let LENGTH_mw_mul_pass = prove
 (`!ys zs (x:N word) k. LENGTH (mw_mul_pass x ys zs k) = LENGTH ys + 1`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[mw_mul_pass_def; LENGTH] THEN
  REPEAT GEN_TAC THEN TRY PAIRARG_TAC THEN ASM_REWRITE_TAC[LENGTH] THEN
  ARITH_TAC);;

let LENGTH_mw_mul_by_single = prove
 (`!(x:N word) ys. LENGTH (mw_mul_by_single x ys) = LENGTH ys + 1`,
  REWRITE_TAC[mw_mul_by_single_def; LENGTH_mw_mul_pass]);;

let DIV_thm2 = prove
 (`!a b c. 0 < b /\ a < c * b ==> a DIV b < c`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[RDIV_LT_EQ; ARITH_RULE `0 < b ==> ~(b = 0)`] THEN
  ONCE_REWRITE_TAC[MULT_SYM] THEN ASM_REWRITE_TAC[]);;

let DIV_thm1 = prove
 (`!a b c. 0 < b /\ b <= c ==> a DIV c <= a DIV b`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC DIV_MONO2 THEN ASM_ARITH_TAC);;

let dimwords_dimword = prove
 (`!n. dimwords n (:N) = dimword(:N) EXP n`,
  REWRITE_TAC[dimwords_def; dimword_def; EXP_EXP] THEN
  GEN_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[MULT_SYM]);;

let mw2n_msf = prove
 (`!(x:N word) xs. mw2n (APPEND xs [x]) = mw2n xs + dimwords (LENGTH xs) (:N) * val x`,
  REWRITE_TAC[mw2n_APPEND; mw2n_def] THEN ARITH_TAC);;

let mw2n_k2mw_0 = prove
 (`!x. mw2n (k2mw x 0:(N word)list) = 0`,
  INDUCT_TAC THEN ASM_REWRITE_TAC[k2mw_def; mw2n_def; DIV_0; VAL_WORD_0] THEN
  ARITH_TAC);;

let mw_mul_by_single_lemma = prove
 (`!(x:N word) (ys:(N word)list).
     mw2n (mw_mul_by_single x ys) = val x * mw2n ys /\
     LENGTH (mw_mul_by_single x ys) = LENGTH ys + 1`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mw_mul_by_single_def] THEN
  MP_TAC(SPECL [`ys:(N word)list`; `k2mw (LENGTH (ys:(N word)list)) 0:(N word)list`;
                `x:N word`; `word 0:N word`] mw_mul_pass_thm) THEN
  REWRITE_TAC[LENGTH_k2mw; mw2n_k2mw_0; VAL_WORD_0; ADD_CLAUSES]);;

let d_word_msb = prove
 (`!(a:N word). word_msb a <=> dimword(:N) DIV 2 <= val a`,
  GEN_TAC THEN REWRITE_TAC[word_msb_def; MSB_VAL] THEN
  REWRITE_TAC[LBIGAUX_DIMWORD_HALF] THEN
  SIMP_TAC[DIV_MULT; ARITH_RULE `~(2 = 0)`]);;

let LBIGAUX_VAL_DOUBLE = prove
 (`!v:N word. val v < dimword(:N) DIV 2 ==> val (word_mul v (word 2)) = 2 * val v`,
  GEN_TAC THEN REWRITE_TAC[VAL_WORD_MUL; VAL_WORD; GSYM dimword_def] THEN
  CONV_TAC MOD_DOWN_CONV THEN REWRITE_TAC[LBIGAUX_DIMWORD_HALF] THEN
  SIMP_TAC[DIV_MULT; ARITH_RULE `~(2 = 0)`] THEN DISCH_TAC THEN
  SUBGOAL_THEN `val (v:N word) * 2 < 2 * 2 EXP (dimindex(:N) - 1)`
    (fun th -> REWRITE_TAC[MATCH_MP MOD_LT th]) THEN
  ASM_ARITH_TAC);;
let calc_d_def = cake_def_wf `MEASURE (\p:N word#N word. dimword(:N) - val(FST p))`
  (REWRITE_TAC WF_REL_THMS THEN BETA_TAC THEN
   REWRITE_TAC[FST; DE_MORGAN_THM; d_word_msb; NOT_LE] THEN
   REPEAT STRIP_TAC THEN MP_TAC(SPEC `v1:N word` LBIGAUX_VAL_DOUBLE) THEN
   ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC)
  `calc_d (v1:N word, d:N word) =
     if v1 = word 0 \/ word_msb v1 then d
     else calc_d (word_mul v1 (word 2), word_mul d (word 2))`;;

(* HOL4 calc_d_ind (the kit does not produce induction theorems for this  *)
(* form of definition, so it is proved here by measure induction)         *)

let calc_d_ind = prove
 (`!P. (!v1 d. (~(v1 = word 0 \/ word_msb v1)
                ==> P (word_mul v1 (word 2), word_mul d (word 2))) ==> P (v1,d))
       ==> !v v1. P (v:N word,v1:N word)`,
  GEN_TAC THEN DISCH_THEN(LABEL_TAC "step") THEN
  SUBGOAL_THEN `!n (v:N word) (d:N word). dimword(:N) - val v = n ==> P (v,d)`
    (fun th -> MESON_TAC[th]) THEN
  MATCH_MP_TAC num_WF THEN X_GEN_TAC `n:num` THEN DISCH_THEN(LABEL_TAC "ih") THEN
  MAP_EVERY X_GEN_TAC [`v:N word`; `d:N word`] THEN DISCH_TAC THEN
  USE_THEN "step" MATCH_MP_TAC THEN
  REWRITE_TAC[DE_MORGAN_THM; d_word_msb; NOT_LE] THEN STRIP_TAC THEN
  USE_THEN "ih" (MP_TAC o SPEC `dimword(:N) - val(word_mul (v:N word) (word 2))`) THEN
  ANTS_TAC THENL
   [MP_TAC(SPEC `v:N word` LBIGAUX_VAL_DOUBLE) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN SUBST1_TAC THEN UNDISCH_TAC `dimword(:N) - val (v:N word) = n` THEN
    UNDISCH_TAC `~(v:N word = word 0)` THEN REWRITE_TAC[GSYM VAL_EQ_0] THEN
    MP_TAC(ISPEC `v:N word` w2n_lt) THEN ARITH_TAC;
    MESON_TAC[]]);;

let single_div_def = new_definition
  `single_div (x1:N word) (x2:N word) (y:N word) =
     (word ((val x1 * dimword(:N) + val x2) DIV val y):N word,
      word ((val x1 * dimword(:N) + val x2) MOD val y):N word)`;;

let mw_simple_div_def = cake_def
  `(mw_simple_div (x:N word) [] (y:N word) = ([]:(N word)list,x,T)) /\
   (mw_simple_div x (CONS x1 xs) y =
      let c1 = word_ult x y in
      match single_div x x1 y with (q,r) ->
      match mw_simple_div r xs y with (qs,r,c) -> (CONS q qs,r,(c /\ c1)))`;;

let mw_div_test_def = cake_def_wf
  `MEASURE (\p:N word#N word#N word#N word#N word#N word. val (FST p))`
  (REWRITE_TAC WF_REL_THMS THEN BETA_TAC THEN REWRITE_TAC[FST] THEN
   REPEAT STRIP_TAC THEN POP_ASSUM MP_TAC THEN REWRITE_TAC[w2n_n2w] THEN
   MP_TAC(SPECL [`val (q:N word) - 1`; `dimword(:N)`] MOD_LE) THEN ARITH_TAC)
  `mw_div_test (q:N word) (u1:N word) (u2:N word) (u3:N word) (v1:N word) (v2:N word) =
     if mw_cmp [u3;u2;u1] (mw_mul_by_single q [v2;v1]) = SOME T
     then let q2 = word (val q - 1) in
          let s = single_mul q2 v1 (word 0) in
            if mw_cmp [u2;u1] (FST (mw_add [FST s; SND s] [word 0;word 1] F)) = SOME T
            then mw_div_test q2 u1 u2 u3 v1 v2
            else q2
     else q`;;
let LBIGAUX_MW_CMP_SOME_T = prove
 (`!xs ys:(N word)list.
     LENGTH xs = LENGTH ys ==> (mw_cmp xs ys = SOME T <=> mw2n xs < mw2n ys)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[mw_cmp_thm] THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[option_DISTINCT; option_INJ; LT_REFL]);;

(* HOL4 mw_div_test_ind (the kit gives no induction theorem for this      *)
(* definition: the recursive call is under let; proved by induction on q) *)

let mw_div_test_ind = prove
 (`!P. (!q u1 u2 u3 v1 v2.
         (!q2 s. mw_cmp [u3;u2;u1] (mw_mul_by_single q [v2;v1]) = SOME T /\
                 q2 = word (val q - 1) /\ s = single_mul q2 v1 (word 0) /\
                 mw_cmp [u2;u1] (FST (mw_add [FST s; SND s] [word 0; word 1] F)) =
                 SOME T
                 ==> P q2 u1 u2 u3 v1 v2)
         ==> P q u1 u2 u3 v1 v2)
       ==> !q u1 u2 u3 v1 v2.
             P (q:N word) (u1:N word) (u2:N word) (u3:N word) (v1:N word) (v2:N word)`,
  GEN_TAC THEN DISCH_THEN(LABEL_TAC "step") THEN
  SUBGOAL_THEN `!n q u1 u2 u3 v1 v2.
      val (q:N word) = n
      ==> (P:N word->N word->N word->N word->N word->N word->bool)
            q u1 u2 u3 v1 v2`
    (fun th -> MESON_TAC[th]) THEN
  MATCH_MP_TAC num_WF THEN X_GEN_TAC `n:num` THEN DISCH_THEN(LABEL_TAC "ih") THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN USE_THEN "step" MATCH_MP_TAC THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  USE_THEN "ih" (MP_TAC o SPEC `val (q2:N word)`) THEN ANTS_TAC THENL
   [ALL_TAC; MESON_TAC[]] THEN
  UNDISCH_TAC `mw_cmp [u3:N word;u2;u1] (mw_mul_by_single (q:N word) [v2;v1]) = SOME T` THEN
  SUBGOAL_THEN `LENGTH [u3:N word;u2;u1] = LENGTH (mw_mul_by_single (q:N word) [v2;v1])`
    (fun th -> REWRITE_TAC[MATCH_MP LBIGAUX_MW_CMP_SOME_T th]) THENL
   [REWRITE_TAC[LENGTH_mw_mul_by_single; LENGTH] THEN ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[mw_mul_by_single_lemma] THEN
  ASM_REWRITE_TAC[w2n_n2w] THEN
  ASM_CASES_TAC `n = 0` THEN ASM_REWRITE_TAC[MULT_CLAUSES; LT] THEN
  MP_TAC(SPECL [`n - 1`; `dimword(:N)`] MOD_LE) THEN
  UNDISCH_TAC `~(n = 0)` THEN ARITH_TAC);;
let mw_div_guess_def = new_definition
  `mw_div_guess (us:(N word)list) (ys:(N word)list) =
     let q = if val (HD us) < val (HD ys)
             then FST (single_div (HD us) (HD (TL us)) (HD ys))
             else word (dimword(:N) - 1) in
     let q2 = mw_div_test q (HD us) (HD (TL us)) (HD (TL (TL us)))
                          (HD ys) (HD (TL ys)) in
       q2`;;

let mw_div_adjust_def = new_definition
  `mw_div_adjust (q:N word) zs ys =
     if mw_cmp zs (mw_mul_by_single q ys) = SOME T then word (val q - 1) else q`;;

let mw_div_aux_def = cake_def_wf
  `MEASURE (\p:(N word)list#(N word)list#(N word)list. LENGTH (FST p))`
  (REWRITE_TAC WF_REL_THMS THEN BETA_TAC THEN REWRITE_TAC[FST] THEN
   REPEAT STRIP_TAC THEN ASM_SIMP_TAC[LENGTH_FRONT] THEN
   FIRST_X_ASSUM(MP_TAC o check (is_neg o concl)) THEN
   REWRITE_TAC[GSYM LENGTH_EQ_NIL] THEN ARITH_TAC)
  `mw_div_aux (zs1:(N word)list) (zs2:(N word)list) (ys:(N word)list) =
     if zs1 = [] then ([],zs2) else
       let zs2 = CONS (LAST zs1) zs2 in
       let zs1 = BUTLAST zs1 in
       let q = mw_div_guess (REVERSE zs2) (REVERSE ys) in
       let q = mw_div_adjust q zs2 ys in
       let zs2 = FST (mw_sub zs2 (mw_mul_by_single q ys) T) in
       match mw_div_aux zs1 (BUTLAST zs2) ys with (qs,rs) -> (CONS q qs,rs)`;;
let mw_div_aux_ind = cake_ind "mw_div_aux";;
let mw_div_def = cake_def
  `mw_div (xs:(N word)list) (ys:(N word)list) =
     let xs = mw_fix xs in
     let ys = mw_fix ys in
       if LENGTH xs < LENGTH ys then
         ([],APPEND xs (REPLICATE (LENGTH ys - LENGTH xs) (word 0)),T)
       else if LENGTH ys = 1 then
         match mw_simple_div (word 0) (REVERSE xs) (HD ys) with (qs,r,c) ->
           (REVERSE qs,[r],c)
       else
         let d = calc_d (LAST ys, word 1) in
         let xs = APPEND (mw_mul_by_single d xs) [word 0] in
         let xs1 = BUTLASTN (LENGTH ys) xs in
         let xs2 = LASTN (LENGTH ys) xs in
         let ys = BUTLAST (mw_mul_by_single d ys) in
         match mw_div_aux xs1 xs2 ys with (qs,rs) ->
         match mw_simple_div (word 0) (REVERSE rs) d with (rs,r,c) ->
           (REVERSE qs,REVERSE rs,c)`;;

(* HOL4's variable mod is renamed md (mod is a HOL Light constant) *)

let mwi_divmod_def = cake_def
  `mwi_divmod (s,xs:(N word)list) (t,ys:(N word)list) =
     match mw_div xs ys with (res,md,c) ->
     let res = mw_fix res in
     let md = mw_fix md in
     let res = if s = t then res else if md = [] then res else mw_addv res [] T in
     let res_sign = (if res = [] then F else ~(s = t)) in
     let md = if s = t then md else if md = [] then md else mw_subv ys md in
     let md_sign = (if md = [] then F else t) in
       (c,(res_sign,res),(md_sign,md))`;;

let mwi_div_def = new_definition
  `mwi_div (s_xs:bool#(N word)list) t_ys = FST (SND (mwi_divmod s_xs t_ys))`;;

let mwi_mod_def = new_definition
  `mwi_mod (s_xs:bool#(N word)list) t_ys = SND (SND (mwi_divmod s_xs t_ys))`;;
(* ------------------------------------------------------------------------- *)
(* top-level entry point                                                     *)
(* HOL4's constructors Add Sub Mul Div Mod Lt Dec and the constant int_op    *)
(* are prefixed with multiword_ (names of the CakeML layer); Eq is kept.     *)
(* ------------------------------------------------------------------------- *)

let mw_op_INDUCT,mw_op_RECURSION =
  cake_type "mw_op = multiword_Add | multiword_Sub | multiword_Mul | multiword_Div | multiword_Mod | multiword_Lt | Eq | multiword_Dec";;

let int_op_def = cake_def
  `(multiword_int_op multiword_Add i j = i + j) /\
   (multiword_int_op multiword_Sub i j = i - j) /\
   (multiword_int_op multiword_Mul i j = i * j) /\
   (multiword_int_op multiword_Div i j = int_div i j) /\
   (multiword_int_op multiword_Mod i j = integer_int_mod i j) /\
   (multiword_int_op multiword_Lt i j = if i < j then &1 else &0) /\
   (multiword_int_op Eq i j = if i = j then &1 else &0:int) /\
   (multiword_int_op multiword_Dec i j = &0)`;;

let mwi_op_def = cake_def
  `(mwi_op multiword_Add s_xs t_ys = mwi_add s_xs t_ys:bool#(N word)list) /\
   (mwi_op multiword_Sub s_xs t_ys = mwi_sub s_xs t_ys) /\
   (mwi_op multiword_Mul s_xs t_ys = mwi_mul s_xs t_ys) /\
   (mwi_op multiword_Div s_xs t_ys = mwi_div s_xs t_ys) /\
   (mwi_op multiword_Mod s_xs t_ys = mwi_mod s_xs t_ys) /\
   (mwi_op multiword_Lt s_xs t_ys = i2mw (if mwi_lt s_xs t_ys then &1 else &0)) /\
   (mwi_op Eq s_xs t_ys = i2mw (if mwi_eq s_xs t_ys then &1 else &0)) /\
   (mwi_op multiword_Dec s_xs t_ys = (F,[]))`;;
let LENGTH_mw_simple_div = prove
 (`!xs x (ys:N word) qs r c.
     mw_simple_div x xs ys = (qs,r,c) ==> LENGTH xs = LENGTH qs`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[mw_simple_div_def; LET_DEF; LET_END_DEF] THEN
  REPEAT GEN_TAC THENL
   [REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN REPEAT VAR_EQ_TAC THEN
    REWRITE_TAC[LENGTH];
    REPEAT PAIRARG_TAC THEN REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN
    REPEAT VAR_EQ_TAC THEN REWRITE_TAC[LENGTH; SUC_INJ] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[]]);;

let LBIGAUX_SINGLE_DIV = prove
 (`!(x:N word) x1 y.
     val x < val y
     ==> val (FST (single_div x x1 y)) = (val x * dimword(:N) + val x1) DIV val y /\
         val (SND (single_div x x1 y)) = (val x * dimword(:N) + val x1) MOD val y`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[single_div_def; w2n_n2w] THEN
  SUBGOAL_THEN `~(val (y:N word) = 0)` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THEN MATCH_MP_TAC MOD_LT THENL
   [ASM_SIMP_TAC[RDIV_LT_EQ] THEN
    SUBGOAL_THEN `SUC (val (x:N word)) * dimword(:N) <= val (y:N word) * dimword(:N)`
    MP_TAC THENL
     [REWRITE_TAC[LE_MULT_RCANCEL] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(ISPEC `x1:N word` w2n_lt) THEN REWRITE_TAC[MULT_CLAUSES] THEN ARITH_TAC;
    TRANS_TAC LT_TRANS `val (y:N word)` THEN REWRITE_TAC[w2n_lt; MOD_LT_EQ] THEN
    ASM_ARITH_TAC]);;

let LBIGAUX_DIVMOD_STEP = prove
 (`!a w r y. ~(y = 0)
     ==> (a * w + r) DIV y = (a DIV y) * w + ((a MOD y) * w + r) DIV y /\
         (a * w + r) MOD y = ((a MOD y) * w + r) MOD y`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(SPECL [`a:num`; `y:num`] DIVISION) THEN ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `q = a DIV y` THEN ABBREV_TAC `m = a MOD y` THEN
  DISCH_THEN(CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC) THEN
  REWRITE_TAC[ARITH_RULE `(q * y + m) * w + r = ((q * w) * y) + (m * w + r)`] THEN
  ASM_SIMP_TAC[DIV_MULT_ADD; MOD_MULT_ADD]);;

let LBIGAUX_MW_SIMPLE_DIV = prove
 (`!xs (x:N word) y qs r c.
     mw_simple_div x xs y = (qs,r,c) /\ word_ult x y
     ==> mw2n (REVERSE qs) =
         (val x * dimwords (LENGTH xs) (:N) + mw2n (REVERSE xs)) DIV val y /\
         val r = (val x * dimwords (LENGTH xs) (:N) + mw2n (REVERSE xs)) MOD val y /\ c`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[mw_simple_div_def; LET_DEF; LET_END_DEF; WORD_ULT] THEN
  REPEAT GEN_TAC THENL
   [REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN REPEAT VAR_EQ_TAC THEN
    REWRITE_TAC[REVERSE; mw2n_def; LENGTH; dimwords_thm; MULT_CLAUSES; ADD_CLAUSES] THEN
    ASM_SIMP_TAC[DIV_LT; MOD_LT];
    ALL_TAC] THEN
  REPEAT PAIRARG_TAC THEN REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN REPEAT VAR_EQ_TAC THEN
  SUBGOAL_THEN `val (q:N word) = (val (x:N word) * dimword(:N) + val (h:N word)) DIV
                val (y:N word) /\
                val (r':N word) = (val x * dimword(:N) + val h) MOD val y`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(SPECL [`x:N word`; `h:N word`; `y:N word`] LBIGAUX_SINGLE_DIV) THEN
    ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `~(val (y:N word) = 0)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`r':N word`; `y:N word`; `qs':(N word)list`; `r:N word`;
                                `c':bool`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[WORD_ULT; MOD_LT_EQ]; ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP LENGTH_mw_simple_div) THEN
  REWRITE_TAC[REVERSE; mw2n_msf; LENGTH_REVERSE; LENGTH; dimwords_thm] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[ARITH_RULE `x * d * w + r + w * h = (x * d + h) * w + r`] THEN
  MP_TAC(SPECL [`val (x:N word) * dimword(:N) + val (h:N word)`;
                `dimwords (LENGTH (t:(N word)list)) (:N)`;
                `mw2n (REVERSE (t:(N word)list))`; `val (y:N word)`]
    LBIGAUX_DIVMOD_STEP) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN SUBST1_TAC) THEN
  ARITH_TAC);;

let mw_simple_div_thm = prove
 (`!xs y qs (r:N word) c.
     mw_simple_div (word 0) xs y = (qs,r,c) /\ word_ult (word 0) y
     ==> mw2n (REVERSE qs) = mw2n (REVERSE xs) DIV val y /\
         val r = mw2n (REVERSE xs) MOD val y /\ c`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP LBIGAUX_MW_SIMPLE_DIV) THEN
  REWRITE_TAC[VAL_WORD_0; MULT_CLAUSES; ADD_CLAUSES]);;

(* arithmetic of the quotient digit estimates of Knuth's algorithm D *)

let LBIGAUX_DIV_TOP_LE = prove
 (`!e t w z y zr.
     z = zr + e * t /\ e * w <= y /\ zr < e ==> (z DIV y) * w <= t`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM NOT_LT] THEN DISCH_TAC THEN
  SUBGOAL_THEN `(z DIV y) * (e * w) <= z` MP_TAC THENL
   [TRANS_TAC LE_TRANS `(z DIV y) * y` THEN CONJ_TAC THENL
     [ASM_REWRITE_TAC[LE_MULT_LCANCEL];
      ONCE_REWRITE_TAC[MULT_SYM] THEN REWRITE_TAC[DIV_MUL_LE]];
    ALL_TAC] THEN
  SUBGOAL_THEN `e * (t + 1) <= e * ((z DIV y) * w)` MP_TAC THENL
   [REWRITE_TAC[LE_MULT_LCANCEL] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  UNDISCH_TAC `zr < e` THEN UNDISCH_TAC `z = zr + e * t` THEN
  ARITH_TAC);;

let LBIGAUX_DIV_TOP_LT = prove
 (`!e t w z y zr k.
     z = zr + e * t /\ e * w <= y /\ zr < e /\ t < k * w ==> z DIV y < k`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`e:num`; `t:num`; `w:num`; `z:num`; `y:num`; `zr:num`]
    LBIGAUX_DIV_TOP_LE) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  SUBGOAL_THEN `(z DIV y) * w < k * w` MP_TAC THENL
   [ASM_ARITH_TAC; REWRITE_TAC[LT_MULT_RCANCEL] THEN ARITH_TAC]);;

let LBIGAUX_DIV_TOP_UPPER = prove
 (`!e t w z y zr yr r.
     z = zr + e * t /\ y = yr + e * w /\ yr < e /\ r * w <= t /\
     z DIV y < w /\ ~(y = 0)
     ==> r <= z DIV y + 1`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM NOT_LT] THEN DISCH_TAC THEN
  ABBREV_TAC `q = z DIV y` THEN
  SUBGOAL_THEN `z < (q + 1) * y` ASSUME_TAC THENL
   [MP_TAC(SPECL [`z:num`; `y:num`] DIVISION) THEN ASM_REWRITE_TAC[] THEN
    ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(q + 1) * y <= (q + 1) * (e * (w + 1))` ASSUME_TAC THENL
   [REWRITE_TAC[LE_MULT_LCANCEL] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `e * t < e * ((q + 1) * (w + 1))` MP_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`z < (q + 1) * y`;
      `(q + 1) * y <= (q + 1) * (e * (w + 1))`; `z = zr + e * t`] THEN
    ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[LT_MULT_LCANCEL] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(q + 2) * w <= r * w` MP_TAC THENL
   [REWRITE_TAC[LE_MULT_RCANCEL] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY UNDISCH_TAC [`r * w <= t`; `t < (q + 1) * (w + 1)`; `q < w`] THEN
  ARITH_TAC);;

let LBIGAUX_DIV_TEST_OUTER = prove
 (`!(q:N word) u1 u2 u3 v1 v2.
     mw_cmp [u3;u2;u1] (mw_mul_by_single q [v2;v1]) = SOME T <=>
     val u3 + dimword(:N) * (val u2 + dimword(:N) * val u1) <
     val q * (val v2 + dimword(:N) * val v1)`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `LENGTH [u3:N word;u2;u1] = LENGTH (mw_mul_by_single (q:N word) [v2;v1])`
    (fun th -> REWRITE_TAC[MATCH_MP LBIGAUX_MW_CMP_SOME_T th]) THENL
   [REWRITE_TAC[LENGTH_mw_mul_by_single; LENGTH] THEN ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[mw_mul_by_single_lemma; mw2n_def; MULT_CLAUSES; ADD_CLAUSES]);;

let LBIGAUX_MUL_BOUND2 = prove
 (`!a b d. a + 2 <= d /\ b < d ==> a * b + d < d * d`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `a * b <= (d - 2) * (d - 1)` MP_TAC THENL
   [MATCH_MP_TAC LE_MULT2 THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `?k. d = k + 2` (CHOOSE_THEN SUBST_ALL_TAC) THENL
   [EXISTS_TAC `d - 2` THEN ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[ARITH_RULE `(k + 2) - 2 = k /\ (k + 2) - 1 = k + 1`] THEN
  ARITH_TAC);;

let LBIGAUX_DIV_TEST_INNER = prove
 (`!(q2:N word) v1 u1 u2.
     val q2 + 2 <= dimword(:N)
     ==> (mw_cmp [u2;u1]
            (FST (mw_add [FST (single_mul q2 v1 (word 0));
                          SND (single_mul q2 v1 (word 0))] [word 0; word 1] F)) =
          SOME T <=>
          val u2 + dimword(:N) * val u1 < val q2 * val v1 + dimword(:N))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPEC `single_mul (q2:N word) v1 (word 0)` PAIR_SURJECTIVE) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`lo:N word`; `hi:N word`] THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP single_mul_thm) THEN
  ASM_REWRITE_TAC[VAL_WORD_0; ADD_CLAUSES] THEN DISCH_TAC THEN
  MP_TAC(ISPEC `mw_add [lo:N word;hi] [word 0; word 1] F` PAIR_SURJECTIVE) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`zs:(N word)list`; `c:bool`] THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP LBIGAUX_MW_ADD_2) THEN
  MP_TAC(SPECL [`[lo:N word;hi]`; `[word 0:N word; word 1]`; `F`; `zs:(N word)list`;
                `c:bool`] mw_add_thm) THEN
  ASM_REWRITE_TAC[LENGTH; FST] THEN
  REWRITE_TAC[mw2n_def; dimwords_thm; VAL_WORD_0; VAL_WORD_1; BITVAL_CLAUSES;
              MULT_CLAUSES; ADD_CLAUSES] THEN
  SUBGOAL_THEN `LENGTH [u2:N word;u1] = LENGTH [z1:N word;z2]`
    (fun th -> REWRITE_TAC[MATCH_MP LBIGAUX_MW_CMP_SOME_T th]) THENL
   [REWRITE_TAC[LENGTH]; ALL_TAC] THEN
  REWRITE_TAC[mw2n_def; MULT_CLAUSES; ADD_CLAUSES] THEN
  MP_TAC(SPECL [`val (q2:N word)`; `val (v1:N word)`; `dimword(:N)`]
    LBIGAUX_MUL_BOUND2) THEN
  ASM_REWRITE_TAC[w2n_lt] THEN
  BOOL_CASES_TAC `c:bool` THEN REWRITE_TAC[BITVAL_CLAUSES] THEN
  ASM_ARITH_TAC);;

let LBIGAUX_DIV_TEST = prove
 (`!q u1 u2 u3 v1 v2 qs.
     qs <= val (q:N word) /\
     (!k. val (u3:N word) + dimword(:N) * (val (u2:N word) + dimword(:N) * val (u1:N word)) <
          k * (val (v2:N word) + dimword(:N) * val (v1:N word)) ==> qs < k)
     ==> qs <= val (mw_div_test q u1 u2 u3 v1 v2) /\
         val (mw_div_test q u1 u2 u3 v1 v2) * (val v2 + dimword(:N) * val v1) <=
         val u3 + dimword(:N) * (val u2 + dimword(:N) * val u1)`,
  MATCH_MP_TAC mw_div_test_ind THEN REPEAT GEN_TAC THEN DISCH_THEN(LABEL_TAC "ih") THEN
  X_GEN_TAC `qs:num` THEN STRIP_TAC THEN
  ONCE_REWRITE_TAC[mw_div_test_def] THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF; LBIGAUX_DIV_TEST_OUTER] THEN
  COND_CASES_TAC THENL [ALL_TAC; ASM_ARITH_TAC] THEN
  SUBGOAL_THEN `qs < val (q:N word)` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `val (word (val (q:N word) - 1):N word) = val q - 1` ASSUME_TAC THENL
   [REWRITE_TAC[w2n_n2w] THEN MATCH_MP_TAC MOD_LT THEN
    MP_TAC(ISPEC `q:N word` w2n_lt) THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `val (word (val (q:N word) - 1):N word) + 2 <= dimword(:N)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN MP_TAC(ISPEC `q:N word` w2n_lt) THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[LBIGAUX_DIV_TEST_INNER] THEN COND_CASES_TAC THENL
   [USE_THEN "ih" (MP_TAC o SPECL [`word (val (q:N word) - 1):N word`;
       `single_mul (word (val (q:N word) - 1)) (v1:N word) (word 0)`]) THEN
    ASM_SIMP_TAC[LBIGAUX_DIV_TEST_INNER; LBIGAUX_DIV_TEST_OUTER] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `val (q:N word) - 1 < dimword(:N)` MP_TAC THENL
   [MP_TAC(ISPEC `q:N word` w2n_lt) THEN ARITH_TAC; ALL_TAC] THEN
  UNDISCH_TAC `~(val (u2:N word) + dimword (:N) * val (u1:N word) <
                 (val (q:N word) - 1) * val (v1:N word) + dimword (:N))` THEN
  ABBREV_TAC `p = val (q:N word) - 1` THEN REWRITE_TAC[NOT_LT] THEN
  REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `dimword(:N) * (p * val (v1:N word) + dimword(:N)) <=
                dimword(:N) * (val (u2:N word) + dimword(:N) * val (u1:N word))`
  MP_TAC THENL [ASM_REWRITE_TAC[LE_MULT_LCANCEL]; ALL_TAC] THEN
  SUBGOAL_THEN `p * val (v2:N word) < dimword(:N) * dimword(:N)` MP_TAC THENL
   [MATCH_MP_TAC LT_MULT2 THEN ASM_REWRITE_TAC[w2n_lt]; ALL_TAC] THEN
  REWRITE_TAC[LEFT_ADD_DISTRIB; RIGHT_ADD_DISTRIB] THEN ARITH_TAC);;

let multiword_LESS_EQ_LENGTH = prove
 (`!xs:A list n. n <= LENGTH xs ==> ?xs1 xs2. xs = APPEND xs1 xs2 /\ LENGTH xs1 = n`,
  REPEAT STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`TAKE n (xs:A list)`; `DROP n (xs:A list)`] THEN
  ASM_SIMP_TAC[TAKE_DROP; LENGTH_TAKE]);;

let LESS_EQ_LENGTH_ALT = prove
 (`!xs:A list n. n <= LENGTH xs ==> ?ys1 ys2. xs = APPEND ys1 ys2 /\ LENGTH ys2 = n`,
  REPEAT STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`TAKE (LENGTH xs - n) (xs:A list)`;
                        `DROP (LENGTH xs - n) (xs:A list)`] THEN
  REWRITE_TAC[TAKE_DROP; LENGTH_DROP] THEN ASM_ARITH_TAC);;

let LBIGAUX_LENGTH_2 = prove
 (`!l:A list. LENGTH l = 2 <=> ?a b. l = [a;b]`,
  REWRITE_TAC[ARITH_RULE `2 = SUC(SUC 0)`; LENGTH_EQ_CONS; LENGTH_EQ_NIL] THEN
  MESON_TAC[]);;

let LBIGAUX_LENGTH_3 = prove
 (`!l:A list. LENGTH l = 3 <=> ?a b c. l = [a;b;c]`,
  REWRITE_TAC[ARITH_RULE `3 = SUC(SUC(SUC 0))`; LENGTH_EQ_CONS; LENGTH_EQ_NIL] THEN
  MESON_TAC[]);;

let LBIGAUX_TOP_WORDS2 = prove
 (`!ys:A list. 2 <= LENGTH ys
     ==> ?yr v2 v1. ys = APPEND yr [v2;v1] /\ LENGTH yr = LENGTH ys - 2`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP LESS_EQ_LENGTH_ALT) THEN
  REWRITE_TAC[LBIGAUX_LENGTH_2] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN MAP_EVERY EXISTS_TAC [`ys1:A list`; `a:A`; `b:A`] THEN
  REWRITE_TAC[LENGTH_APPEND; LENGTH] THEN ARITH_TAC);;

let LBIGAUX_TOP_WORDS3 = prove
 (`!zs:A list. 3 <= LENGTH zs
     ==> ?zr u3 u2 u1. zs = APPEND zr [u3;u2;u1] /\ LENGTH zr = LENGTH zs - 3`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP LESS_EQ_LENGTH_ALT) THEN
  REWRITE_TAC[LBIGAUX_LENGTH_3] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN MAP_EVERY EXISTS_TAC [`ys1:A list`; `a:A`; `b:A`; `c:A`] THEN
  REWRITE_TAC[LENGTH_APPEND; LENGTH] THEN ARITH_TAC);;

let LBIGAUX_DIGIT_CORE = prove
 (`!(u1:N word) u2 u3 v1 v2 z y zr yr ee.
     z = zr + ee * (val u3 + dimword(:N) * (val u2 + dimword(:N) * val u1)) /\
     y = yr + ee * (val v2 + dimword(:N) * val v1) /\
     zr < ee /\ yr < ee /\ ~(val v1 = 0) /\ z < dimword(:N) * y
     ==> z DIV y <=
         val (mw_div_test (if val u1 < val v1 then FST (single_div u1 u2 v1)
                           else word (dimword(:N) - 1)) u1 u2 u3 v1 v2) /\
         val (mw_div_test (if val u1 < val v1 then FST (single_div u1 u2 v1)
                           else word (dimword(:N) - 1)) u1 u2 u3 v1 v2) <=
         z DIV y + 1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(ASSUME_TAC o SYM o check (is_var o lhs o concl))) THEN
  ABBREV_TAC `ww = val (v2:N word) + dimword(:N) * val (v1:N word)` THEN
  ABBREV_TAC `tt = val (u3:N word) + dimword(:N) * (val (u2:N word) +
                   dimword(:N) * val (u1:N word))` THEN
  SUBGOAL_THEN `dimword(:N) <= ww` ASSUME_TAC THENL
   [EXPAND_TAC "ww" THEN
    MATCH_MP_TAC(ARITH_RULE `d * 1 <= d * v ==> d <= a + d * v`) THEN
    REWRITE_TAC[LE_MULT_LCANCEL] THEN
    UNDISCH_TAC `~(val (v1:N word) = 0)` THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `~(y = 0)` ASSUME_TAC THENL
   [UNDISCH_TAC `yr + ee * ww = y` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[ADD_EQ_0; MULT_EQ_0] THEN MP_TAC ZERO_LT_dimword THEN
    MAP_EVERY UNDISCH_TAC [`zr < ee`; `dimword(:N) <= ww`] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `z DIV y < dimword(:N)` ASSUME_TAC THENL
   [MATCH_MP_TAC DIV_thm2 THEN CONJ_TAC THENL
     [UNDISCH_TAC `~(y = 0)` THEN ARITH_TAC; FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `q0 = if val (u1:N word) < val (v1:N word) then FST (single_div u1 u2 v1)
                   else word (dimword(:N) - 1)` THEN
  SUBGOAL_THEN `z DIV y <= val (q0:N word)` ASSUME_TAC THENL
   [EXPAND_TAC "q0" THEN COND_CASES_TAC THENL
     [ASM_SIMP_TAC[LBIGAUX_SINGLE_DIV; LE_RDIV_EQ] THEN
      ONCE_REWRITE_TAC[MULT_SYM] THEN
      MATCH_MP_TAC LBIGAUX_DIV_TOP_LE THEN
      MAP_EVERY EXISTS_TAC [`ee * dimword(:N)`; `zr + ee * val (u3:N word)`] THEN
      REPEAT CONJ_TAC THENL
       [UNDISCH_TAC `zr + ee * tt = z` THEN EXPAND_TAC "tt" THEN ARITH_TAC;
        UNDISCH_TAC `yr + ee * ww = y` THEN EXPAND_TAC "ww" THEN ARITH_TAC;
        SUBGOAL_THEN `ee * (val (u3:N word) + 1) <= ee * dimword(:N)` MP_TAC THENL
         [REWRITE_TAC[LE_MULT_LCANCEL] THEN MP_TAC(ISPEC `u3:N word` w2n_lt) THEN
          ARITH_TAC;
          UNDISCH_TAC `zr < ee` THEN ARITH_TAC]];
      REWRITE_TAC[w2n_n2w] THEN MP_TAC ONE_LT_dimword THEN
      SIMP_TAC[MOD_LT; ARITH_RULE `1 < d ==> d - 1 < d`] THEN
      UNDISCH_TAC `z DIV y < dimword(:N)` THEN ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(SPECL [`q0:N word`; `u1:N word`; `u2:N word`; `u3:N word`; `v1:N word`;
                `v2:N word`; `z DIV y`] LBIGAUX_DIV_TEST) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [X_GEN_TAC `k:num` THEN DISCH_TAC THEN MATCH_MP_TAC LBIGAUX_DIV_TOP_LT THEN
    MAP_EVERY EXISTS_TAC [`ee:num`; `tt:num`; `ww:num`; `zr:num`] THEN
    ASM_REWRITE_TAC[] THEN UNDISCH_TAC `yr + ee * ww = y` THEN ARITH_TAC;
    ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC LBIGAUX_DIV_TOP_UPPER THEN
  MAP_EVERY EXISTS_TAC [`ee:num`; `tt:num`; `ww:num`; `zr:num`; `yr:num`] THEN
  ASM_REWRITE_TAC[] THEN UNDISCH_TAC `z DIV y < dimword(:N)` THEN
  UNDISCH_TAC `dimword(:N) <= ww` THEN ARITH_TAC);;

let LBIGAUX_DIGIT = prove
 (`!zs ys:(N word)list.
     2 <= LENGTH ys /\ LENGTH zs = LENGTH ys + 1 /\ ~(LAST ys = word 0) /\
     mw2n zs < dimword(:N) * mw2n ys
     ==> val (mw_div_adjust (mw_div_guess (REVERSE zs) (REVERSE ys)) zs ys) =
         mw2n zs DIV mw2n ys`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `yr:(N word)list` (X_CHOOSE_THEN `v2:N word`
    (X_CHOOSE_THEN `v1:N word` STRIP_ASSUME_TAC)) o MATCH_MP LBIGAUX_TOP_WORDS2) THEN
  SUBGOAL_THEN `3 <= LENGTH (zs:(N word)list)` MP_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `zr:(N word)list` (X_CHOOSE_THEN `u3:N word`
    (X_CHOOSE_THEN `u2:N word` (X_CHOOSE_THEN `u1:N word` STRIP_ASSUME_TAC))) o
    MATCH_MP LBIGAUX_TOP_WORDS3) THEN
  SUBGOAL_THEN `LENGTH (zr:(N word)list) = LENGTH (yr:(N word)list)` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  UNDISCH_TAC `LENGTH (zr:(N word)list) = LENGTH (zs:(N word)list) - 3` THEN
  UNDISCH_TAC `LENGTH (yr:(N word)list) = LENGTH (ys:(N word)list) - 2` THEN
  REPEAT(DISCH_THEN(K ALL_TAC)) THEN
  SUBGOAL_THEN `~(val (v1:N word) = 0)` ASSUME_TAC THENL
   [UNDISCH_TAC `~(LAST (ys:(N word)list) = word 0)` THEN
    ASM_REWRITE_TAC[LAST_APPEND; NOT_CONS_NIL; LAST; VAL_EQ_0]; ALL_TAC] THEN
  SUBGOAL_THEN `mw_div_guess (REVERSE zs) (REVERSE ys) =
     mw_div_test (if val (u1:N word) < val (v1:N word) then FST (single_div u1 u2 v1)
                  else word (dimword(:N) - 1)) u1 u2 u3 v1 (v2:N word)`
  SUBST1_TAC THENL
   [ASM_REWRITE_TAC[mw_div_guess_def; REVERSE_APPEND; REVERSE; APPEND; HD; TL;
                    LET_DEF; LET_END_DEF]; ALL_TAC] THEN
  MP_TAC(SPECL [`u1:N word`; `u2:N word`; `u3:N word`; `v1:N word`; `v2:N word`;
                `mw2n (zs:(N word)list)`; `mw2n (ys:(N word)list)`;
                `mw2n (zr:(N word)list)`; `mw2n (yr:(N word)list)`;
                `dimwords (LENGTH (yr:(N word)list)) (:N)`] LBIGAUX_DIGIT_CORE) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[mw2n_APPEND; mw2n_def] THEN ARITH_TAC;
      ASM_REWRITE_TAC[mw2n_APPEND; mw2n_def] THEN ARITH_TAC;
      UNDISCH_TAC `LENGTH (zr:(N word)list) = LENGTH (yr:(N word)list)` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[mw2n_lt];
      REWRITE_TAC[mw2n_lt];
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (is_var o lhs o concl))) THEN
  ABBREV_TAC `g = mw_div_test (if val (u1:N word) < val (v1:N word)
                               then FST (single_div u1 u2 v1)
                               else word (dimword(:N) - 1)) u1 u2 u3 v1 (v2:N word)` THEN
  STRIP_TAC THEN REWRITE_TAC[mw_div_adjust_def] THEN
  SUBGOAL_THEN `LENGTH (zs:(N word)list) = LENGTH (mw_mul_by_single (g:N word) ys)`
    (fun th -> REWRITE_TAC[MATCH_MP LBIGAUX_MW_CMP_SOME_T th]) THENL
   [ASM_REWRITE_TAC[LENGTH_mw_mul_by_single]; ALL_TAC] THEN
  REWRITE_TAC[mw_mul_by_single_lemma] THEN
  SUBGOAL_THEN `~(mw2n (ys:(N word)list) = 0)` ASSUME_TAC THENL
   [DISCH_TAC THEN
    UNDISCH_TAC `mw2n (zs:(N word)list) < dimword(:N) * mw2n (ys:(N word)list)` THEN
    ASM_REWRITE_TAC[MULT_CLAUSES] THEN ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`mw2n (zs:(N word)list)`; `mw2n (ys:(N word)list)`] DIVISION) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `mw2n (zs:(N word)list) DIV mw2n (ys:(N word)list) < dimword(:N)`
  MP_TAC THENL
   [MATCH_MP_TAC DIV_thm2 THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `~(mw2n (ys:(N word)list) = 0)` THEN ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY UNDISCH_TAC
   [`mw2n (zs:(N word)list) DIV mw2n (ys:(N word)list) <= val (g:N word)`;
    `val (g:N word) <= mw2n (zs:(N word)list) DIV mw2n (ys:(N word)list) + 1`] THEN
  ABBREV_TAC `qq = mw2n (zs:(N word)list) DIV mw2n (ys:(N word)list)` THEN
  ABBREV_TAC `rr = mw2n (zs:(N word)list) MOD mw2n (ys:(N word)list)` THEN
  ABBREV_TAC `zz = mw2n (zs:(N word)list)` THEN
  ABBREV_TAC `yy = mw2n (ys:(N word)list)` THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `val (g:N word) = qq \/ val g = qq + 1` MP_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`val (g:N word) <= qq + 1`; `qq <= val (g:N word)`] THEN
    ARITH_TAC; ALL_TAC] THEN
  STRIP_TAC THEN FIRST_ASSUM(fun th -> REWRITE_TAC[th]) THEN COND_CASES_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`zz < qq * yy`; `zz = qq * yy + rr`] THEN ARITH_TAC;
    ASM_REWRITE_TAC[];
    REWRITE_TAC[ADD_SUB; w2n_n2w] THEN MATCH_MP_TAC MOD_LT THEN
    FIRST_ASSUM ACCEPT_TAC;
    MAP_EVERY UNDISCH_TAC [`~(zz < (qq + 1) * yy)`; `zz = qq * yy + rr`; `rr < yy`] THEN
    ARITH_TAC]);;

let LBIGAUX_LENGTH_BUTLAST = prove
 (`!l:A list. LENGTH (BUTLAST l) = LENGTH l - 1`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[BUTLAST; LENGTH] THENL [ARITH_TAC; ALL_TAC] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[LENGTH] THENL
   [ARITH_TAC;
    UNDISCH_TAC `~(t:A list = [])` THEN REWRITE_TAC[GSYM LENGTH_EQ_NIL] THEN
    ARITH_TAC]);;

let LBIGAUX_LENGTH_MW_SUB = prove
 (`!xs ys:(N word)list c. LENGTH (FST (mw_sub xs ys c)) = LENGTH xs`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPEC `mw_sub (xs:(N word)list) ys c` PAIR_SURJECTIVE) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[FST] THEN
  ASM_MESON_TAC[LENGTH_mw_sub]);;

let LBIGAUX_MW2N_BUTLAST = prove
 (`!xs:(N word)list.
     mw2n xs < dimwords (LENGTH xs - 1) (:N) ==> mw2n (BUTLAST xs) = mw2n xs`,
  GEN_TAC THEN ASM_CASES_TAC `xs:(N word)list = []` THEN
  ASM_REWRITE_TAC[BUTLAST] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP LBIGAUX_MW2N_FRONT_LAST th]) THEN
  REWRITE_TAC[LBIGAUX_LENGTH_BUTLAST] THEN
  ASM_CASES_TAC `val (LAST (xs:(N word)list)) = 0` THEN
  ASM_REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES] THEN
  MATCH_MP_TAC(ARITH_RULE `w * 1 <= w * v ==> a + w * v < w ==> c`) THEN
  REWRITE_TAC[LE_MULT_LCANCEL] THEN ASM_ARITH_TAC);;

let LENGTH_mw_div_aux = prove
 (`!ts1 ts2 ys qs rs:(N word)list.
     mw_div_aux ts1 ts2 ys = (qs,rs) /\ LENGTH ts2 = LENGTH ys
     ==> LENGTH rs = LENGTH ys /\ LENGTH qs = LENGTH ts1`,
  MATCH_MP_TAC mw_div_aux_ind THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV o LAND_CONV) [mw_div_aux_def] THEN
  ASM_CASES_TAC `zs1:(N word)list = []` THEN
  ASM_REWRITE_TAC[PAIR_EQ; LET_DEF; LET_END_DEF] THENL
   [STRIP_TAC THEN REPEAT VAR_EQ_TAC THEN ASM_REWRITE_TAC[LENGTH]; ALL_TAC] THEN
  PAIRARG_TAC THEN REWRITE_TAC[PAIR_EQ] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`qs':(N word)list`; `rs':(N word)list`] o
    C MP (ASSUME `~(zs1:(N word)list = [])`)) THEN
  ASM_REWRITE_TAC[LBIGAUX_LENGTH_BUTLAST; LBIGAUX_LENGTH_MW_SUB; LENGTH] THEN
  ANTS_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[LENGTH] THEN
  UNDISCH_TAC `~(zs1:(N word)list = [])` THEN REWRITE_TAC[GSYM LENGTH_EQ_NIL] THEN
  ARITH_TAC);;

let LBIGAUX_MW_DIV_AUX = prove
 (`!zs1 zs2 ys qs rs:(N word)list.
     mw_div_aux zs1 zs2 ys = (qs,rs) /\ LENGTH zs2 = LENGTH ys /\
     2 <= LENGTH ys /\ ~(LAST ys = word 0) /\ mw2n zs2 < mw2n ys
     ==> mw2n (REVERSE qs) = mw2n (APPEND zs1 zs2) DIV mw2n ys /\
         mw2n rs = mw2n (APPEND zs1 zs2) MOD mw2n ys`,
  MATCH_MP_TAC mw_div_aux_ind THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV o LAND_CONV) [mw_div_aux_def] THEN
  ASM_CASES_TAC `zs1:(N word)list = []` THEN
  ASM_REWRITE_TAC[PAIR_EQ; LET_DEF; LET_END_DEF] THENL
   [STRIP_TAC THEN REPEAT VAR_EQ_TAC THEN
    ASM_SIMP_TAC[REVERSE; mw2n_def; APPEND; DIV_LT; MOD_LT]; ALL_TAC] THEN
  PAIRARG_TAC THEN REWRITE_TAC[PAIR_EQ] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`qs':(N word)list`; `rs':(N word)list`] o
    C MP (ASSUME `~(zs1:(N word)list = [])`)) THEN
  ABBREV_TAC `zz2 = CONS (LAST zs1) (zs2:(N word)list)` THEN
  ABBREV_TAC `q = mw_div_adjust (mw_div_guess (REVERSE zz2) (REVERSE ys)) zz2
                    (ys:(N word)list)` THEN
  ABBREV_TAC `zz3 = FST (mw_sub zz2 (mw_mul_by_single (q:N word) ys) T)` THEN
  SUBGOAL_THEN `LENGTH (zz2:(N word)list) = LENGTH (ys:(N word)list) + 1` ASSUME_TAC THENL
   [EXPAND_TAC "zz2" THEN ASM_REWRITE_TAC[LENGTH] THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `~(mw2n (ys:(N word)list) = 0)` ASSUME_TAC THENL
   [UNDISCH_TAC `mw2n (zs2:(N word)list) < mw2n (ys:(N word)list)` THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `mw2n (zz2:(N word)list) < dimword(:N) * mw2n (ys:(N word)list)`
  ASSUME_TAC THENL
   [EXPAND_TAC "zz2" THEN REWRITE_TAC[mw2n_def] THEN
    MP_TAC(ISPEC `LAST (zs1:(N word)list)` w2n_lt) THEN
    SUBGOAL_THEN `dimword(:N) * (mw2n (zs2:(N word)list) + 1) <=
                  dimword(:N) * mw2n (ys:(N word)list)` MP_TAC THENL
     [REWRITE_TAC[LE_MULT_LCANCEL] THEN ASM_ARITH_TAC; ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `val (q:N word) = mw2n (zz2:(N word)list) DIV mw2n (ys:(N word)list)`
  ASSUME_TAC THENL
   [EXPAND_TAC "q" THEN MATCH_MP_TAC LBIGAUX_DIGIT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `mw2n (zz3:(N word)list) = mw2n (zz2:(N word)list) MOD mw2n (ys:(N word)list) /\
                LENGTH zz3 = LENGTH ys + 1` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "zz3" THEN REWRITE_TAC[LBIGAUX_LENGTH_MW_SUB] THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(SPECL [`zz2:(N word)list`; `mw_mul_by_single (q:N word) ys`] mw_sub_thm) THEN
    ASM_REWRITE_TAC[mw_mul_by_single_lemma] THEN ANTS_TAC THENL
     [ONCE_REWRITE_TAC[MULT_SYM] THEN REWRITE_TAC[DIV_MUL_LE]; ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN
    MP_TAC(SPECL [`mw2n (zz2:(N word)list)`; `mw2n (ys:(N word)list)`] DIVISION) THEN
    ASM_REWRITE_TAC[] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `mw2n (BUTLAST (zz3:(N word)list)) = mw2n zz3` ASSUME_TAC THENL
   [MATCH_MP_TAC LBIGAUX_MW2N_BUTLAST THEN ASM_REWRITE_TAC[ADD_SUB] THEN
    TRANS_TAC LT_TRANS `mw2n (ys:(N word)list)` THEN REWRITE_TAC[mw2n_lt] THEN
    ASM_REWRITE_TAC[MOD_LT_EQ]; ALL_TAC] THEN
  SUBGOAL_THEN `LENGTH (BUTLAST (zz3:(N word)list)) = LENGTH (ys:(N word)list)`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[LBIGAUX_LENGTH_BUTLAST; ADD_SUB]; ALL_TAC] THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[MOD_LT_EQ]; ALL_TAC] THEN
  SUBGOAL_THEN `LENGTH (qs':(N word)list) = LENGTH (BUTLAST (zs1:(N word)list))`
  ASSUME_TAC THENL [ASM_MESON_TAC[LENGTH_mw_div_aux]; ALL_TAC] THEN
  SUBGOAL_THEN `mw2n (APPEND zs1 zs2:(N word)list) =
     (dimwords (LENGTH (BUTLAST (zs1:(N word)list))) (:N) * val (q:N word)) *
       mw2n (ys:(N word)list) +
     mw2n (APPEND (BUTLAST zs1) (BUTLAST zz3))` SUBST1_TAC THENL
   [FIRST_ASSUM(fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o LAND_CONV)
      [GSYM(MATCH_MP APPEND_BUTLAST_LAST th)]) THEN
    REWRITE_TAC[GSYM APPEND_ASSOC; APPEND] THEN ASM_REWRITE_TAC[mw2n_APPEND] THEN
    MP_TAC(SPECL [`mw2n (zz2:(N word)list)`; `mw2n (ys:(N word)list)`] DIVISION) THEN
    ASM_REWRITE_TAC[] THEN
    ABBREV_TAC `qq = mw2n (zz2:(N word)list) DIV mw2n (ys:(N word)list)` THEN
    ABBREV_TAC `rr = mw2n (zz2:(N word)list) MOD mw2n (ys:(N word)list)` THEN
    DISCH_THEN(CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC) THEN ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[DIV_MULT_ADD; MOD_MULT_ADD] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[REVERSE; mw2n_msf; LENGTH_REVERSE] THEN
  ARITH_TAC);;

(* the normalisation factor calc_d (v,1) is a power of 2 with              *)
(* calc_d (v,1) times (v + 1) <= dimword (HOL4: d_lemma3 to d_lemma5)      *)

let LBIGAUX_CALC_D_IND = prove
 (`!P. (!v1 d. (~(v1 = word 0 \/ word_msb v1)
                ==> P (word_mul v1 (word 2)) (word_mul d (word 2))) ==> P v1 d)
       ==> !v v1. P (v:N word) (v1:N word)`,
  GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPEC `\p:N word#N word. (P:N word->N word->bool) (FST p) (SND p)`
    calc_d_ind) THEN
  BETA_TAC THEN REWRITE_TAC[FST; SND] THEN ASM_REWRITE_TAC[]);;

let LBIGAUX_CALC_D = prove
 (`!v d:N word. ?k. calc_d (v,d) = word_mul d (word (2 EXP k)) /\
                    (~(v = word 0) ==> val v * 2 EXP k < dimword(:N))`,
  MATCH_MP_TAC LBIGAUX_CALC_D_IND THEN MAP_EVERY X_GEN_TAC [`v:N word`; `d:N word`] THEN
  DISCH_TAC THEN ONCE_REWRITE_TAC[calc_d_def] THEN COND_CASES_TAC THENL
   [EXISTS_TAC `0` THEN REWRITE_TAC[EXP; MULT_CLAUSES; w2n_lt] THEN
    CONV_TAC WORD_RULE; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o C MP (ASSUME `~(v = word 0 \/ word_msb (v:N word))`)) THEN
  DISCH_THEN(X_CHOOSE_THEN `k:num` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `SUC k` THEN CONJ_TAC THENL
   [ASM_REWRITE_TAC[EXP; WORD_MUL; WORD_MUL_ASSOC]; ALL_TAC] THEN
  DISCH_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[DE_MORGAN_THM; d_word_msb; NOT_LE]) THEN
  FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
  ASM_SIMP_TAC[LBIGAUX_VAL_DOUBLE; GSYM VAL_EQ_0] THEN
  REWRITE_TAC[EXP] THEN UNDISCH_TAC `~(v:N word = word 0)` THEN
  REWRITE_TAC[GSYM VAL_EQ_0] THEN ARITH_TAC);;

let LBIGAUX_CALC_D_BOUND = prove
 (`!v:N word. ~(v = word 0)
     ==> 1 <= val (calc_d (v,word 1)) /\
         val (calc_d (v,word 1)) * (val v + 1) <= dimword(:N)`,
  GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(SPECL [`v:N word`; `word 1:N word`] LBIGAUX_CALC_D) THEN
  DISCH_THEN(X_CHOOSE_THEN `k:num` (CONJUNCTS_THEN2 SUBST1_TAC MP_TAC)) THEN
  ASM_REWRITE_TAC[GSYM WORD_MUL; MULT_CLAUSES] THEN DISCH_TAC THEN
  SUBGOAL_THEN `~(val (v:N word) = 0)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[VAL_EQ_0]; ALL_TAC] THEN
  SUBGOAL_THEN `2 EXP k < dimword(:N)` ASSUME_TAC THENL
   [TRANS_TAC LET_TRANS `val (v:N word) * 2 EXP k` THEN ASM_REWRITE_TAC[] THEN
    GEN_REWRITE_TAC LAND_CONV [ARITH_RULE `x = 1 * x`] THEN
    REWRITE_TAC[LE_MULT_RCANCEL] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[w2n_n2w; MOD_LT] THEN
  CONJ_TAC THENL [REWRITE_TAC[ARITH_RULE `1 <= n <=> ~(n = 0)`; EXP_EQ_0] THEN
                  ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `k < dimindex(:N)` ASSUME_TAC THENL
   [UNDISCH_TAC `2 EXP k < dimword(:N)` THEN
    REWRITE_TAC[dimword_def; WORDSAUX_EXP2_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `dimword(:N) = 2 EXP k * 2 EXP (dimindex(:N) - k)` ASSUME_TAC THENL
   [REWRITE_TAC[dimword_def; GSYM EXP_ADD] THEN AP_TERM_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `val (v:N word) < 2 EXP (dimindex(:N) - k)` ASSUME_TAC THENL
   [UNDISCH_TAC `val (v:N word) * 2 EXP k < dimword(:N)` THEN ASM_REWRITE_TAC[] THEN
    GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [MULT_SYM] THEN
    REWRITE_TAC[LT_MULT_RCANCEL] THEN SIMP_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[LE_MULT_LCANCEL] THEN ASM_ARITH_TAC);;

let LBIGAUX_NORM_DIVISOR = prove
 (`!ys:(N word)list.
     mw_ok ys /\ ~(ys = [])
     ==> 1 <= val (calc_d (LAST ys,word 1)) /\
         mw2n (BUTLAST (mw_mul_by_single (calc_d (LAST ys,word 1)) ys)) =
           val (calc_d (LAST ys,word 1)) * mw2n ys /\
         LENGTH (BUTLAST (mw_mul_by_single (calc_d (LAST ys,word 1)) ys)) =
           LENGTH ys /\
         dimwords (LENGTH ys - 1) (:N) <= val (calc_d (LAST ys,word 1)) * mw2n ys /\
         ~(LAST (BUTLAST (mw_mul_by_single (calc_d (LAST ys,word 1)) ys)) = word 0)`,
  GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(val (LAST (ys:(N word)list)) = 0)` ASSUME_TAC THENL
   [UNDISCH_TAC `mw_ok (ys:(N word)list)` THEN ASM_REWRITE_TAC[mw_ok_def; VAL_EQ_0];
    ALL_TAC] THEN
  MP_TAC(ISPEC `LAST (ys:(N word)list)` LBIGAUX_CALC_D_BOUND) THEN
  ASM_REWRITE_TAC[GSYM VAL_EQ_0] THEN
  ABBREV_TAC `d = calc_d (LAST (ys:(N word)list),word 1)` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `mw2n (ys:(N word)list) =
                mw2n (BUTLAST ys) + (dimwords (LENGTH (ys:(N word)list) - 1) (:N)) * val (LAST ys) /\ mw2n (BUTLAST ys) < (dimwords (LENGTH (ys:(N word)list) - 1) (:N))`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[LBIGAUX_MW2N_FRONT_LAST; LBIGAUX_LENGTH_BUTLAST] THEN
    REWRITE_TAC[GSYM LBIGAUX_LENGTH_BUTLAST; mw2n_lt]; ALL_TAC] THEN
  SUBGOAL_THEN `(dimwords (LENGTH (ys:(N word)list) - 1) (:N)) <= val (d:N word) * mw2n (ys:(N word)list)` ASSUME_TAC THENL
   [SUBST1_TAC(ASSUME `mw2n (ys:(N word)list) = mw2n (BUTLAST ys) + (dimwords (LENGTH (ys:(N word)list) - 1) (:N)) * val (LAST ys)`) THEN
    SUBGOAL_THEN `(dimwords (LENGTH (ys:(N word)list) - 1) (:N)) * 1 <= (dimwords (LENGTH (ys:(N word)list) - 1) (:N)) * val (LAST (ys:(N word)list))` MP_TAC THENL
     [REWRITE_TAC[LE_MULT_LCANCEL] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `1 * (mw2n (BUTLAST (ys:(N word)list)) + (dimwords (LENGTH (ys:(N word)list) - 1) (:N)) * val (LAST ys)) <=
                  val (d:N word) * (mw2n (BUTLAST ys) + (dimwords (LENGTH (ys:(N word)list) - 1) (:N)) * val (LAST ys))` MP_TAC THENL
     [REWRITE_TAC[LE_MULT_RCANCEL] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `val (d:N word) * mw2n (ys:(N word)list) < dimwords (LENGTH ys) (:N)`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `dimwords (LENGTH (ys:(N word)list)) (:N) = dimword(:N) * (dimwords (LENGTH (ys:(N word)list) - 1) (:N))`
    SUBST1_TAC THENL
     [REWRITE_TAC[GSYM(CONJUNCT2 dimwords_thm)] THEN
      AP_THM_TAC THEN AP_TERM_TAC THEN
      UNDISCH_TAC `~(ys:(N word)list = [])` THEN
      REWRITE_TAC[GSYM LENGTH_EQ_NIL] THEN ARITH_TAC; ALL_TAC] THEN
    SUBST1_TAC(ASSUME `mw2n (ys:(N word)list) = mw2n (BUTLAST ys) + (dimwords (LENGTH (ys:(N word)list) - 1) (:N)) * val (LAST ys)`) THEN
    SUBGOAL_THEN `val (d:N word) * mw2n (BUTLAST (ys:(N word)list)) < val d * (dimwords (LENGTH (ys:(N word)list) - 1) (:N))`
    MP_TAC THENL
     [REWRITE_TAC[LT_MULT_LCANCEL] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `(dimwords (LENGTH (ys:(N word)list) - 1) (:N)) * (val (d:N word) * (val (LAST (ys:(N word)list)) + 1)) <=
                  (dimwords (LENGTH (ys:(N word)list) - 1) (:N)) * dimword(:N)` MP_TAC THENL
     [REWRITE_TAC[LE_MULT_LCANCEL] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    ARITH_TAC; ALL_TAC] THEN
  UNDISCH_TAC `mw2n (ys:(N word)list) =
     mw2n (BUTLAST ys) + dimwords (LENGTH (ys:(N word)list) - 1) (:N) * val (LAST ys)` THEN
  DISCH_THEN(K ALL_TAC) THEN
  SUBGOAL_THEN `mw2n (BUTLAST (mw_mul_by_single (d:N word) ys)) =
                val d * mw2n (ys:(N word)list) /\
                LENGTH (BUTLAST (mw_mul_by_single d ys)) = LENGTH ys`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[LBIGAUX_LENGTH_BUTLAST; mw_mul_by_single_lemma; ADD_SUB] THEN
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `mw2n (mw_mul_by_single (d:N word) (ys:(N word)list))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC LBIGAUX_MW2N_BUTLAST THEN
      ASM_REWRITE_TAC[mw_mul_by_single_lemma; ADD_SUB];
      REWRITE_TAC[mw_mul_by_single_lemma]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `ns = BUTLAST (mw_mul_by_single (d:N word) (ys:(N word)list))` THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `~(ns:(N word)list = [])` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM LENGTH_EQ_NIL] THEN ASM_REWRITE_TAC[] THEN
    ASM_REWRITE_TAC[LENGTH_EQ_NIL]; ALL_TAC] THEN
  MP_TAC(ISPEC `ns:(N word)list` LBIGAUX_MW2N_FRONT_LAST) THEN
  ASM_REWRITE_TAC[VAL_WORD_0; MULT_CLAUSES; ADD_CLAUSES; LBIGAUX_LENGTH_BUTLAST] THEN
  MP_TAC(ISPEC `BUTLAST (ns:(N word)list)` mw2n_lt) THEN
  ASM_REWRITE_TAC[LBIGAUX_LENGTH_BUTLAST] THEN
  UNDISCH_TAC `dimwords (LENGTH (ys:(N word)list) - 1) (:N) <=
               val (d:N word) * mw2n (ys:(N word)list)` THEN
  ARITH_TAC);;

let LAST_FRONT_mw_mul_by_single_NOT_ZERO = prove
 (`!ys:(N word)list.
     mw_ok ys /\ ~(ys = []) /\ 2 < dimword(:N)
     ==> ~(LAST (BUTLAST (mw_mul_by_single (calc_d (LAST ys,word 1)) ys)) = word 0)`,
  SIMP_TAC[LBIGAUX_NORM_DIVISOR]);;

let LBIGAUX_DIMWORDS_ADD = prove
 (`!a b. dimwords (a + b) (:N) = dimwords a (:N) * dimwords b (:N)`,
  REWRITE_TAC[dimwords_def; RIGHT_ADD_DISTRIB; EXP_ADD]);;

let mw_div_thm = prove
 (`!xs ys md res (c:bool).
     mw_div xs ys = (res,md,c) /\ ~(mw2n ys = 0)
     ==> mw2n res = mw2n xs DIV mw2n ys /\ mw2n md = mw2n xs MOD mw2n ys /\ c /\
         LENGTH md = LENGTH (mw_fix ys:(N word)list)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mw_div_def; LET_DEF; LET_END_DEF] THEN
  ONCE_REWRITE_TAC[GSYM mw2n_mw_fix] THEN
  MP_TAC(ISPEC `xs:(N word)list` mw_ok_fix) THEN
  MP_TAC(ISPEC `ys:(N word)list` mw_ok_fix) THEN
  SPEC_TAC(`mw_fix (xs:(N word)list)`,`xs:(N word)list`) THEN
  SPEC_TAC(`mw_fix (ys:(N word)list)`,`ys:(N word)list`) THEN
  REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
  REWRITE_TAC[mw2n_mw_fix] THEN
  POP_ASSUM(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  COND_CASES_TAC THENL
   [REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN REPEAT VAR_EQ_TAC THEN
    MP_TAC(SPECL [`xs:(N word)list`; `ys:(N word)list`] LENGTH_LESS_IMP_mw2n_LESS) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    ASM_SIMP_TAC[mw2n_def; DIV_LT; MOD_LT; GSYM mw2n_APPEND_REPLICATE;
                 LENGTH_APPEND; LENGTH_REPLICATE] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  COND_CASES_TAC THENL
  [(UNDISCH_TAC `LENGTH (ys:(N word)list) = 1` THEN
  REWRITE_TAC[ARITH_RULE `1 = SUC 0`; LENGTH_EQ_CONS; LENGTH_EQ_NIL] THEN
  STRIP_TAC THEN REPEAT(FIRST_X_ASSUM SUBST_ALL_TAC) THEN REWRITE_TAC[HD] THEN
  REPEAT PAIRARG_TAC THEN REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN
  REPEAT VAR_EQ_TAC) THEN
   (MP_TAC(SPECL [`REVERSE xs:(N word)list`; `h:N word`; `qs:(N word)list`; `r:N word`;
                `c:bool`] mw_simple_div_thm) THEN
  ASM_REWRITE_TAC[REVERSE_REVERSE; WORD_ULT; VAL_WORD_0] THEN
  UNDISCH_TAC `~(mw2n [h:N word] = 0)` THEN
  REWRITE_TAC[mw2n_def; MULT_CLAUSES; ADD_CLAUSES; LENGTH] THEN
  SIMP_TAC[ARITH_RULE `~(n = 0) ==> 0 < n`]);
   (SUBGOAL_THEN `~(ys:(N word)list = [])` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `~(mw2n (ys:(N word)list) = 0)` THEN
    ASM_REWRITE_TAC[mw2n_def]; ALL_TAC] THEN
  SUBGOAL_THEN `2 <= LENGTH (ys:(N word)list)` ASSUME_TAC THENL
   [UNDISCH_TAC `~(ys:(N word)list = [])` THEN UNDISCH_TAC `~(LENGTH (ys:(N word)list) = 1)` THEN
    REWRITE_TAC[GSYM LENGTH_EQ_NIL] THEN ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPEC `ys:(N word)list` LBIGAUX_NORM_DIVISOR) THEN ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `d = calc_d (LAST (ys:(N word)list),word 1)` THEN STRIP_TAC THEN
  ABBREV_TAC `ysn = BUTLAST (mw_mul_by_single (d:N word) (ys:(N word)list))` THEN
  ABBREV_TAC `xsn = APPEND (mw_mul_by_single (d:N word) (xs:(N word)list)) [word 0]` THEN
  SUBGOAL_THEN `mw2n (xsn:(N word)list) = val (d:N word) * mw2n (xs:(N word)list) /\
                LENGTH xsn = LENGTH xs + 2 /\
                mw2n xsn < dimwords (LENGTH xs + 1) (:N)` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "xsn" THEN
    REWRITE_TAC[mw2n_APPEND; mw2n_def; VAL_WORD_0; LENGTH_APPEND; LENGTH;
                mw_mul_by_single_lemma] THEN
    REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES] THEN
    MP_TAC(ISPEC `mw_mul_by_single (d:N word) (xs:(N word)list)` mw2n_lt) THEN
    REWRITE_TAC[mw_mul_by_single_lemma] THEN ARITH_TAC; ALL_TAC]) THEN
   (ABBREV_TAC `xs1 = BUTLASTN (LENGTH (ys:(N word)list)) (xsn:(N word)list)` THEN
  ABBREV_TAC `xs2 = LASTN (LENGTH (ys:(N word)list)) (xsn:(N word)list)` THEN
  SUBGOAL_THEN `APPEND xs1 xs2 = xsn:(N word)list /\
                LENGTH (xs2:(N word)list) = LENGTH (ys:(N word)list) /\
                LENGTH (xs1:(N word)list) + LENGTH ys = LENGTH (xs:(N word)list) + 2`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `LENGTH (ys:(N word)list) <= LENGTH (xsn:(N word)list)` ASSUME_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    MAP_EVERY EXPAND_TAC ["xs1"; "xs2"] THEN
    ASM_SIMP_TAC[APPEND_BUTLASTN_LASTN; LENGTH_LASTN] THEN
    FIRST_ASSUM(MP_TAC o AP_TERM `LENGTH:(N word)list->num` o
      MATCH_MP APPEND_BUTLASTN_LASTN) THEN
    ASM_SIMP_TAC[LENGTH_APPEND; LENGTH_LASTN]; ALL_TAC] THEN
  SUBGOAL_THEN `mw2n (xs2:(N word)list) < mw2n (ysn:(N word)list)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC LTE_TRANS THEN
    EXISTS_TAC `dimwords (LENGTH (ys:(N word)list) - 1) (:N)` THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[GSYM NOT_LE] THEN DISCH_TAC THEN
    UNDISCH_TAC `mw2n (xsn:(N word)list) < dimwords (LENGTH (xs:(N word)list) + 1) (:N)` THEN
    SUBST1_TAC(SYM(ASSUME `APPEND xs1 xs2 = xsn:(N word)list`)) THEN
    REWRITE_TAC[mw2n_APPEND; NOT_LT] THEN
    SUBGOAL_THEN `dimwords (LENGTH (xs:(N word)list) + 1) (:N) =
                  dimwords (LENGTH (xs1:(N word)list)) (:N) *
                  dimwords (LENGTH (ys:(N word)list) - 1) (:N)` SUBST1_TAC THENL
     [REWRITE_TAC[GSYM LBIGAUX_DIMWORDS_ADD] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
      ASM_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC(ARITH_RULE `b <= c ==> b <= a + c`) THEN
    ASM_REWRITE_TAC[LE_MULT_LCANCEL]; ALL_TAC]) THEN
   (REPEAT PAIRARG_TAC THEN REWRITE_TAC[PAIR_EQ]) THEN
   (DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
  MP_TAC(SPECL [`xs1:(N word)list`; `xs2:(N word)list`; `ysn:(N word)list`;
                `qs:(N word)list`; `rs:(N word)list`] LBIGAUX_MW_DIV_AUX) THEN
  MP_TAC(SPECL [`xs1:(N word)list`; `xs2:(N word)list`; `ysn:(N word)list`;
                `qs:(N word)list`; `rs:(N word)list`] LENGTH_mw_div_aux) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`REVERSE rs:(N word)list`; `d:N word`; `rs':(N word)list`; `r:N word`;
                `c':bool`] mw_simple_div_thm) THEN
  ASM_REWRITE_TAC[WORD_ULT; VAL_WORD_0; REVERSE_REVERSE] THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP LENGTH_mw_simple_div) THEN
  ASM_REWRITE_TAC[LENGTH_REVERSE] THEN
  SUBGOAL_THEN `~(val (d:N word) = 0)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[DIV_MULT2; MOD_MULT2; DIV_MULT] THEN
  ASM_MESON_TAC[LENGTH_REVERSE])]);;

(* the integer floor division and modulus at the four sign combinations    *)
(* (HOL4: NEG_DIV and NEG_MOD)                                             *)

let LBIGAUX_NEG_DIV = prove
 (`!n m. ~(m = 0)
     ==> int_div (&n) (&m) = &(n DIV m) /\
         int_div (-- &n) (&m) = --(&(n DIV m + (if n MOD m = 0 then 0 else 1))) /\
         int_div (&n) (-- &m) = --(&(n DIV m + (if n MOD m = 0 then 0 else 1))) /\
         int_div (-- &n) (-- &m) = &(n DIV m)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `~(&m:int = &0)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[INT_OF_NUM_EQ]; ALL_TAC] THEN
  SUBGOAL_THEN `int_div (-- &n) (&m) = --(&(n DIV m + (if n MOD m = 0 then 0 else 1)))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC INT_DIV_UNIQUE THEN
    EXISTS_TAC `if n MOD m = 0 then &0 else &m - &(n MOD m):int` THEN
    REWRITE_TAC[INT_ARITH `~(&m:int < &0)`] THEN
    MP_TAC(SPECL [`n:num`; `m:num`] DIVISION) THEN ASM_REWRITE_TAC[] THEN
    ABBREV_TAC `q = n DIV m` THEN ABBREV_TAC `r = n MOD m` THEN
    DISCH_THEN(CONJUNCTS_THEN2 SUBST1_TAC MP_TAC) THEN
    REWRITE_TAC[GSYM INT_OF_NUM_LT; GSYM INT_OF_NUM_ADD; GSYM INT_OF_NUM_MUL] THEN
    COND_CASES_TAC THEN POP_ASSUM MP_TAC THEN
    REWRITE_TAC[GSYM INT_OF_NUM_EQ; GSYM INT_OF_NUM_ADD] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[INT_DIV_NEG; INT_NEG_NEG; INT_DIV]);;

let LBIGAUX_NEG_MOD = prove
 (`!n m. ~(m = 0)
     ==> integer_int_mod (&n) (&m) = &(n MOD m) /\
         integer_int_mod (-- &n) (&m) = &(if n MOD m = 0 then 0 else m - n MOD m) /\
         integer_int_mod (&n) (-- &m) = --(&(if n MOD m = 0 then 0 else m - n MOD m)) /\
         integer_int_mod (-- &n) (-- &m) = --(&(n MOD m))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  ASM_SIMP_TAC[integer_int_mod_DEF; LBIGAUX_NEG_DIV] THEN
  MP_TAC(SPECL [`n:num`; `m:num`] DIVISION) THEN ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `q = n DIV m` THEN ABBREV_TAC `r = n MOD m` THEN
  DISCH_THEN(CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC) THEN
  COND_CASES_TAC THEN
  ASM_SIMP_TAC[GSYM INT_OF_NUM_ADD; GSYM INT_OF_NUM_MUL; GSYM INT_OF_NUM_SUB;
               LT_IMP_LE] THEN
  POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN
  REWRITE_TAC[GSYM INT_OF_NUM_EQ; GSYM INT_OF_NUM_LT] THEN INT_ARITH_TAC);;

let LBIGAUX_MW_ADDV_N2MW = prove
 (`!n. mw_addv (n2mw n:(N word)list) [] T = n2mw (n + 1)`,
  GEN_TAC THEN
  SUBGOAL_THEN `mw_ok (mw_addv (n2mw n:(N word)list) [] T)` MP_TAC THENL
   [MATCH_MP_TAC mw_ok_addv THEN REWRITE_TAC[mw_ok_n2mw; mw_ok_CLAUSES]; ALL_TAC] THEN
  DISCH_THEN(SUBST1_TAC o MATCH_MP mw_ok_mw_mw2n) THEN AP_TERM_TAC THEN
  SIMP_TAC[mw_addv_thm; LENGTH; LE_0; mw2n_n2mw; mw2n_def; BITVAL_CLAUSES] THEN
  ARITH_TAC);;

let LBIGAUX_MW_SUBV_N2MW = prove
 (`!a b. ~(b = 0)
     ==> mw_subv (n2mw b:(N word)list) (n2mw (a MOD b)) = n2mw (b - a MOD b)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC IMP_EQ_n2mw_ALT THEN
  REWRITE_TAC[mw_ok_n2mw; mw2n_n2mw; mw_subv_def; mw_ok_fix] THEN
  REWRITE_TAC[GSYM mw_subv_def] THEN
  SUBGOAL_THEN `a MOD b < b` ASSUME_TAC THENL [ASM_REWRITE_TAC[MOD_LT_EQ]; ALL_TAC] THEN
  MP_TAC(SPECL [`n2mw b:(N word)list`; `n2mw (a MOD b):(N word)list`] mw_subv_thm) THEN
  REWRITE_TAC[mw2n_n2mw] THEN ANTS_TAC THENL
   [ASM_SIMP_TAC[LT_IMP_LE] THEN MATCH_MP_TAC LENGTH_n2mw_LESS_LENGTH_n2mw THEN
    ASM_SIMP_TAC[LT_IMP_LE];
    SIMP_TAC[]]);;

let LBIGAUX_DIVMOD_CASE_TAC =
  SUBGOAL_THEN `i:int = if i < &0 then -- &a else &a` SUBST1_TAC THENL
   [COND_CASES_TAC THEN UNDISCH_TAC `abs i = &a:int` THEN ASM_INT_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `j:int = if j < &0 then -- &b else &b` SUBST1_TAC THENL
   [COND_CASES_TAC THEN UNDISCH_TAC `abs j = &b:int` THEN ASM_INT_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[LBIGAUX_NEG_DIV; LBIGAUX_NEG_MOD] THEN
  REWRITE_TAC[INT_ABS_NEG; INT_ABS_NUM; NUM_OF_INT_OF_NUM; INT_NEG_LT0;
              INT_OF_NUM_LT; INT_ARITH `~(&n:int < &0)`; n2mw_NIL] THEN
  ASM_CASES_TAC `a MOD b = 0` THEN
  ASM_REWRITE_TAC[n2mw_NIL; ADD_CLAUSES; ADD_EQ_0; ARITH_EQ; SUB_EQ_0;
                  GSYM NOT_LT; COND_ID] THEN
  REWRITE_TAC[ARITH_RULE `0 < n <=> ~(n = 0)`] THEN
  TRY COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `a MOD b < b` THEN ARITH_TAC;;

let mwi_divmod_thm = prove
 (`!i j. ~(j = &0)
     ==> mwi_divmod (i2mw i) (i2mw j:bool#(N word)list) =
         (T, i2mw (int_div i j), i2mw (integer_int_mod i j))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o BINOP_CONV) [i2mw_def] THEN
  REWRITE_TAC[mwi_divmod_def] THEN
  ABBREV_TAC `a = num_of_int (abs i)` THEN ABBREV_TAC `b = num_of_int (abs j)` THEN
  SUBGOAL_THEN `~(b = 0)` ASSUME_TAC THENL
   [EXPAND_TAC "b" THEN ASM_REWRITE_TAC[LBIGAUX_NUM_ABS_EQ_0]; ALL_TAC] THEN
  PAIRARG_TAC THEN PAIRARG_TAC THEN
  MP_TAC(SPECL [`n2mw a:(N word)list`; `n2mw b:(N word)list`; `md:(N word)list`;
                `res:(N word)list`; `c:bool`] mw_div_thm) THEN
  ASM_REWRITE_TAC[mw2n_n2mw] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[n2mw_mw2n; LET_DEF; LET_END_DEF] THEN
  REWRITE_TAC[LBIGAUX_MW_ADDV_N2MW; n2mw_NIL] THEN ASM_SIMP_TAC[LBIGAUX_MW_SUBV_N2MW] THEN
  REWRITE_TAC[i2mw_def; PAIR_EQ] THEN
  SUBGOAL_THEN `abs i = &a:int /\ abs j = &b:int` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["a";"b"] THEN REWRITE_TAC[LBIGAUX_NUM_ABS]; ALL_TAC] THEN
  SUBGOAL_THEN `a MOD b < b` ASSUME_TAC THENL [ASM_REWRITE_TAC[MOD_LT_EQ]; ALL_TAC] THEN
  ASM_CASES_TAC `i:int < &0` THEN ASM_CASES_TAC `j:int < &0` THEN ASM_REWRITE_TAC[] THEN
  LBIGAUX_DIVMOD_CASE_TAC);;

let mwi_op_thm = prove
 (`!op i j.
     (op = multiword_Div \/ op = multiword_Mod ==> ~(j = &0))
     ==> mwi_op op (i2mw i) (i2mw j):bool#(N word)list =
         i2mw (multiword_int_op op i j)`,
  MATCH_MP_TAC mw_op_INDUCT THEN
  REWRITE_TAC[mwi_op_def; int_op_def; distinctness "mw_op";
              mwi_add_thm; mwi_sub_thm; mwi_mul_thm] THEN
  SIMP_TAC[mwi_div_def; mwi_mod_def; mwi_divmod_thm] THEN
  REWRITE_TAC[mwi_lt_def; mwi_eq_def; mwi_compare_thm] THEN
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THENL
   [ASM_CASES_TAC `i:int = j` THEN
    ASM_REWRITE_TAC[option_DISTINCT; option_INJ; INT_LT_REFL];
    ASM_CASES_TAC `i:int = j` THEN ASM_REWRITE_TAC[option_DISTINCT];
    REWRITE_TAC[i2mw_def; INT_LT_REFL; INT_ABS_NUM; NUM_OF_INT_OF_NUM; n2mw_0]]);;

(* ------------------------------------------------------------------------- *)
(* extra                                                                     *)
(* ------------------------------------------------------------------------- *)

let LENGTH_mw_add = prove
 (`!xs1 (ys:(N word)list) c qs1 c1.
     mw_add xs1 ys c = (qs1,c1) ==> LENGTH xs1 = LENGTH qs1`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[mw_add_def; PAIR_EQ] THEN REPEAT GEN_TAC THENL
   [STRIP_TAC THEN REPEAT VAR_EQ_TAC THEN REWRITE_TAC[LENGTH];
    PAIRARG_TAC THEN PAIRARG_TAC THEN REWRITE_TAC[PAIR_EQ] THEN
    DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
    REWRITE_TAC[LENGTH; SUC_INJ] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_MESON_TAC[]]);;

let LENGTH_mw_fix_IMP = prove
 (`!(xs:(N word)list) (ys:(N word)list).
     LENGTH xs = LENGTH ys ==> LENGTH (mw_fix xs) <= LENGTH ys`,
  MESON_TAC[LENGTH_mw_fix]);;

let LENGTH_mw_subv = prove
 (`!ys xs:(N word)list. LENGTH xs <= LENGTH ys ==> LENGTH (mw_subv ys xs) <= LENGTH ys`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mw_subv_def] THEN
  MATCH_MP_TAC LENGTH_mw_fix_IMP THEN REWRITE_TAC[LBIGAUX_LENGTH_MW_SUB]);;

let mw_add_F = prove
 (`!xs2:(N word)list. mw_add xs2 (MAP (\x. word 0) xs2) F = (xs2,F)`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[mw_add_def; MAP; HD; TL] THEN
  SUBGOAL_THEN `single_add (h:N word) (word 0) F = (h,F)` SUBST1_TAC THENL
   [REWRITE_TAC[single_add_def; multiword_b2w_def; BITVAL_CLAUSES; VAL_WORD_0;
                ADD_CLAUSES; WORD_ADD_0; PAIR_EQ; NOT_LE; w2n_lt];
    CAKE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[]]);;

let mw_addv_EQ_mw_add = prove
 (CASE_TERM
  `!xs1 xs2 (ys:(N word)list) c1.
     LENGTH ys = LENGTH xs1
     ==> mw_addv (APPEND xs1 xs2) ys c1 =
         match mw_add xs1 ys c1 with (zs1,c2) ->
         match mw_add xs2 (MAP (\x. word 0) xs2) c2 with (zs2,c3) ->
           APPEND (APPEND zs1 zs2) (if c3 then [word 1] else [])`,
  LIST_INDUCT_TAC THENL
   [REWRITE_TAC[APPEND; LENGTH; LENGTH_EQ_NIL] THEN REPEAT GEN_TAC THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[mw_add_def] THEN CAKE_REWRITE_TAC[] THEN
    SPEC_TAC(`c1:bool`,`c1:bool`) THEN SPEC_TAC(`xs2:(N word)list`,`xs2:(N word)list`) THEN
    LIST_INDUCT_TAC THENL
     [REWRITE_TAC[mw_addv_def; MAP; mw_add_def; APPEND] THEN CAKE_REWRITE_TAC[] THEN
      REWRITE_TAC[APPEND];
      GEN_TAC THEN REWRITE_TAC[mw_addv_def; MAP; mw_add_def; HD; TL; NOT_CONS_NIL] THEN
      CAKE_REWRITE_TAC[] THEN PAIRARG_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `c1':bool`) THEN
      PAIRARG_TAC THEN REWRITE_TAC[APPEND] THEN DISCH_THEN SUBST1_TAC THEN
      REWRITE_TAC[APPEND]];
    X_GEN_TAC `xs2:(N word)list` THEN X_GEN_TAC `ys:(N word)list` THEN
    CASES_ON `ys:(N word)list` THEN
    REWRITE_TAC[LENGTH; ARITH_RULE `~(0 = SUC n) /\ (SUC m = SUC n <=> m = n)`] THEN
    REPEAT STRIP_TAC THEN
    REWRITE_TAC[APPEND; mw_addv_def; mw_add_def; HD; TL; NOT_CONS_NIL] THEN
    CAKE_REWRITE_TAC[] THEN PAIRARG_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`xs2:(N word)list`; `a1:(N word)list`; `c1':bool`]) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    PAIRARG_TAC THEN PAIRARG_TAC THEN REWRITE_TAC[APPEND]]);;

let LBIGAUX_SINGLE_ADD_0_F = prove
 (`!h:N word. single_add h (word 0) F = (h,F)`,
  REWRITE_TAC[single_add_def; multiword_b2w_def; BITVAL_CLAUSES; VAL_WORD_0;
              ADD_CLAUSES; WORD_ADD_0; PAIR_EQ; NOT_LE; w2n_lt]);;

let LBIGAUX_MW_ADDV_NIL_F = prove
 (`!xs:(N word)list. mw_addv xs [] F = xs`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[mw_addv_def] THEN
  CAKE_REWRITE_TAC[LBIGAUX_SINGLE_ADD_0_F] THEN ASM_REWRITE_TAC[]);;

let LBIGAUX_MW_ADDV_CONS_NIL_T = prove
 (`!(x:N word) xs.
     mw_addv (CONS x xs) [] T =
     if x = word_not (word 0) then CONS (word 0) (mw_addv xs [] T)
     else CONS (word_add x (word 1)) xs`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mw_addv_def] THEN CAKE_REWRITE_TAC[] THEN
  REWRITE_TAC[single_add_def; multiword_b2w_def; BITVAL_CLAUSES; VAL_WORD_0;
              ADD_CLAUSES; WORD_ADD_0] THEN
  CAKE_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(dimword(:N) <= val (x:N word) + 1) <=> x = word_not (word 0)`
  SUBST1_TAC THENL
   [REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_NOT; VAL_WORD_0; GSYM dimword_def] THEN
    MP_TAC(ISPEC `x:N word` w2n_lt) THEN ARITH_TAC; ALL_TAC] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[LBIGAUX_MW_ADDV_NIL_F; CONS_11] THEN
  CONV_TAC WORD_RULE);;

let mw_addv_NIL = prove
 (`mw_addv [] [] T = [word 1:N word] /\
   (!xs:(N word)list. mw_addv xs [] F = xs) /\
   (!(x:N word) xs.
      mw_addv (CONS x xs) [] T =
      if x = word_not (word 0) then CONS (word 0) (mw_addv xs [] T)
      else CONS (word_add x (word 1)) xs)`,
  REWRITE_TAC[mw_addv_def; LBIGAUX_MW_ADDV_NIL_F; LBIGAUX_MW_ADDV_CONS_NIL_T]);;

let LBIGAUX_LENGTH_MW_ADDV = prove
 (`!xs (ys:(N word)list) c. LENGTH (mw_addv xs ys c) <= LENGTH xs + 1`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[mw_addv_def] THENL
   [REPEAT GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[LENGTH] THEN ARITH_TAC;
    REPEAT GEN_TAC THEN REPEAT PAIRARG_TAC THEN REWRITE_TAC[LENGTH] THEN
    ASM_REWRITE_TAC[LE_SUC; ARITH_RULE `SUC n + 1 = SUC (n + 1)`]]);;

let LENGTH_mw_addv = prove
 (`!xs ys:(N word)list.
     LENGTH ys <= LENGTH xs ==> LENGTH (mw_addv xs ys F) <= LENGTH xs + LENGTH ys`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `ys:(N word)list = []` THEN
  ASM_REWRITE_TAC[LBIGAUX_MW_ADDV_NIL_F; LENGTH; ADD_CLAUSES; LE_REFL] THEN
  DISCH_TAC THEN TRANS_TAC LE_TRANS `LENGTH (xs:(N word)list) + 1` THEN
  REWRITE_TAC[LBIGAUX_LENGTH_MW_ADDV; LE_ADD_LCANCEL] THEN
  UNDISCH_TAC `~(ys:(N word)list = [])` THEN REWRITE_TAC[GSYM LENGTH_EQ_NIL] THEN
  ARITH_TAC);;

let LENGTH_mw_mul = prove
 (`!xs ys zs:(N word)list.
     LENGTH zs = LENGTH ys ==> LENGTH (mw_mul xs ys zs) = LENGTH xs + LENGTH ys`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[mw_mul_def; LENGTH; ADD_CLAUSES; LET_DEF;
    LET_END_DEF] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[LENGTH; SUC_INJ] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  SUBGOAL_THEN `~(mw_mul_pass (h:N word) ys zs (word 0) = [])` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM LENGTH_EQ_NIL; LENGTH_mw_mul_pass] THEN ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[LENGTH_TL; LENGTH_mw_mul_pass] THEN ARITH_TAC);;

let mw_sub_APPEND = prove
 (CASE_TERM
  `!xs1 xs2 (ys:(N word)list) c.
     LENGTH xs1 = LENGTH ys
     ==> mw_sub (APPEND xs1 xs2) ys c =
         match mw_sub xs1 ys c with (ts1,c) ->
         match mw_sub xs2 [] c with (ts2,c) -> (APPEND ts1 ts2,c)`,
  LIST_INDUCT_TAC THEN X_GEN_TAC `xs2:(N word)list` THEN X_GEN_TAC `ys:(N word)list` THEN
  CASES_ON `ys:(N word)list` THEN
  REWRITE_TAC[LENGTH; ARITH_RULE `~(SUC n = 0) /\ ~(0 = SUC n) /\
                                  (SUC m = SUC n <=> m = n)`] THEN
  REWRITE_TAC[APPEND; mw_sub_def] THENL
   [GEN_TAC THEN CAKE_REWRITE_TAC[] THEN PAIRARG_TAC THEN REWRITE_TAC[APPEND];
    REPEAT STRIP_TAC THEN PAIRARG_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`xs2:(N word)list`; `a1:(N word)list`; `c1:bool`]) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    MP_TAC(ISPEC `mw_sub (t:(N word)list) a1 c1` PAIR_SURJECTIVE) THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`p:(N word)list`; `pc:bool`] THEN
    DISCH_THEN SUBST1_TAC THEN CAKE_REWRITE_TAC[] THEN
    MP_TAC(ISPEC `mw_sub (xs2:(N word)list) [] pc` PAIR_SURJECTIVE) THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`q:(N word)list`; `qc:bool`] THEN
    DISCH_THEN SUBST1_TAC THEN CAKE_REWRITE_TAC[] THEN REWRITE_TAC[APPEND]]);;

let k2mw_LENGTH_0 = prove
 (`!ys:B list. k2mw (LENGTH ys) 0 = MAP (combin_K (word 0)) ys:(N word)list`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[LENGTH; k2mw_def; MAP; DIV_0; K_THM]);;

let mw_mul_by_single2_def = cake_def
  `(mw_mul_by_single2 (x1:N word) (x2:N word) [] k1 k2 = [k2]) /\
   (mw_mul_by_single2 x1 x2 (CONS y ys) k1 k2 =
      match single_mul_add x1 y k1 (word 0) with (y1,k1) ->
      match single_mul_add x2 y1 k2 (word 0) with (y2,k2) ->
        CONS y2 (mw_mul_by_single2 x1 x2 ys k1 k2))`;;

let LBIGAUX_MW_MUL_BY_SINGLE2 = prove
 (`!ys (x1:N word) x2 k1 k2.
     mw_mul_by_single2 x1 x2 ys k1 k2 =
     mw_mul_pass x2 (BUTLAST (mw_mul_pass x1 ys (k2mw (LENGTH ys) 0) k1))
                 (k2mw (LENGTH ys) 0) k2`,
  LIST_INDUCT_TAC THEN
  REWRITE_TAC[mw_mul_by_single2_def; mw_mul_pass_def; LENGTH; k2mw_def; BUTLAST;
              DIV_0] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[HD; TL] THEN PAIRARG_TAC THEN
  SUBGOAL_THEN `~(mw_mul_pass (x1:N word) t (k2mw (LENGTH (t:(N word)list)) 0) k1' = [])`
    (fun th -> REWRITE_TAC[BUTLAST; th]) THENL
   [REWRITE_TAC[GSYM LENGTH_EQ_NIL; LENGTH_mw_mul_pass] THEN ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[mw_mul_pass_def; HD; TL] THEN PAIRARG_TAC THEN ASM_REWRITE_TAC[]);;

let mw_mul_by_single2_thm = prove
 (`!ys (x1:N word) x2.
     mw_mul_by_single2 x1 x2 ys (word 0) (word 0) =
     mw_mul_by_single x2 (BUTLAST (mw_mul_by_single x1 ys))`,
  REWRITE_TAC[LBIGAUX_MW_MUL_BY_SINGLE2; mw_mul_by_single_def] THEN
  REWRITE_TAC[LBIGAUX_LENGTH_BUTLAST; LENGTH_mw_mul_pass; ADD_SUB]);;
(* calc only top three results of mw_mul_pass *)

let mw_mul_pass_top_def = cake_def
  `(mw_mul_pass_top (x:N word) [] (k,k1,k2) = (k,k1,k2)) /\
   (mw_mul_pass_top x (CONS y ys) (k,k1,k2) =
      match single_mul_add x y k (word 0) with (y1,k) ->
        mw_mul_pass_top x ys (k,y1,k1))`;;

let LBIGAUX_LAST_CONS2 = prove
 (`!(a:A) b t. LAST (CONS a (CONS b t)) = LAST (CONS b t) /\
               BUTLAST (CONS a (CONS b t)) = CONS a (BUTLAST (CONS b t))`,
  REWRITE_TAC[LAST; BUTLAST; NOT_CONS_NIL]);;

let LBIGAUX_MW_MUL_PASS_TOP = prove
 (`!ys (x:N word) k1 k2 k3.
     mw_mul_pass_top x ys (k1,k2,k3) =
     (LAST (APPEND [k3;k2] (mw_mul_pass x ys (MAP (combin_K (word 0)) ys) k1)),
      LAST (BUTLAST (APPEND [k3;k2] (mw_mul_pass x ys (MAP (combin_K (word 0)) ys) k1))),
      LAST (BUTLAST (BUTLAST
        (APPEND [k3;k2] (mw_mul_pass x ys (MAP (combin_K (word 0)) ys) k1)))))`,
  LIST_INDUCT_TAC THENL
   [REWRITE_TAC[mw_mul_pass_top_def; mw_mul_pass_def; MAP; APPEND] THEN
    REWRITE_TAC[LAST; BUTLAST; NOT_CONS_NIL];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[mw_mul_pass_top_def; mw_mul_pass_def; MAP; HD; TL;
    K_THM] THEN
  PAIRARG_TAC THEN ASM_REWRITE_TAC[APPEND] THEN
  ABBREV_TAC `m = mw_mul_pass (x:N word) t (MAP (combin_K (word 0)) t) k'` THEN
  SUBGOAL_THEN `~(m:(N word)list = [])` ASSUME_TAC THENL
   [EXPAND_TAC "m" THEN REWRITE_TAC[GSYM LENGTH_EQ_NIL; LENGTH_mw_mul_pass] THEN
    ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[LBIGAUX_LAST_CONS2; BUTLAST] THEN
  ASM_CASES_TAC `BUTLAST (m:(N word)list) = []` THEN
  ASM_REWRITE_TAC[LBIGAUX_LAST_CONS2; LAST; BUTLAST; NOT_CONS_NIL]);;

let mw_mul_pass_top_thm = prove
 (`!(x:N word) ys.
     1 < LENGTH ys
     ==> mw_mul_pass_top x ys (word 0,word 0,word 0) =
         (LAST (mw_mul_by_single x ys),
          LAST (BUTLAST (mw_mul_by_single x ys)),
          LAST (BUTLAST (BUTLAST (mw_mul_by_single x ys))))`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[LBIGAUX_MW_MUL_PASS_TOP; mw_mul_by_single_def; k2mw_LENGTH_0] THEN
  ABBREV_TAC `m = mw_mul_pass (x:N word) ys (MAP (combin_K (word 0)) ys) (word 0)` THEN
  SUBGOAL_THEN `2 < LENGTH (m:(N word)list)` MP_TAC THENL
   [EXPAND_TAC "m" THEN REWRITE_TAC[LENGTH_mw_mul_pass] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `~(m:(N word)list = []) /\ ~(BUTLAST m = []) /\
                ~(BUTLAST (BUTLAST m) = [])` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM LENGTH_EQ_NIL; LBIGAUX_LENGTH_BUTLAST] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[LAST_APPEND; BUTLAST_APPEND]);;

(* extra lemmas about single_div by repeated subtraction (to be used on    *)
(* architectures without division)                                         *)

let num_div_loop_def = cake_def_wf `MEASURE (FST:num#num#num#num->num)`
  (REWRITE_TAC WF_REL_THMS THEN REWRITE_TAC[FST] THEN ARITH_TAC)
  `num_div_loop (k:num,n:num,m:num,i:num) =
     if k = 0 then (m,i) else
       let n = n DIV 2 in
       let m = m * 2 in
         if i < n then num_div_loop (k - 1,n,m,i)
         else num_div_loop (k - 1,n,m + 1,i - n)`;;
let num_div_loop_lemma = prove
 (`!k i n m. i < n * 2 EXP k /\ 0 < n
             ==> num_div_loop (k,n * 2 EXP k,m,i) = (m * 2 EXP k + i DIV n,i MOD n)`,
  INDUCT_TAC THEN REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[num_div_loop_def] THENL
   [UNDISCH_TAC `i < n * 2 EXP 0` THEN
    ASM_SIMP_TAC[EXP; MULT_CLAUSES; DIV_LT; MOD_LT; ADD_CLAUSES];
    ALL_TAC] THEN
  REWRITE_TAC[NOT_SUC; SUC_SUB1; LET_DEF; LET_END_DEF] THEN
  SUBGOAL_THEN `(n * 2 EXP SUC k) DIV 2 = n * 2 EXP k` SUBST1_TAC THENL
   [REWRITE_TAC[EXP; ARITH_RULE `n * 2 * x = 2 * (n * x)`] THEN
    SIMP_TAC[DIV_MULT; ARITH_RULE `~(2 = 0)`]; ALL_TAC] THEN
  COND_CASES_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPECL [`i:num`; `n:num`; `m * 2`]) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[EXP; PAIR_EQ] THEN ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`i - n * 2 EXP k`; `n:num`; `m * 2 + 1`]) THEN
  ANTS_TAC THENL
   [UNDISCH_TAC `i < n * 2 EXP SUC k` THEN REWRITE_TAC[EXP] THEN ASM_ARITH_TAC;
    DISCH_THEN SUBST1_TAC] THEN
  SUBGOAL_THEN `i = (2 EXP k) * n + (i - n * 2 EXP k)` (fun th ->
    GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [th]) THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[DIV_MULT_ADD; MOD_MULT_ADD; ARITH_RULE `0 < n ==> ~(n = 0)`] THEN
  REWRITE_TAC[EXP; PAIR_EQ] THEN ARITH_TAC);;

let num_div_loop_thm = prove
 (`!k i n. i < n * 2 EXP k /\ 0 < n
           ==> num_div_loop (k,n * 2 EXP k,0,i) = (i DIV n,i MOD n)`,
  SIMP_TAC[num_div_loop_lemma; MULT_CLAUSES; ADD_CLAUSES]);;
let single_div_loop_def = cake_def_wf
  `MEASURE (\p:N word#(N word)list#N word#(N word)list. val (FST p))`
  (REWRITE_TAC WF_REL_THMS THEN BETA_TAC THEN REWRITE_TAC[FST] THEN
   REPEAT STRIP_TAC THEN
   SUBGOAL_THEN `val (word_sub (k:N word) (word 1)) < val k` ASSUME_TAC THENL
    [UNDISCH_TAC `~(k:N word = word 0)` THEN REWRITE_TAC[GSYM VAL_EQ_0] THEN
     DISCH_TAC THEN
     ASM_SIMP_TAC[VAL_WORD_SUB_CASES; VAL_WORD_1; ARITH_RULE `~(n = 0) ==> 1 <= n`] THEN
     ASM_ARITH_TAC; ALL_TAC] THEN
   ASM_ARITH_TAC)
  `single_div_loop (k:N word,ns:(N word)list,m:N word,is:(N word)list) =
     if k = word 0 then (m,is) else
       let ns = mw_shift ns in
       let m = word_shl m 1 in
         if mw_cmp is ns = SOME T then single_div_loop (word_sub k (word 1),ns,m,is)
         else
           let m = word_add m (word 1) in
           match mw_sub is ns T with (is,_) ->
             single_div_loop (word_sub k (word 1),ns,m,is)`;;
let single_div_full_def = cake_def
  `single_div_full m2 (m1:N word) n =
     match single_div_loop (word (dimindex(:N)),[word 0;n],word 0,[m1;m2]) with
       (m,is) -> (m, HD is)`;;

let LBIGAUX_WORD_SUC_SUB1 = prove
 (`!k. word_sub (word (SUC k)) (word 1):N word = word k`,
  GEN_TAC THEN MP_TAC(SPECL [`SUC k`; `1`] WORD_SUB) THEN
  REWRITE_TAC[ARITH_RULE `1 <= SUC k /\ SUC k - 1 = k`] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN REFL_TAC);;

let LBIGAUX_SDL_ARITH_TAC =
  MAP_EVERY UNDISCH_TAC [`SUC k < dimword(:N)`; `SUC k <= dimindex(:N)`;
    `val (m:N word) < 2 EXP (dimindex(:N) - SUC k)`;
    `2 EXP (dimindex(:N) - k) = 2 * 2 EXP (dimindex(:N) - SUC k)`] THEN
  ARITH_TAC;;

let LBIGAUX_SINGLE_DIV_LOOP = prove
 (`!k (ns:(N word)list) m is t qs.
     single_div_loop (word k,ns,m,is) = (t,qs) /\ k < dimword(:N) /\
     k <= dimindex(:N) /\ val m < 2 EXP (dimindex(:N) - k) /\
     LENGTH ns = 2 /\ LENGTH is = 2
     ==> num_div_loop (k,mw2n ns,val m,mw2n is) = (val t,mw2n qs) /\ LENGTH qs = 2`,
  INDUCT_TAC THEN REPEAT GEN_TAC THENL
   [ONCE_REWRITE_TAC[single_div_loop_def; num_div_loop_def] THEN
    REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN REPEAT VAR_EQ_TAC THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `2 EXP (dimindex(:N) - k) = 2 * 2 EXP (dimindex(:N) - SUC k) /\
                2 EXP (dimindex(:N) - k) <= dimword(:N)` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM(CONJUNCT2 EXP); dimword_def; LE_EXP] THEN
    CONJ_TAC THENL [AP_TERM_TAC THEN ASM_ARITH_TAC; ARITH_TAC]; ALL_TAC] THEN
  SUBGOAL_THEN `val (word_shl (m:N word) 1) = val m * 2 /\
                val (word_add (word_shl (m:N word) 1) (word 1)) = val m * 2 + 1`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[VAL_WORD_ADD; VAL_WORD_SHL; VAL_WORD_1; EXP_1; GSYM dimword_def] THEN
    SUBGOAL_THEN `2 * val (m:N word) < dimword(:N)` ASSUME_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[MOD_LT] THEN CONJ_TAC THENL [ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `2 * val (m:N word) + 1 < dimword(:N)`
      (fun th -> REWRITE_TAC[MATCH_MP MOD_LT th]) THEN
    ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `~(word (SUC k):N word = word 0)` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM VAL_EQ; w2n_n2w; VAL_WORD_0] THEN ASM_SIMP_TAC[MOD_LT] THEN
    ARITH_TAC; ALL_TAC] THEN
  UNDISCH_TAC `single_div_loop (word (SUC k),ns,m,is) = (t:N word,qs:(N word)list)` THEN
  ONCE_REWRITE_TAC[single_div_loop_def; num_div_loop_def] THEN
  ASM_REWRITE_TAC[NOT_SUC; SUC_SUB1; LBIGAUX_WORD_SUC_SUB1; LET_DEF; LET_END_DEF] THEN
  SUBGOAL_THEN `LENGTH (is:(N word)list) = LENGTH (mw_shift (ns:(N word)list))`
    (fun th -> REWRITE_TAC[MATCH_MP LBIGAUX_MW_CMP_SOME_T th]) THENL
   [ASM_REWRITE_TAC[LENGTH_mw_shift]; ALL_TAC] THEN
  REWRITE_TAC[mw_shift_thm] THEN COND_CASES_TAC THENL
  [(REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`mw_shift ns:(N word)list`; `word_shl (m:N word) 1`;
    `is:(N word)list`; `t:N word`; `qs:(N word)list`]) THEN
  ASM_REWRITE_TAC[LENGTH_mw_shift; mw_shift_thm] THEN
  ANTS_TAC THENL [LBIGAUX_SDL_ARITH_TAC; SIMP_TAC[]]);
   (REWRITE_TAC[] THEN PAIRARG_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `mw2n (is':(N word)list) = mw2n (is:(N word)list) - mw2n (ns:(N word)list) DIV 2 /\
                LENGTH is' = 2` STRIP_ASSUME_TAC THENL
   [MP_TAC(SPECL [`is:(N word)list`; `mw_shift ns:(N word)list`] mw_sub_thm) THEN
    ASM_REWRITE_TAC[LENGTH_mw_shift; mw_shift_thm; GSYM NOT_LT] THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP LENGTH_mw_sub) THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`mw_shift ns:(N word)list`;
    `word_add (word_shl (m:N word) 1) (word 1)`;
    `is':(N word)list`; `t:N word`; `qs:(N word)list`]) THEN
  ASM_REWRITE_TAC[LENGTH_mw_shift; mw_shift_thm] THEN
  ANTS_TAC THENL [LBIGAUX_SDL_ARITH_TAC; SIMP_TAC[]])]);;
let mw2n_0 = prove
 (`mw2n ([]:(N word)list) = 0 /\
   (!xs:(N word)list. mw2n (CONS (word 0) xs) = dimword(:N) * mw2n xs)`,
  REWRITE_TAC[mw2n_def; VAL_WORD_0; ADD_CLAUSES]);;

let HD_eq_n2w_mw2n = prove
 (`!xs:(N word)list.
     ~(LENGTH xs = 0) /\ mw2n xs < dimword(:N) ==> HD xs = word (mw2n xs)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[LENGTH; NOT_SUC; HD; mw2n_def] THEN
  ASM_CASES_TAC `mw2n (t:(N word)list) = 0` THEN
  ASM_REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; WORD_VAL] THEN
  MATCH_MP_TAC(TAUT `~p ==> p ==> q`) THEN
  MATCH_MP_TAC(ARITH_RULE `d * 1 <= d * m ==> ~(v + d * m < d)`) THEN
  REWRITE_TAC[LE_MULT_LCANCEL] THEN ASM_ARITH_TAC);;

let LESS_2_EXP = prove
 (`!n. n < 2 EXP n`,
  REWRITE_TAC[LT_POW2_REFL]);;

let single_div_full_thm = prove
 (`!x1 x2 y:N word.
     mw2n [x2;x1] < mw2n [word 0;y] ==> single_div_full x1 x2 y = single_div x1 x2 y`,
    REPEAT GEN_TAC THEN REWRITE_TAC[single_div_full_def] THEN PAIRARG_TAC THEN
  DISCH_TAC THEN
  MP_TAC(SPECL [`dimindex(:N)`; `[word 0;y]:(N word)list`; `word 0:N word`;
                `[x2;x1]:(N word)list`; `m:N word`; `is:(N word)list`]
    LBIGAUX_SINGLE_DIV_LOOP) THEN
  ASM_REWRITE_TAC[LENGTH; VAL_WORD_0; SUB_REFL; EXP; ARITH_RULE `0 < 1`; LE_REFL] THEN
  SUBGOAL_THEN `dimindex(:N) < dimword(:N)` (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[dimword_def; LESS_2_EXP]; ALL_TAC] THEN
  CONV_TAC NUM_REDUCE_CONV THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(val (y:N word) = 0)` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `mw2n [x2;x1:N word] < mw2n [word 0;y:N word]` THEN
    ASM_REWRITE_TAC[mw2n_def; VAL_WORD_0] THEN ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`dimindex(:N)`; `mw2n [x2;x1:N word]`; `val (y:N word)`]
    num_div_loop_thm) THEN
  ANTS_TAC THENL
   [UNDISCH_TAC `mw2n [x2;x1:N word] < mw2n [word 0;y:N word]` THEN
    REWRITE_TAC[mw2n_def; VAL_WORD_0; dimword_def] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `mw2n [word 0;y:N word] = val y * 2 EXP dimindex(:N)` SUBST1_TAC THENL
   [REWRITE_TAC[mw2n_def; VAL_WORD_0; dimword_def] THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `mw2n [word 0;y:N word] = val y * 2 EXP dimindex(:N)` ASSUME_TAC THENL
   [REWRITE_TAC[mw2n_def; VAL_WORD_0; dimword_def] THEN ARITH_TAC; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `mw2n [word 0;y:N word] = val y * 2 EXP dimindex(:N)`]) THEN
  ASM_REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN
  REWRITE_TAC[single_div_def; PAIR_EQ] THEN
  SUBGOAL_THEN `mw2n [x2;x1:N word] = val x1 * dimword(:N) + val x2` ASSUME_TAC THENL
   [REWRITE_TAC[mw2n_def] THEN ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL
   [ASM_MESON_TAC[WORD_VAL];
    SUBGOAL_THEN `HD is = word (mw2n (is:(N word)list))` SUBST1_TAC THENL
     [MATCH_MP_TAC HD_eq_n2w_mw2n THEN ASM_REWRITE_TAC[ARITH_RULE `~(2 = 0)`] THEN
      TRANS_TAC LT_TRANS `val (y:N word)` THEN REWRITE_TAC[w2n_lt] THEN
      ASM_REWRITE_TAC[MOD_LT_EQ];
      ASM_MESON_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* HOL4 [simp] theorems                                                      *)
(* ------------------------------------------------------------------------- *)

let _ = cake_add_simps [LESS_2_EXP];;

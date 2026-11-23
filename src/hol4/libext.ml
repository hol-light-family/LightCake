(* ========================================================================= *)
(* libext: the HOL4 library items that the Pancake and Candle theories use   *)
(* and the port did not have otherwise, with their HOL4 names, by HOL4       *)
(* theory: list, rich_list, arithmetic, pred_set, relation, option, pair,    *)
(* quantHeuristics, finite_map, words, logroot, numeral_bit, alignment,      *)
(* byte, llist.  The balanced_map items are in hol4/balanced_map_part2.ml.   *)
(*                                                                           *)
(* Items the port or HOL Light already has under another name (use those): *)
(*   list isPREFIX_REFL = IS_PREFIX_REFL (hol4/rich_list.ml)                 *)
(*   list LIST_REL_MAP = EVERY2_MAP, LIST_REL_THM = EVERY2_THM (hol4/list.ml; *)
(*     HOL4 binds them so)                                                   *)
(*   list OPT_MMAP_cong = OPT_MMAP_CONG (misc/misc_p2.ml; quantifiers in    *)
(*     another order)                                                        *)
(*   arithmetic ADD_MONO_LESS_EQ = LE_ADD_LCANCEL, LESS_EQ_IFF_LESS_SUC =    *)
(*     GSYM LT_SUC_LE, TIMES2 = MULT_2; arithmetic and prim_rec LESS_MONO_EQ  *)
(*     = LT_SUC (HOL Light)                                                  *)
(*   pred_set MAX_SET_PROPERTY = in_max_set (hol4/basic.ml), IMAGE_11_INFINITE *)
(*     = INFINITE_IMAGE_INJ (HOL Light); HOL4 INFINITE_DIFF_FINITE is       *)
(*     pred_set_INFINITE_DIFF_FINITE here (HOL Light's theorem of that name  *)
(*     is HOL4's INFINITE_DIFF_FINITE')                                      *)
(*   relation RTC_CASES2 = RTC_CASES_L (HOL Light Library/rstc.ml); HOL4    *)
(*     inv is INV and EQC is RSTC there (inv_MOVES_OUT below uses them)      *)
(*   combin I_EQ_IDABS = I_DEF (HOL Light)                                   *)
(*   words word_0_n2w = VAL_WORD_0 (HOL Light)                               *)
(*   llist LL_ALL = llist_every (hol4/llist.ml)                              *)
(* APPEND_EQ_APPEND_MID is bound here to the helper of hol4/grammar.ml with  *)
(* HOL4's statement (LPARSEAUX_APPEND_EQ_APPEND_MID).                        *)
(*                                                                           *)
(* Not here: words word_exp and word_exp_def (the new theories' uses are of  *)
(* wordSem's word_exp, wl_word_exp in the port); bit BIT_DEF and             *)
(* NOT_BIT_GT_LOG2, logroot LOG_MOD, numposrep BIT_l2n_2 and EL_n2l,         *)
(* pred_set INFINITE_INHAB (no user).                                        *)
(*                                                                           *)
(* Added with the new constants, as HOL4's [simp] rules: MAP3_CONS3,        *)
(* MAP3_NIL, LENGTH_MAP3, mapPartial_EQ_NIL, FMERGE_WITH_KEY_FEMPTY,        *)
(* FMERGE_WITH_KEY_EQ_EMPTY, LFLATTEN_THM; also MAP3_ind.                    *)
(* HOL4 builds FLOOKUP_FMERGE_WITH_KEY, WORD_ADD_LEFT_LO2, WORD_ADD_LEFT_LS2,*)
(* WORD_ADD_RIGHT_LO, LOG2_w2n_lt and LIST_LENGTH_1 with SIMP_RULE or other *)
(* rules: the statements are what those rules give (comments at each).       *)
(* Lemmas named LIBXAUX_... are helpers of this file.                        *)
(* ========================================================================= *)

needs "hol4/vocab.ml";;
needs "hol4/list.ml";;
needs "hol4/rich_list.ml";;
needs "hol4/basic.ml";;
needs "hol4/finite_map.ml";;
needs "hol4/words4.ml";;
needs "hol4/numposrep.ml";;
needs "hol4/llist.ml";;
needs "hol4/grammar.ml";;

type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* list (HOL4 src/list/src/listScript.sml)                                   *)
(* ------------------------------------------------------------------------- *)

let dropWhile_def = cake_def
  `(dropWhile (P:A->bool) [] = []) /\
   (dropWhile P (CONS h t) = if P h then dropWhile P t else CONS h t)`;;
let _ = cake_add_simps [dropWhile_def];;

(* HOL4 UNZIP is a definition by recursion; vocab.ml defines UNZIP by       *)
(* MAP FST and MAP SND (HOL4 UNZIP_MAP), so HOL4's equations are a theorem. *)

let UNZIP = prove
 (`(UNZIP [] = ([]:A list,[]:B list)) /\
   (!(x:A#B) l. UNZIP (CONS x l) =
                (CONS (FST x) (FST (UNZIP l)),CONS (SND x) (SND (UNZIP l))))`,
  REWRITE_TAC[UNZIP_DEF; MAP]);;

let mapPartial_def = cake_def
  `(mapPartial (f:A->B option) [] = []) /\
   (mapPartial f (CONS x xs) =
      match f x with NONE -> mapPartial f xs
                   | SOME y -> CONS y (mapPartial f xs))`;;
let _ = cake_add_simps [mapPartial_def];;

let mapPartial_EQ_NIL = prove
 (`!(f:A->B option) xs. mapPartial f xs = [] <=> !x. MEM x xs ==> f x = NONE`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[mapPartial_def; MEM; TAUT `(a \/ b ==> c) <=> (a ==> c) /\ (b ==> c)`;
              FORALL_AND_THM; FORALL_UNWIND_THM2] THEN
  QCASES_ON "(f:A->B option) h" THEN
  ASM_REWRITE_TAC[option_CASE; NOT_CONS_NIL; option_DISTINCT]);;
let _ = cake_add_simps [mapPartial_EQ_NIL];;

let MAP3_def = cake_def
  `(MAP3 (f:A->B->C->D) (CONS h1 t1) (CONS h2 t2) (CONS h3 t3) =
      CONS (f h1 h2 h3) (MAP3 f t1 t2 t3)) /\
   (MAP3 f xs ys zs = [])`;;

let MAP3_ind = cake_ind "MAP3";;

let MAP3_CONS3 = prove
 (`!(f:A->B->C->D) h1 t1 h2 t2 h3 t3.
     MAP3 f (CONS h1 t1) (CONS h2 t2) (CONS h3 t3) =
     CONS (f h1 h2 h3) (MAP3 f t1 t2 t3)`,
  REWRITE_TAC[MAP3_def]);;
let _ = cake_add_simps [MAP3_CONS3];;

let MAP3_NIL = prove
 (`!(f:A->B->C->D) xs ys zs.
     MAP3 f [] ys zs = [] /\ MAP3 f xs [] zs = [] /\ MAP3 f xs ys [] = []`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[MAP3_def]);;
let _ = cake_add_simps [MAP3_NIL];;

let LENGTH_MAP3 = prove
 (`!(f:A->B->C->D) xs ys zs.
     LENGTH (MAP3 f xs ys zs) = MIN (MIN (LENGTH xs) (LENGTH ys)) (LENGTH zs)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[MAP3_def; LENGTH] THEN ARITH_TAC);;
let _ = cake_add_simps [LENGTH_MAP3];;

let ALL_DISTINCT_DROP = prove
 (`!(ls:A list) n. ALL_DISTINCT ls ==> ALL_DISTINCT (DROP n ls)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[DROP_DEF; ALL_DISTINCT] THEN
  REPEAT STRIP_TAC THEN COND_CASES_TAC THEN ASM_SIMP_TAC[ALL_DISTINCT]);;

let DROP_TAKE = prove
 (`!(xs:A list) n k. DROP n (TAKE k xs) = TAKE (k - n) (DROP n xs)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[TAKE_DEF; DROP_DEF] THEN
  REPEAT GEN_TAC THEN ASM_CASES_TAC `k = 0` THEN
  ASM_REWRITE_TAC[DROP_DEF; SUB_0; TAKE_0] THEN
  ASM_CASES_TAC `n = 0` THEN ASM_REWRITE_TAC[DROP_DEF; TAKE_DEF; SUB_0] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN ASM_ARITH_TAC);;

let LENGTH_dropWhile_LESS_EQ = prove
 (`!(P:A->bool) ls. LENGTH (dropWhile P ls) <= LENGTH ls`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[dropWhile_def; LENGTH; LE_REFL] THEN
  COND_CASES_TAC THEN REWRITE_TAC[LENGTH; LE_REFL] THEN ASM_ARITH_TAC);;

let EXISTS_NOT_EVERY = prove
 (`!(P:A->bool) l. EX P l <=> ~ALL (\x. ~P x) l`,
  REWRITE_TAC[GSYM NOT_EX]);;

let EVERY_CONG = prove
 (`!(l1:A list) l2 P P'.
     l1 = l2 /\ (!x. MEM x l2 ==> (P x <=> P' x)) ==> (ALL P l1 <=> ALL P' l2)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC) THEN
  REWRITE_TAC[EVERY_MEM] THEN ASM_MESON_TAC[]);;

let MEM_DROP = prove
 (`!(x:A) ls n. MEM x (DROP n ls) <=> ?m. m + n < LENGTH ls /\ x = EL (m + n) ls`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[list_MEM_EL; LENGTH_DROP; ARITH_RULE `m < l - n <=> m + n < l`] THEN
  EQ_TAC THEN DISCH_THEN(X_CHOOSE_THEN `m:num` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `m:num` THEN ASM_SIMP_TAC[EL_DROP]);;

let ALL_DISTINCT_SNOC = prove
 (`!(x:A) l. ALL_DISTINCT (SNOC x l) <=> ~MEM x l /\ ALL_DISTINCT l`,
  REWRITE_TAC[SNOC_APPEND; ALL_DISTINCT_APPEND; ALL_DISTINCT; MEM] THEN
  MESON_TAC[]);;

let ALL_DISTINCT_EL_IMP = prove
 (`!(l:A list) n1 n2.
     ALL_DISTINCT l /\ n1 < LENGTH l /\ n2 < LENGTH l
     ==> (EL n1 l = EL n2 l <=> n1 = n2)`,
  MESON_TAC[EL_ALL_DISTINCT_EL_EQ]);;

(* HOL4 APPEND_EQ_APPEND_MID: the helper of hol4/grammar.ml with the same  *)
(* statement                                                                *)

let APPEND_EQ_APPEND_MID = LPARSEAUX_APPEND_EQ_APPEND_MID;;

let FOLDL_CONG = prove
 (`!(l:A list) l' b b' (f:B->A->B) f'.
     l = l' /\ b = b' /\ (!x a. MEM x l' ==> f a x = f' a x)
     ==> FOLDL f b l = FOLDL f' b' l'`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 SUBST1_TAC (CONJUNCTS_THEN2 SUBST1_TAC MP_TAC)) THEN
  SPEC_TAC(`b':B`,`b':B`) THEN SPEC_TAC(`l':A list`,`l':A list`) THEN
  LIST_INDUCT_TAC THEN REWRITE_TAC[FOLDL; MEM] THEN
  X_GEN_TAC `b':B` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(f:B->A->B) b' h = f' b' h` SUBST1_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[]);;

let SUM_MAP_FOLDL = prove
 (`!(f:A->num) ls. SUM (MAP f ls) = FOLDL (\a e. a + f e) 0 ls`,
  GEN_TAC THEN
  SUBGOAL_THEN `!ls a. FOLDL (\a e. a + (f:A->num) e) a ls = a + SUM (MAP f ls)`
   (fun th -> REWRITE_TAC[th; ADD_CLAUSES]) THEN
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[FOLDL; MAP; SUM; ADD_CLAUSES; ADD_ASSOC]);;

let INFINITE_LIST_UNIV = prove
 (`INFINITE (:A list)`,
  MP_TAC(ISPEC `\n. REPLICATE n (ARB:A)` INFINITE_IMAGE_INJ) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL [MESON_TAC[LENGTH_REPLICATE]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `(:num)`) THEN REWRITE_TAC[num_INFINITE] THEN
  MESON_TAC[INFINITE_SUPERSET; SUBSET_UNIV]);;
let _ = cake_add_simps [INFINITE_LIST_UNIV];;

let LLEX_EL_THM = prove
 (`!(R:A->A->bool) l1 l2.
     LLEX R l1 l2 <=>
     ?n. n <= LENGTH l1 /\ n < LENGTH l2 /\ TAKE n l1 = TAKE n l2 /\
         (n < LENGTH l1 ==> R (EL n l1) (EL n l2))`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN X_GEN_TAC `l2:A list` THEN
  STRUCT_CASES_TAC(ISPEC `l2:A list` list_CASES) THEN
  REWRITE_TAC[LLEX_def; list_CASE; LENGTH; ARITH_RULE `~(n < 0)`;
              NOT_CONS_NIL] THENL
   [EXISTS_TAC `0` THEN REWRITE_TAC[TAKE_0; LE_REFL; LT_0];
    GEN_REWRITE_TAC RAND_CONV [EXISTS_NUM] THEN
    ASM_REWRITE_TAC[TAKE_0; TAKE_DEF; NOT_SUC; SUC_SUB1; EL; HD; TL; LE_SUC;
                    LT_SUC; LE_0; LT_0; CONS_11] THEN
    MESON_TAC[]]);;

let LENGTH_FILTER_LEQ_MONO = prove
 (`!(P:A->bool) Q.
     (!x. P x ==> Q x) ==> !ls. LENGTH (FILTER P ls) <= LENGTH (FILTER Q ls)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[FILTER; LENGTH; LE_REFL] THEN
  ASM_CASES_TAC `(P:A->bool) h` THEN ASM_CASES_TAC `(Q:A->bool) h` THEN
  ASM_REWRITE_TAC[LENGTH] THEN FIRST [ASM_ARITH_TAC; ASM_MESON_TAC[]]);;

let NOT_NULL_MEM = prove
 (`!l:A list. ~NULL l <=> ?e. MEM e l`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[NULL; MEM] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* rich_list (HOL4 src/list/src/rich_listScript.sml)                         *)
(* ------------------------------------------------------------------------- *)

let HEAD_MEM = prove
 (`!ls:A list. ~(ls = []) ==> MEM (HD ls) ls`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[NOT_CONS_NIL; HD; MEM]);;

let FILTER_IDEM = prove
 (`!(f:A->bool) l. FILTER f (FILTER f l) = FILTER f l`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[FILTER] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[FILTER]);;

let MAP_SND_FILTER_NEQ = prove
 (`!(z:B) (ls:(A#B)list).
     MAP SND (FILTER (\(x,y). ~(y = z)) ls) = FILTER (\y. ~(z = y)) (MAP SND ls)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[FILTER; MAP] THEN
  POP_ASSUM MP_TAC THEN SPEC_TAC(`h:A#B`,`p:A#B`) THEN
  REWRITE_TAC[FORALL_PAIR_THM; SND] THEN MAP_EVERY X_GEN_TAC [`a:A`; `b:B`] THEN
  DISCH_TAC THEN ASM_CASES_TAC `(b:B) = z` THEN ASM_REWRITE_TAC[MAP; SND] THEN
  SUBGOAL_THEN `~((z:B) = b)` (fun th -> ASM_REWRITE_TAC[th; MAP; SND]) THEN
  ASM_MESON_TAC[]);;

let ZIP_MAP_MAP = prove
 (`!(ls:A list) (f:A->B) (g:A->C).
     ZIP (MAP f ls) (MAP g ls) = MAP (\x. (f x,g x)) ls`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[MAP; ZIP_def]);;

let EL_LENGTH_APPEND_rwt = prove
 (`!(l1:A list) l2 n. ~NULL l2 /\ n = LENGTH l1 ==> EL n (APPEND l1 l2) = HD l2`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[EL_APPEND2; LE_REFL; SUB_REFL; EL]);;

(* ------------------------------------------------------------------------- *)
(* arithmetic (HOL4 src/num/theories/arithmeticScript.sml)                   *)
(* ------------------------------------------------------------------------- *)

let MAX_LT = prove
 (`!n m p. (p < MAX m n <=> p < m \/ p < n) /\ (MAX m n < p <=> m < p /\ n < p)`,
  REWRITE_TAC[MAX] THEN REPEAT GEN_TAC THEN COND_CASES_TAC THEN ASM_ARITH_TAC);;

let ADD_EQ_SUB = prove
 (`!m n p. n <= p ==> (m + n = p <=> m = p - n)`,
  ARITH_TAC);;

let LESS_ADD_SUC = prove
 (`!m n. m < m + SUC n`,
  ARITH_TAC);;

let SUB_RIGHT_LESS = prove
 (`!m n p. m - n < p <=> m < n + p /\ 0 < p`,
  ARITH_TAC);;

let LESS_EQ_SUC_REFL = prove
 (`!m. m <= SUC m`,
  ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* pred_set (HOL4 src/pred_set/src/pred_setScript.sml)                       *)
(* ------------------------------------------------------------------------- *)

let FUNPOW_eq_elim = prove
 (`!(f:A->A) n t t'. INJ f (:A) (:A) ==> (ITER n f t = ITER n f t' <=> t = t')`,
  GEN_TAC THEN INDUCT_TAC THEN REWRITE_TAC[ITER; INJ; IN_UNIV] THEN
  REPEAT STRIP_TAC THEN EQ_TAC THEN SIMP_TAC[] THEN
  ASM_MESON_TAC[INJ; IN_UNIV]);;

let FUNPOW_min_cancel = prove
 (`!(f:A->A) n n' X X'.
     n <= n' /\ INJ f (:A) (:A)
     ==> (ITER n f X = ITER n' f X' <=> X = ITER (n' - n) f X')`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `ITER n' (f:A->A) X' = ITER n f (ITER (n' - n) f X')`
   SUBST1_TAC THENL
   [REWRITE_TAC[ITER_ADD] THEN AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    ASM_ARITH_TAC;
    ASM_SIMP_TAC[FUNPOW_eq_elim]]);;

let compl_insert = prove
 (`!s (x:A). COMPL (x INSERT s) = COMPL s DELETE x`,
  REWRITE_TAC[EXTENSION; IN_COMPL; IN_INSERT; IN_DELETE] THEN MESON_TAC[]);;

let FINITE_PREIMAGE = prove
 (`!(f:A->B) s. (!x y. f x = f y <=> x = y) /\ FINITE s ==> FINITE (PREIMAGE f s)`,
  REWRITE_TAC[PREIMAGE_DEF] THEN MESON_TAC[FINITE_IMAGE_INJ]);;

let LIBXAUX_MAX_SET_ELIM = prove
 (`!s. FINITE s /\ ~(s = {})
       ==> MAX_SET s IN s /\ !x. x IN s ==> x <= MAX_SET s`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[X_LE_MAX_SET] THEN
  ASM_REWRITE_TAC[MAX_SET_DEF] THEN
  SUBGOAL_THEN `?m. m IN s /\ !n:num. n IN s ==> n <= m` MP_TAC THENL
   [MP_TAC (SPEC `\x:num. x IN s` num_MAX) THEN REWRITE_TAC[] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[GSYM th]) THEN
    CONJ_TAC THENL [ASM_MESON_TAC[MEMBER_NOT_EMPTY]; ASM_MESON_TAC[num_FINITE]];
    DISCH_THEN(MP_TAC o SELECT_RULE) THEN MESON_TAC[]]);;

let MAX_SET_THM = prove
 (`(MAX_SET {} = 0) /\
   (!e s. FINITE s ==> MAX_SET (e INSERT s) = MAX e (MAX_SET s))`,
  CONJ_TAC THENL [REWRITE_TAC[MAX_SET_DEF]; ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `(e:num) INSERT s` LIBXAUX_MAX_SET_ELIM) THEN
  ASM_REWRITE_TAC[FINITE_INSERT; NOT_INSERT_EMPTY; IN_INSERT] THEN
  ASM_CASES_TAC `s:num->bool = {}` THENL
   [ASM_REWRITE_TAC[NOT_IN_EMPTY; MAX_SET_DEF] THEN ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPEC `s:num->bool` LIBXAUX_MAX_SET_ELIM) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[MAX] THEN MESON_TAC[LE_ANTISYM; LE_TRANS; LE_CASES]);;

let IMAGE_11 = prove
 (`!(f:A->B) s1 s2.
     (!x y. f x = f y <=> x = y) ==> (IMAGE f s1 = IMAGE f s2 <=> s1 = s2)`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN SIMP_TAC[] THEN
  MP_TAC(ISPEC `f:A->B` INJECTIVE_IMAGE) THEN ASM_MESON_TAC[]);;

let INJ_CARD_IMAGE = prove
 (`!(f:A->B) s t. FINITE s ==> INJ f s t ==> CARD (IMAGE f s) = CARD s`,
  REWRITE_TAC[INJ] THEN MESON_TAC[CARD_IMAGE_INJ]);;

let DISJOINT_ALT' = prove
 (`!s t:A->bool. DISJOINT s t <=> !x. x IN t ==> ~(x IN s)`,
  SET_TAC[]);;

let DISJOINT_SUBSET' = prove
 (`!s t u:A->bool. DISJOINT s t /\ u SUBSET s ==> DISJOINT u t`,
  SET_TAC[]);;

let DISJOINT_BIGUNION = prove
 (`(!(s:(A->bool)->bool) t.
      DISJOINT (UNIONS s) t <=> !s'. s' IN s ==> DISJOINT s' t) /\
   (!(s:(A->bool)->bool) t.
      DISJOINT t (UNIONS s) <=> !s'. s' IN s ==> DISJOINT t s')`,
  REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; IN_UNIONS; NOT_IN_EMPTY] THEN
  MESON_TAC[]);;

(* HOL4 INFINITE_DIFF_FINITE: HOL Light's INFINITE_DIFF_FINITE concludes   *)
(* INFINITE (s DIFF t), as HOL4's INFINITE_DIFF_FINITE' does                 *)

let pred_set_INFINITE_DIFF_FINITE = prove
 (`!s t:A->bool. INFINITE s /\ FINITE t ==> ~(s DIFF t = {})`,
  MESON_TAC[INFINITE_DIFF_FINITE; INFINITE_NONEMPTY]);;

let INFINITE_INJ_NOT_SURJ = prove
 (`!s:A->bool. INFINITE s <=> ?f. INJ f s s /\ ~SURJ f s s`,
  GEN_TAC THEN EQ_TAC THENL
   [REWRITE_TAC[INFINITE_ENUMERATE_SUBSET] THEN
    DISCH_THEN(X_CHOOSE_THEN `r:num->A` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC
     `\x:A. if ?n. x = (r:num->A) n then r (SUC (@n. x = r n)) else x` THEN
    REWRITE_TAC[INJ; SURJ; NOT_FORALL_THM; NOT_IMP; NOT_EXISTS_THM] THEN
    SUBGOAL_THEN `!n. (@m. (r:num->A) n = r m) = n` ASSUME_TAC THENL
     [GEN_TAC THEN MATCH_MP_TAC SELECT_UNIQUE THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [X_GEN_TAC `x:A` THEN DISCH_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[];
      MAP_EVERY X_GEN_TAC [`x:A`; `y:A`] THEN
      ASM_CASES_TAC `?n. (x:A) = (r:num->A) n` THEN
      ASM_CASES_TAC `?n. (y:A) = (r:num->A) n` THEN ASM_REWRITE_TAC[] THEN
      REPEAT(FIRST_X_ASSUM(CHOOSE_THEN SUBST_ALL_TAC o
                           check (is_exists o concl))) THEN
      ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[SUC_INJ];
      REWRITE_TAC[DE_MORGAN_THM; NOT_FORALL_THM; NOT_IMP; NOT_EXISTS_THM] THEN
      DISJ2_TAC THEN EXISTS_TAC `(r:num->A) 0` THEN ASM_REWRITE_TAC[] THEN
      X_GEN_TAC `y:A` THEN ASM_CASES_TAC `?n. (y:A) = (r:num->A) n` THEN
      ASM_REWRITE_TAC[] THENL
       [FIRST_X_ASSUM(CHOOSE_THEN SUBST_ALL_TAC) THEN ASM_REWRITE_TAC[] THEN
        ASM_MESON_TAC[NOT_SUC];
        ASM_MESON_TAC[]]];
    REWRITE_TAC[INFINITE; INJ; SURJ] THEN
    DISCH_THEN(X_CHOOSE_THEN `f:A->A` STRIP_ASSUME_TAC) THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`s:A->bool`; `f:A->A`] SURJECTIVE_IFF_INJECTIVE) THEN
    ASM_REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN ASM_MESON_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* relation (HOL4 src/relation/relationScript.sml).  HOL4 inv is HOL Light's *)
(* INV and HOL4 EQC is HOL Light's RSTC (Library/rstc.ml: RC(TC(SC R)), the  *)
(* definition of HOL4 EQC).                                                   *)
(* ------------------------------------------------------------------------- *)

let inv_MOVES_OUT = prove
 (`!R:A->A->bool.
     INV (INV R) = R /\ SC (INV R) = SC R /\ RC (INV R) = INV (RC R) /\
     TC (INV R) = INV (TC R) /\ RTC (INV R) = INV (RTC R) /\
     RSTC (INV R) = RSTC R`,
  GEN_TAC THEN REWRITE_TAC[SC_INV_STRONG; RC_INV; TC_INV; RTC_INV; RSTC_INV] THEN
  REWRITE_TAC[FUN_EQ_THM; INV] THEN MESON_TAC[RSTC_SYM]);;

(* ------------------------------------------------------------------------- *)
(* option (HOL4 src/coretypes/optionScript.sml)                              *)
(* ------------------------------------------------------------------------- *)

let IF_NONE_EQUALS_OPTION = prove
 (`!P (X:A option) x.
     ((if P then X else NONE) = NONE <=> (P ==> IS_NONE X)) /\
     ((if P then NONE else X) = NONE <=> (IS_SOME X ==> P)) /\
     ((if P then X else NONE) = SOME x <=> P /\ X = SOME x) /\
     ((if P then NONE else X) = SOME x <=> ~P /\ X = SOME x)`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `P:bool` THEN ASM_REWRITE_TAC[] THEN
  STRUCT_CASES_TAC(ISPEC `X:A option` (cases "option")) THEN
  REWRITE_TAC[IS_NONE_DEF; IS_SOME_DEF; option_DISTINCT; option_INJ]);;

(* ------------------------------------------------------------------------- *)
(* pair (HOL4 src/coretypes/pairScript.sml)                                  *)
(* ------------------------------------------------------------------------- *)

let UNCURRY_CONG = prove
 (`!(f':A->B->C) f M' M.
     M = M' /\ (!x y. M' = (x,y) ==> f x y = f' x y)
     ==> UNCURRY f M = UNCURRY f' M'`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 SUBST1_TAC MP_TAC) THEN
  SPEC_TAC(`M':A#B`,`p:A#B`) THEN
  REWRITE_TAC[FORALL_PAIR_THM; UNCURRY_DEF; PAIR_EQ] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* quantHeuristics (HOL4 src/quantHeuristics/quantHeuristicsScript.sml).    *)
(* LIST_LENGTH_1 is generated by mk_length_upto_n_thms 1 there: the         *)
(* conjuncts below are its 14 rewrites for the length 1 and the 6 of        *)
(* LIST_LENGTH_THMS_0, in its order.                                         *)
(* ------------------------------------------------------------------------- *)

let LIBXAUX_LE_LENGTH_1 = prove
 (`!l:A list. 1 <= LENGTH l <=> ?l' e1. l = CONS e1 l'`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[LENGTH; ARITH_RULE `~(1 <= 0)`;
    ARITH_RULE `1 <= SUC n`; NOT_CONS_NIL; CONS_11] THEN MESON_TAC[]);;

let LIBXAUX_LE_LENGTH_PLUS = prove
 (`!(l:A list) x. x + 1 <= LENGTH l <=> ?l' e1. x <= LENGTH l' /\ l = CONS e1 l'`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[LENGTH; ARITH_RULE `~(x + 1 <= 0)`;
    ARITH_RULE `x + 1 <= SUC n <=> x <= n`; NOT_CONS_NIL; CONS_11] THEN
  MESON_TAC[]);;

let LIBXAUX_LENGTH_EQ_PLUS = prove
 (`!(l:A list) x. LENGTH l = x + 1 <=> ?l' e1. LENGTH l' = x /\ l = CONS e1 l'`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[LENGTH; ARITH_RULE `~(0 = x + 1)`;
    ARITH_RULE `SUC n = x + 1 <=> n = x`; NOT_CONS_NIL; CONS_11] THEN
  MESON_TAC[]);;

let LIST_LENGTH_1 = prove
 (`(!l:A list. LENGTH l = 1 <=> ?e1. l = [e1]) /\
   (!l:A list. 1 = LENGTH l <=> ?e1. l = [e1]) /\
   (!l:A list. 0 < LENGTH l <=> ?l' e1. l = CONS e1 l') /\
   (!l:A list. LENGTH l > 0 <=> ?l' e1. l = CONS e1 l') /\
   (!l:A list. 1 <= LENGTH l <=> ?l' e1. l = CONS e1 l') /\
   (!l:A list. LENGTH l >= 1 <=> ?l' e1. l = CONS e1 l') /\
   (!(l:A list) x. 1 + x <= LENGTH l <=> ?l' e1. x <= LENGTH l' /\ l = CONS e1 l') /\
   (!(l:A list) x. LENGTH l >= 1 + x <=> ?l' e1. x <= LENGTH l' /\ l = CONS e1 l') /\
   (!(l:A list) x. x + 1 <= LENGTH l <=> ?l' e1. x <= LENGTH l' /\ l = CONS e1 l') /\
   (!(l:A list) x. LENGTH l >= x + 1 <=> ?l' e1. x <= LENGTH l' /\ l = CONS e1 l') /\
   (!(l:A list) x. LENGTH l = 1 + x <=> ?l' e1. LENGTH l' = x /\ l = CONS e1 l') /\
   (!(l:A list) x. 1 + x = LENGTH l <=> ?l' e1. LENGTH l' = x /\ l = CONS e1 l') /\
   (!(l:A list) x. LENGTH l = x + 1 <=> ?l' e1. LENGTH l' = x /\ l = CONS e1 l') /\
   (!(l:A list) x. x + 1 = LENGTH l <=> ?l' e1. LENGTH l' = x /\ l = CONS e1 l') /\
   (!l:A list. LENGTH l = 0 <=> l = []) /\
   (!l:A list. 0 = LENGTH l <=> l = []) /\
   (!l:A list. LENGTH l < 1 <=> l = []) /\
   (!l:A list. 1 > LENGTH l <=> l = []) /\
   (!l:A list. 0 >= LENGTH l <=> l = []) /\
   (!l:A list. LENGTH l <= 0 <=> l = [])`,
  REWRITE_TAC[GSYM LISTAUX_LENGTH_EQ_1; GSYM LIBXAUX_LE_LENGTH_1;
              GSYM LIBXAUX_LE_LENGTH_PLUS; GSYM LIBXAUX_LENGTH_EQ_PLUS;
              GSYM LENGTH_EQ_NIL; GT; GE] THEN
  ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* finite_map (HOL4 src/finite_maps/finite_mapScript.sml)                    *)
(* ------------------------------------------------------------------------- *)

let FMERGE_WITH_KEY_DEF = new_specification ["FMERGE_WITH_KEY"]
 (prove
   (`?FMERGE_WITH_KEY. !(f:A->B->B->B) (m1:(A,B)fmap) m2.
       FDOM (FMERGE_WITH_KEY f m1 m2) = FDOM m1 UNION FDOM m2 /\
       (!x. FAPPLY (FMERGE_WITH_KEY f m1 m2) x =
            if x IN FDOM m1 /\ x IN FDOM m2 then f x (FAPPLY m1 x) (FAPPLY m2 x)
            else if x IN FDOM m1 then FAPPLY m1 x else FAPPLY m2 x)`,
    EXISTS_TAC `\(f:A->B->B->B) (m1:(A,B)fmap) (m2:(A,B)fmap).
                  fmap_ABS (\x. if x IN FDOM m1 /\ x IN FDOM m2
                                then SOME (f x (FAPPLY m1 x) (FAPPLY m2 x))
                                else if x IN FDOM m1 then FLOOKUP m1 x
                                else FLOOKUP m2 x)` THEN
    MAP_EVERY X_GEN_TAC [`f:A->B->B->B`; `m1:(A,B)fmap`; `m2:(A,B)fmap`] THEN
    REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `FLOOKUP (fmap_ABS (\x. if x IN FDOM m1 /\ x IN FDOM m2
                             then SOME ((f:A->B->B->B) x (FAPPLY m1 x) (FAPPLY m2 x))
                             else if x IN FDOM m1 then FLOOKUP (m1:(A,B)fmap) x
                             else FLOOKUP m2 x)) =
      (\x. if x IN FDOM m1 /\ x IN FDOM m2
           then SOME (f x (FAPPLY m1 x) (FAPPLY m2 x))
           else if x IN FDOM m1 then FLOOKUP m1 x
           else FLOOKUP m2 x)` ASSUME_TAC THENL
     [MATCH_MP_TAC FLOOKUP_fmap_ABS THEN
      EXISTS_TAC `FDOM (m1:(A,B)fmap) UNION FDOM (m2:(A,B)fmap)` THEN
      REWRITE_TAC[FINITE_UNION; FDOM_FINITE; IN_UNION] THEN
      REWRITE_TAC[FDOM_FLOOKUP] THEN MESON_TAC[option_DISTINCT];
      ALL_TAC] THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP FLOOKUP_EQ_FDOM_FAPPLY) THEN
    ASM_REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_UNION] THEN
    REWRITE_TAC[FDOM_FLOOKUP; FAPPLY_FLOOKUP] THEN
    CONJ_TAC THEN X_GEN_TAC `x:A` THEN
    ASM_CASES_TAC `FLOOKUP (m1:(A,B)fmap) x = NONE` THEN
    ASM_CASES_TAC `FLOOKUP (m2:(A,B)fmap) x = NONE` THEN
    ASM_REWRITE_TAC[option_DISTINCT; THE_DEF]));;

(* HOL4 states FLOOKUP_FMERGE_WITH_KEY as SIMP_RULE (srw_ss()) [] of a case *)
(* on (FLOOKUP m1 k, FLOOKUP m2 k) with OPTION_CHOICE; this is the result.  *)

let FLOOKUP_FMERGE_WITH_KEY = prove
 (CASE_TERM
  `!(f:A->B->B->B) m1 m2 k.
     FLOOKUP (FMERGE_WITH_KEY f m1 m2) k =
     match FLOOKUP m1 k with
       NONE -> FLOOKUP m2 k
     | SOME v1 -> (match FLOOKUP m2 k with
                     NONE -> SOME v1
                   | SOME v2 -> SOME (f k v1 v2))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[FLOOKUP_DEF; FMERGE_WITH_KEY_DEF; IN_UNION] THEN
  ASM_CASES_TAC `(k:A) IN FDOM (m1:(A,B)fmap)` THEN
  ASM_CASES_TAC `(k:A) IN FDOM (m2:(A,B)fmap)` THEN
  ASM_REWRITE_TAC[option_CASE]);;

let FMERGE_WITH_KEY_FEMPTY = prove
 (`!(f:A->B->B->B) m1 m2.
     FMERGE_WITH_KEY f FEMPTY m2 = m2 /\ FMERGE_WITH_KEY f m1 FEMPTY = m1`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[fmap_eq_flookup; FLOOKUP_FMERGE_WITH_KEY; FLOOKUP_EMPTY;
              option_CASE] THEN
  X_GEN_TAC `x:A` THEN QCASES_ON "FLOOKUP (m1:(A,B)fmap) x" THEN
  REWRITE_TAC[option_CASE]);;
let _ = cake_add_simps [FMERGE_WITH_KEY_FEMPTY];;

let FMERGE_WITH_KEY_EQ_EMPTY = prove
 (`!(f:A->B->B->B) m1 m2.
     FMERGE_WITH_KEY f m1 m2 = FEMPTY <=> m1 = FEMPTY /\ m2 = FEMPTY`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[fmap_eq_flookup; FLOOKUP_FMERGE_WITH_KEY; FLOOKUP_EMPTY] THEN
  EQ_TAC THENL
   [DISCH_TAC THEN REWRITE_TAC[AND_FORALL_THM] THEN X_GEN_TAC `x:A` THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:A`) THEN
    QCASES_ON "FLOOKUP (m1:(A,B)fmap) x" THEN
    QCASES_ON "FLOOKUP (m2:(A,B)fmap) x" THEN
    ASM_REWRITE_TAC[option_CASE; option_DISTINCT];
    STRIP_TAC THEN ASM_REWRITE_TAC[option_CASE]]);;
let _ = cake_add_simps [FMERGE_WITH_KEY_EQ_EMPTY];;

let DRESTRICT_FDOM = prove
 (`!f:(A,B)fmap. DRESTRICT f (FDOM f) = f`,
  REWRITE_TAC[fmap_eq_flookup; FLOOKUP_DRESTRICT] THEN
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[FLOOKUP_DEF]);;

let FMAP_MAP2_FUPDATE_LIST = prove
 (`!(l:(A#B)list) m (f:A#B->C).
     FMAP_MAP2 f (m |++ l) = FMAP_MAP2 f m |++ MAP (\(k,v). (k,f (k,v))) l`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[FUPDATE_LIST_THM; MAP] THEN
  POP_ASSUM MP_TAC THEN SPEC_TAC(`h:A#B`,`p:A#B`) THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[FMAP_MAP2_FUPDATE] THEN CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN
  REWRITE_TAC[]);;

let IN_FRANGE_DOMSUB_suff = prove
 (`!(fm:(A,B)fmap) k P.
     (!v. v IN FRANGE fm ==> P v) ==> (!v. v IN FRANGE (fm \\ k) ==> P v)`,
  REWRITE_TAC[IN_FRANGE_FLOOKUP; DOMSUB_FLOOKUP_THM] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  POP_ASSUM MP_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT] THEN
  MESON_TAC[]);;

let FRANGE_DOMSUB_SUBSET = prove
 (`!(fm:(A,B)fmap) k. FRANGE (fm \\ k) SUBSET FRANGE fm`,
  REWRITE_TAC[SUBSET; IN_FRANGE_FLOOKUP; DOMSUB_FLOOKUP_THM] THEN
  REPEAT GEN_TAC THEN DISCH_THEN(X_CHOOSE_THEN `k':A` MP_TAC) THEN
  COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT] THEN MESON_TAC[]);;

let IN_FRANGE_FUNION_suff = prove
 (`!(f1:(A,B)fmap) f2 P.
     (!v. v IN FRANGE f1 ==> P v) /\ (!v. v IN FRANGE f2 ==> P v)
     ==> (!v. v IN FRANGE (FUNION f1 f2) ==> P v)`,
  REWRITE_TAC[IN_FRANGE_FLOOKUP; FLOOKUP_FUNION] THEN REPEAT STRIP_TAC THEN
  POP_ASSUM MP_TAC THEN QCASES_ON "FLOOKUP (f1:(A,B)fmap) k" THEN
  REWRITE_TAC[option_CASE] THEN ASM_MESON_TAC[]);;

let IN_FRANGE_FUPDATE_suff = prove
 (`!(fm:(A,B)fmap) kv P.
     (!v. v IN FRANGE fm ==> P v) /\ P (SND kv)
     ==> (!v. v IN FRANGE (fm |+ kv) ==> P v)`,
  GEN_TAC THEN REWRITE_TAC[FORALL_PAIR_THM; SND] THEN
  REWRITE_TAC[IN_FRANGE_FLOOKUP; FLOOKUP_UPDATE] THEN REPEAT STRIP_TAC THEN
  POP_ASSUM MP_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[option_INJ] THEN
  ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* words (HOL4 src/n-bit/wordsScript.sml), in HOL Light's word vocabulary    *)
(* (src/hol4/words4.ml header): <+ word_ult, <=+ word_ule, n2w word, w2n     *)
(* val, -w word_neg, UINT_MAXw word_neg (word 1), INT_MINw word_INT_MIN.     *)
(* ------------------------------------------------------------------------- *)

let word_log2_def = new_definition
  `word_log2 (w:N word) = word (LOG2 (val w)):N word`;;

(* HOL4 word_L_def: word_L (INT_MINw) is HOL Light's word_INT_MIN *)

let word_L_def = prove
 (`word_INT_MIN:N word = word (INT_MIN(:N))`,
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_INT_MIN; VAL_WORD; INT_MIN_def] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOD_LT THEN REWRITE_TAC[LT_EXP] THEN
  MP_TAC(ISPEC `(:N)` DIMINDEX_GE_1) THEN ARITH_TAC);;

let WORD_LOWER_LOWER_EQ_TRANS = prove
 (`!a b c:N word. word_ult a b /\ word_ule b c ==> word_ult a c`,
  REWRITE_TAC[WORD_ULT; WORD_ULE] THEN ARITH_TAC);;

let WORD_LOWER_EQ_LOWER_TRANS = prove
 (`!a b c:N word. word_ule a b /\ word_ult b c ==> word_ult a c`,
  REWRITE_TAC[WORD_ULT; WORD_ULE] THEN ARITH_TAC);;

let WORD_LOWER_IMP_LOWER_OR_EQ = prove
 (`!a b:N word. word_ult a b ==> word_ule a b`,
  REWRITE_TAC[WORD_ULT; WORD_ULE] THEN ARITH_TAC);;

let WORD_LOWER_OR_EQ = prove
 (`!a b:N word. word_ule a b <=> word_ult a b \/ a = b`,
  REWRITE_TAC[WORD_ULT; WORD_ULE; GSYM VAL_EQ] THEN ARITH_TAC);;

let WORD_SUM_ZERO = prove
 (`!a b:N word. word_add a b = word 0 <=> a = word_neg b`,
  REPEAT GEN_TAC THEN EQ_TAC THEN DISCH_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o AP_TERM `\x:N word. word_sub x b`) THEN
    REWRITE_TAC[] THEN CONV_TAC WORD_RULE;
    ASM_REWRITE_TAC[] THEN CONV_TAC WORD_RULE]);;

let WORD_RIGHT_ADD_DISTRIB = prove
 (`!v w x:N word.
     word_mul (word_add v w) x = word_add (word_mul v x) (word_mul w x)`,
  CONV_TAC WORD_RULE);;

let WORD_MSB_INT_MIN_LS = prove
 (`!a:N word. word_msb a <=> word_ule word_INT_MIN a`,
  REWRITE_TAC[word_msb_def; MSB_VAL; WORD_ULE; VAL_WORD_INT_MIN]);;

(* the unsigned comparisons of sums and negations, by cases on overflow *)

let WORD_LESS_NEG_LEFT = prove
 (`!a b:N word.
     word_ult (word_neg a) b <=>
     ~(b = word 0) /\ (a = word 0 \/ word_ult (word_neg b) a)`,
  REWRITE_TAC[WORD_ULT; WORD_ULE; GSYM VAL_EQ; VAL_WORD_NEG_CASES; VAL_WORD_0] THEN
  REPEAT GEN_TAC THEN
  MAP_EVERY (fun t -> MP_TAC(ISPEC t VAL_BOUND)) [`a:N word`; `b:N word`] THEN
  REPEAT COND_CASES_TAC THEN ASM_ARITH_TAC);;

(* HOL4 derives WORD_ADD_LEFT_LO2 and WORD_ADD_LEFT_LS2 from                *)
(* WORD_ADD_LEFT_LO/LS with SIMP_RULE, and WORD_ADD_RIGHT_LO with           *)
(* SIMP_CONV; the statements below are what those rules give.               *)

let WORD_ADD_LEFT_LO2 = prove
 (`!c a:N word.
     word_ult (word_add c a) a <=>
     ~(a = word 0) /\
     (~(c = word 0) /\ word_ult (word_neg c) a \/ a = word_neg c)`,
  REWRITE_TAC[WORD_ULT; WORD_ULE; GSYM VAL_EQ; VAL_WORD_ADD_CASES;
              VAL_WORD_NEG_CASES; VAL_WORD_0] THEN
  REPEAT GEN_TAC THEN
  MAP_EVERY (fun t -> MP_TAC(ISPEC t VAL_BOUND)) [`a:N word`; `c:N word`] THEN
  REPEAT COND_CASES_TAC THEN ASM_ARITH_TAC);;

let WORD_ADD_LEFT_LS2 = prove
 (`!c a:N word.
     word_ule (word_add c a) a <=>
     c = word 0 \/
     ~(a = word 0) /\ (word_ult (word_neg c) a \/ a = word_neg c)`,
  REWRITE_TAC[WORD_ULT; WORD_ULE; GSYM VAL_EQ; VAL_WORD_ADD_CASES;
              VAL_WORD_NEG_CASES; VAL_WORD_0] THEN
  REPEAT GEN_TAC THEN
  MAP_EVERY (fun t -> MP_TAC(ISPEC t VAL_BOUND)) [`a:N word`; `c:N word`] THEN
  REPEAT COND_CASES_TAC THEN ASM_ARITH_TAC);;

let LIBXAUX_VAL_WORD_SUB = prove
 (`!(a:N word) (c:N word). val(word(val a - val c):N word) = val a - val c`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC VAL_WORD_EQ THEN
  MP_TAC(ISPEC `a:N word` VAL_BOUND) THEN ARITH_TAC);;

let WORD_ADD_RIGHT_LO = prove
 (`!c a b:N word.
     word_ult a (word_add b c) <=>
     if word_ule c a then
       let x = word (val a - val c):N word in
       word_ult x b /\ (c = word 0 \/ word_ult b (word_add (word_neg a) x))
     else word_ult b (word_neg c) \/ word_ult (word_add (word_neg c) a) b`,
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  REWRITE_TAC[WORD_ULT; WORD_ULE; GSYM VAL_EQ; VAL_WORD_ADD_CASES;
              VAL_WORD_NEG_CASES; VAL_WORD_0; LIBXAUX_VAL_WORD_SUB] THEN
  REPEAT GEN_TAC THEN
  MAP_EVERY (fun t -> MP_TAC(ISPEC t VAL_BOUND))
    [`a:N word`; `b:N word`; `c:N word`] THEN
  REPEAT COND_CASES_TAC THEN ASM_ARITH_TAC);;

let w2n_plus1 = prove
 (`!a:N word.
     val a + 1 =
     if a = word_neg (word 1) then dimword(:N) else val (word_add a (word 1))`,
  GEN_TAC THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_NEG_1; VAL_WORD_ADD_CASES; VAL_WORD_1;
              dimword_def] THEN
  MP_TAC(ISPEC `a:N word` VAL_BOUND) THEN
  REPEAT COND_CASES_TAC THEN ASM_ARITH_TAC);;

let LOG2_w2n_lt = prove
 (`!w:N word. ~(w = word 0) ==> LOG2 (val w) < dimindex(:N)`,
  GEN_TAC THEN REWRITE_TAC[GSYM VAL_EQ_0] THEN
  MP_TAC(SPECL [`val(w:N word)`; `dimindex(:N)`] LT_TWOEXP) THEN
  REWRITE_TAC[VAL_BOUND] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* logroot and numeral_bit (HOL4 src/num/extra_theories/logrootScript.sml,   *)
(* numeral_bitScript.sml)                                                     *)
(* ------------------------------------------------------------------------- *)

let LOG2_LT_SELF = prove
 (`!n. 0 < n ==> LOG2 n < n`,
  MESON_TAC[LOG2_PROPERTY; LT_POW2_REFL; LTE_TRANS]);;

(* HOL4 LOG_compute has FAIL LOG v m n with v the bool variable named      *)
(* "base < 2 or n = 0" (an EVAL error marker; FAIL x y = x)                 *)

let LOG_compute =
  let tm = vsubst [mk_var("base < 2 or n = 0",`:bool`),`msgv:bool`]
   `!m n. LOG m n =
          if m < 2 \/ n = 0 then FAIL LOG (msgv:bool) m n
          else if n < m then 0 else SUC (LOG m (n DIV m))` in
  prove
   (tm,
    REPEAT GEN_TAC THEN REWRITE_TAC[FAIL_DEF] THEN
    COND_CASES_TAC THEN REWRITE_TAC[] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[DE_MORGAN_THM; NOT_LT]) THEN
    COND_CASES_TAC THEN ASM_SIMP_TAC[LSTRAUX_LOG_LT] THEN
    MATCH_MP_TAC LSTRAUX_LOG_DIV THEN ASM_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* alignment and byte (HOL4 src/n-bit/alignmentScript.sml, byteScript.sml)   *)
(* ------------------------------------------------------------------------- *)

let byte_align_aligned = prove
 (`!x:N word. byte_aligned x <=> byte_align x = x`,
  REWRITE_TAC[byte_aligned_def; byte_align_def; aligned_def]);;

let aligned_imp = prove
 (`!p q (w:N word).
     p < q /\ alignment_aligned q w ==> alignment_aligned p w`,
  REWRITE_TAC[aligned_w2n] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `2 EXP q = 2 EXP p * 2 EXP (q - p)` SUBST_ALL_TAC THENL
   [REWRITE_TAC[GSYM EXP_ADD] THEN AP_TERM_TAC THEN ASM_ARITH_TAC;
    ONCE_REWRITE_TAC[GSYM(ISPECL [`val(w:N word)`; `2 EXP p`; `2 EXP (q - p)`]
                         MOD_MOD)] THEN
    ASM_REWRITE_TAC[MOD_0]]);;

let set_byte_get_byte = prove
 (`!(a:N word) (w:N word) be.
     8 <= dimindex(:N) ==> set_byte a (get_byte a w be) w be = w`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPECL [`a:N word`; `be:bool`] o MATCH_MP
   (MESON[BYTE_INDEX_BOUND]
     `8 <= dimindex(:N) ==> !a:N word be. byte_index a be + 8 <= dimindex(:N)`)) THEN
  REWRITE_TAC[get_byte_DEF; set_byte_DEF] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  SPEC_TAC(`byte_index (a:N word) be`,`k:num`) THEN GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[WORD_EQ_BITS_ALT] THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[BIT_WORD_ZX; BIT_WORD_USHR; BIT_WORD_OR_ALT; BIT_WORD_SLICE_ALT;
                  BIT_WORD_SHL; DIMINDEX_8] THEN
  ASM_CASES_TAC `k:num <= i` THENL
   [ASM_SIMP_TAC[SUB_ADD; ARITH_RULE `k <= i ==> ~(i < k)`;
                 ARITH_RULE `i < d ==> i - k < d`] THEN
    MESON_TAC[ARITH_RULE `k + 8 <= i \/ i - k < 8`];
    ASM_SIMP_TAC[ARITH_RULE `~(k <= i) ==> ~(k + 8 <= i) /\ i < k`; LE_0]]);;

(* ------------------------------------------------------------------------- *)
(* llist (HOL4 src/coalgebras/llistScript.sml).  HOL4 LL_ALL is every.       *)
(* ------------------------------------------------------------------------- *)

let LIBXAUX_MINIMAL_SUC = prove
 (`!P. (?n. P (SUC n)) /\ ~P 0 ==> (minimal) P = SUC (minimal n. P (SUC n))`,
  GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC MINIMAL_UNIQUE THEN
  MP_TAC(ISPEC `\n. (P:num->bool) (SUC n)` MINIMAL) THEN REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o fst o EQ_IMP_RULE) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; STRIP_TAC] THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `m:num` THEN STRUCT_CASES_TAC(SPEC `m:num` num_CASES) THEN
  ASM_REWRITE_TAC[LT_SUC] THEN ASM_MESON_TAC[]);;

(* MESON fails on llist_every ((=) LNIL) (an unapplied (=), CONVENTIONS section  *)
(* 10), so these proofs rewrite instead                                     *)

let LFLATTEN = new_specification ["LFLATTEN"]
 (prove
   (`?LFLATTEN. !ll:(A llist)llist.
       LFLATTEN ll =
       if llist_every ((=) LNIL) ll then LNIL
       else if THE (LHD ll) = LNIL then LFLATTEN (THE (LTL ll))
       else LCONS (THE (LHD (THE (LHD ll))))
                  (LFLATTEN (LCONS (THE (LTL (THE (LHD ll)))) (THE (LTL ll))))`,
    ABBREV_TAC
     `f = \ll:(A llist)llist.
        if llist_every ((=) LNIL) ll then NONE
        else SOME (LCONS (THE (LTL (THE (LNTH (minimal n.
                                ?e. LNTH n ll = SOME e /\ ~(e = LNIL)) ll))))
                         (THE (LDROP (SUC (minimal n.
                                ?e. LNTH n ll = SOME e /\ ~(e = LNIL))) ll)),
                   THE (LHD (THE (LNTH (minimal n.
                                ?e. LNTH n ll = SOME e /\ ~(e = LNIL)) ll))))` THEN
    EXISTS_TAC `LUNFOLD (f:(A llist)llist->((A llist)llist#A)option)` THEN
    X_GEN_TAC `ll:(A llist)llist` THEN
    ASM_CASES_TAC `llist_every ((=) LNIL) (ll:(A llist)llist)` THEN ASM_REWRITE_TAC[] THENL
     [GEN_REWRITE_TAC LAND_CONV [LUNFOLD] THEN EXPAND_TAC "f" THEN
      ASM_REWRITE_TAC[option_CASE];
      ALL_TAC] THEN
    MP_TAC(ISPEC `ll:(A llist)llist` llist_CASES) THEN
    DISCH_THEN(DISJ_CASES_THEN2 SUBST_ALL_TAC
      (X_CHOOSE_THEN `h:A llist` (X_CHOOSE_THEN `t:(A llist)llist` SUBST_ALL_TAC)))
    THENL
     [UNDISCH_TAC `~llist_every ((=) LNIL) (LNIL:(A llist)llist)` THEN
      REWRITE_TAC[every_thm];
      ALL_TAC] THEN
    REWRITE_TAC[LHD_THM; LTL_THM; THE_DEF] THEN
    ASM_CASES_TAC `h:A llist = LNIL` THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN REWRITE_TAC[] THEN
      SUBGOAL_THEN `?n e. LNTH n (t:(A llist)llist) = SOME e /\ ~(e = LNIL)`
      ASSUME_TAC THENL
       [UNDISCH_TAC `~llist_every ((=) LNIL) (LCONS LNIL (t:(A llist)llist))` THEN
        REWRITE_TAC[every_thm; every_LNTH; NOT_FORALL_THM; NOT_IMP] THEN
        MESON_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN `~llist_every ((=) LNIL) (t:(A llist)llist)` ASSUME_TAC THENL
       [UNDISCH_TAC `~llist_every ((=) LNIL) (LCONS LNIL (t:(A llist)llist))` THEN
        REWRITE_TAC[every_thm];
        ALL_TAC] THEN
      SUBGOAL_THEN
       `(minimal n. ?e. LNTH n (LCONS LNIL t) = SOME e /\ ~(e = LNIL)) =
        SUC (minimal n. ?e. LNTH n (t:(A llist)llist) = SOME e /\ ~(e = LNIL))`
      ASSUME_TAC THENL
       [W(MP_TAC o PART_MATCH (lhand o rand) LIBXAUX_MINIMAL_SUC o lhand o snd) THEN
        REWRITE_TAC[LNTH_THM; option_INJ] THEN
        ANTS_TAC THENL
         [CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; MESON_TAC[]]; SIMP_TAC[]];
        ALL_TAC] THEN
      SUBGOAL_THEN `(f:(A llist)llist->((A llist)llist#A)option) (LCONS LNIL t) = f t`
      ASSUME_TAC THENL
       [EXPAND_TAC "f" THEN ASM_REWRITE_TAC[LNTH_THM; LDROP_THM];
        ALL_TAC] THEN
      GEN_REWRITE_TAC LAND_CONV [LUNFOLD] THEN
      GEN_REWRITE_TAC RAND_CONV [LUNFOLD] THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `(minimal n. ?e. LNTH n (LCONS h t) = SOME e /\ ~(e:A llist = LNIL)) = 0`
    ASSUME_TAC THENL
     [MATCH_MP_TAC MINIMAL_UNIQUE THEN REWRITE_TAC[LNTH_THM; option_INJ; LT] THEN
      EXISTS_TAC `h:A llist` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    GEN_REWRITE_TAC LAND_CONV [LUNFOLD] THEN EXPAND_TAC "f" THEN
    ASM_REWRITE_TAC[LNTH_THM; LDROP_THM; THE_DEF; option_CASE; pair_CASE]));;

let LFLATTEN_THM = prove
 (`(LFLATTEN (LNIL:(A llist)llist) = LNIL) /\
   (!t:(A llist)llist. LFLATTEN (LCONS LNIL t) = LFLATTEN t) /\
   (!(h:A) t tl. LFLATTEN (LCONS (LCONS h t) tl) = LCONS h (LFLATTEN (LCONS t tl)))`,
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC LAND_CONV [LFLATTEN] THEN
  REWRITE_TAC[every_thm; LHD_THM; LTL_THM; THE_DEF; LCONS_NOT_NIL] THEN
  COND_CASES_TAC THEN REWRITE_TAC[] THEN
  GEN_REWRITE_TAC RAND_CONV [LFLATTEN] THEN ASM_REWRITE_TAC[]);;
let _ = cake_add_simps [LFLATTEN_THM];;

let LFLATTEN_EQ_NIL = prove
 (`!ll:(A llist)llist. LFLATTEN ll = LNIL <=> llist_every ((=) LNIL) ll`,
  GEN_TAC THEN EQ_TAC THENL
   [SPEC_TAC(`ll:(A llist)llist`,`ll:(A llist)llist`) THEN
    MATCH_MP_TAC llist_every_coind THEN
    MAP_EVERY X_GEN_TAC [`h:A llist`; `t:(A llist)llist`] THEN
    MP_TAC(ISPEC `h:A llist` llist_CASES) THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[LFLATTEN_THM; LCONS_NOT_NIL];
    ONCE_REWRITE_TAC[LFLATTEN] THEN SIMP_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Lemmas used by several later files.                                       *)
(* ------------------------------------------------------------------------- *)

let LIBXAUX_dropWhile_CONS = prove
 (`!P (l:A list) h t. dropWhile P l = CONS h t ==> LENGTH t < LENGTH l`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`P:A->bool`; `l:A list`] LENGTH_dropWhile_LESS_EQ) THEN
  ASM_REWRITE_TAC[LENGTH] THEN ARITH_TAC);;

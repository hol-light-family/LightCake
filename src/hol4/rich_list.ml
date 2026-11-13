(* ========================================================================= *)
(* rich_list: port of HOL4 src/list/src/rich_listScript.sml (HOL4 library). *)
(* Enriched theory of lists: rich_list constants (SPLITL here, the others  *)
(* in vocab.ml) and the rich_list theorems used by the CakeML closure,     *)
(* including the list theorems that rich_list re-exports.                  *)
(*                                                                           *)
(* Notation: HOL4 IS_PREFIX x y is an overload for isPREFIX y x, so it is  *)
(* written y <<= x here; EVERY = ALL, EXISTS = EX, LIST_REL = EVERY2 =     *)
(* ALL2, FRONT = BUTLAST, GENLIST = list_of_seq, FOLDR f e l = ITLIST f l *)
(* e, LIST_TO_SET = set_of_list, SIGMA = SUM_IMAGE (vocab.ml header).      *)
(* Facts of listTheory needed here have local names RICHAUX_...            *)
(* ========================================================================= *)

needs "hol4/vocab.ml";;

type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Local helpers: TAKE and DROP in SUC form (HOL4 rich_list TAKE, DROP)      *)
(* and facts of listTheory, with local names RICHAUX_...                     *)
(* ------------------------------------------------------------------------- *)

let TAKE = prove
 (`(!l:A list. TAKE 0 l = []) /\
   (!n (x:A) l. TAKE (SUC n) (CONS x l) = CONS x (TAKE n l))`,
  CONJ_TAC THENL [LIST_INDUCT_TAC; ALL_TAC] THEN
  REWRITE_TAC[TAKE_DEF; NOT_SUC; SUC_SUB1]);;

let DROP = prove
 (`(!l:A list. DROP 0 l = l) /\
   (!n (x:A) l. DROP (SUC n) (CONS x l) = DROP n l)`,
  CONJ_TAC THENL [LIST_INDUCT_TAC; ALL_TAC] THEN
  REWRITE_TAC[DROP_DEF; NOT_SUC; SUC_SUB1]);;

let RICHAUX_TAKE_NIL = prove
 (`!n. TAKE n ([]:A list) = []`,
  REWRITE_TAC[TAKE_DEF]);;

let RICHAUX_DROP_NIL = prove
 (`!n. DROP n ([]:A list) = []`,
  REWRITE_TAC[DROP_DEF]);;

let RICHAUX_TAKE_CLAUSES = prove
 (`(!n. TAKE n ([]:A list) = []) /\
   (!l:A list. TAKE 0 l = []) /\
   (!n (x:A) l. TAKE (SUC n) (CONS x l) = CONS x (TAKE n l))`,
  REWRITE_TAC[RICHAUX_TAKE_NIL; TAKE]);;

let RICHAUX_DROP_CLAUSES = prove
 (`(!n. DROP n ([]:A list) = []) /\
   (!l:A list. DROP 0 l = l) /\
   (!n (x:A) l. DROP (SUC n) (CONS x l) = DROP n l)`,
  REWRITE_TAC[RICHAUX_DROP_NIL; DROP]);;

let RICHAUX_LENGTH_TAKE_EQ = prove
 (`!n (l:A list). LENGTH (TAKE n l) = MIN n (LENGTH l)`,
  INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[RICHAUX_TAKE_CLAUSES; LENGTH] THEN ARITH_TAC);;

let RICHAUX_LENGTH_TAKE = prove
 (`!n (l:A list). n <= LENGTH l ==> LENGTH (TAKE n l) = n`,
  REWRITE_TAC[RICHAUX_LENGTH_TAKE_EQ] THEN ARITH_TAC);;

let RICHAUX_LENGTH_DROP = prove
 (`!n (l:A list). LENGTH (DROP n l) = LENGTH l - n`,
  INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[RICHAUX_DROP_CLAUSES; LENGTH] THEN ARITH_TAC);;

let RICHAUX_TAKE_DROP = prove
 (`!n (l:A list). APPEND (TAKE n l) (DROP n l) = l`,
  INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[RICHAUX_TAKE_CLAUSES; RICHAUX_DROP_CLAUSES; APPEND]);;

let RICHAUX_TAKE_LENGTH_TOO_LONG = prove
 (`!n (l:A list). LENGTH l <= n ==> TAKE n l = l`,
  INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  ASM_SIMP_TAC[RICHAUX_TAKE_CLAUSES; LENGTH; LE_SUC] THEN ARITH_TAC);;

let RICHAUX_DROP_LENGTH_TOO_LONG = prove
 (`!n (l:A list). LENGTH l <= n ==> DROP n l = []`,
  INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  ASM_SIMP_TAC[RICHAUX_DROP_CLAUSES; LENGTH; LE_SUC] THEN ARITH_TAC);;

let RICHAUX_TAKE_LENGTH_ID = prove
 (`!l:A list. TAKE (LENGTH l) l = l`,
  SIMP_TAC[RICHAUX_TAKE_LENGTH_TOO_LONG; LE_REFL]);;

let RICHAUX_MEM_REVERSE = prove
 (`!(x:A) l. MEM x (REVERSE l) <=> MEM x l`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[REVERSE; MEM; MEM_APPEND] THEN MESON_TAC[]);;

let RICHAUX_ALL2_LENGTH = prove
 (`!(P:A->B->bool) l1 l2. ALL2 P l1 l2 ==> LENGTH l1 = LENGTH l2`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[ALL2; LENGTH; SUC_INJ; NOT_SUC] THEN ASM_MESON_TAC[]);;

let RICHAUX_FORALL_LT_SUC = prove
 (`!P m. (!n. n < SUC m ==> P n) <=> P 0 /\ (!n. n < m ==> P (SUC n))`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [MESON_TAC[LT_0; LT_SUC];
    STRIP_TAC THEN INDUCT_TAC THEN ASM_MESON_TAC[LT_SUC]]);;

let RICHAUX_ALL2_EL = prove
 (`!(P:A->B->bool) l1 l2.
     ALL2 P l1 l2 <=>
     LENGTH l1 = LENGTH l2 /\ !n. n < LENGTH l1 ==> P (EL n l1) (EL n l2)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[ALL2; LENGTH; NOT_SUC; SUC_INJ; CONJUNCT1 LT;
                  RICHAUX_FORALL_LT_SUC] THEN
  REWRITE_TAC[EL; HD; TL] THEN MESON_TAC[]);;

let RICHAUX_isPREFIX_THM = prove
 (`(!l:A list. [] <<= l <=> T) /\
   (!(h:A) t. CONS h t <<= [] <=> F) /\
   (!(h1:A) t1 h2 t2. CONS h1 t1 <<= CONS h2 t2 <=> h1 = h2 /\ t1 <<= t2)`,
  REWRITE_TAC[isPREFIX; list_CASE]);;

(* ------------------------------------------------------------------------- *)
(* List theorems that HOL4 rich_list re-exports from listTheory              *)
(* (in listScript order; helpers RICHAUX_... just before their use).         *)
(* ------------------------------------------------------------------------- *)

let NULL_DEF = NULL;;

let FOLDR = ITLIST;;

let NOT_NIL_CONS = prove
 (`!(a0:A) a1. ~([] = CONS a0 a1)`,
  MESON_TAC[NOT_CONS_NIL]);;

let CONS = prove
 (`!l:A list. ~NULL l ==> CONS (HD l) (TL l) = l`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[NULL; HD; TL]);;

let MAP_EQ_f = prove
 (`!(f1:A->B) f2 l. MAP f1 l = MAP f2 l <=> !e. MEM e l ==> f1 e = f2 e`,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[MAP; MEM; CONS_11] THEN MESON_TAC[]);;

(* HOL4: MAP_o (HOL Light's MAP_o is the pointwise form) *)

let rich_list_MAP_o = prove
 (`!(f:B->C) (g:A->B). MAP (f o g) = MAP f o MAP g`,
  REWRITE_TAC[FUN_EQ_THM; o_THM; MAP_o]);;

let MAP_MAP_o = prove
 (`!(f:B->C) (g:A->B) l. MAP f (MAP g l) = MAP (f o g) l`,
  REWRITE_TAC[MAP_o]);;

let FLAT_APPEND = prove
 (`!l1 l2:(A list) list. FLAT (APPEND l1 l2) = APPEND (FLAT l1) (FLAT l2)`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[FLAT; APPEND; APPEND_ASSOC]);;

let LENGTH_NIL = LENGTH_EQ_NIL;;

let NULL_EQ_NIL = prove
 (`!l:A list. NULL l <=> l = []`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[NULL; NOT_CONS_NIL]);;

let LENGTH_CONS = prove
 (`!(l:A list) n. LENGTH l = SUC n <=> ?h l'. LENGTH l' = n /\ l = CONS h l'`,
  REWRITE_TAC[LENGTH_EQ_CONS] THEN MESON_TAC[]);;

let RICHAUX_APPEND_11_LENGTH1 = prove
 (`!(l1:A list) l2 l1' l2'.
     LENGTH l1 = LENGTH l1'
     ==> (APPEND l1 l2 = APPEND l1' l2' <=> l1 = l1' /\ l2 = l2')`,
  LIST_INDUCT_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN
  ASM_SIMP_TAC[LENGTH; NOT_SUC; GSYM NOT_SUC; SUC_INJ; APPEND; CONS_11;
               CONJ_ASSOC]);;

let APPEND_LENGTH_EQ = prove
 (`!(l1:A list) l1'.
     LENGTH l1 = LENGTH l1'
     ==> !l2 l2'. LENGTH l2 = LENGTH l2'
                  ==> (APPEND l1 l2 = APPEND l1' l2' <=> l1 = l1' /\ l2 = l2')`,
  MESON_TAC[RICHAUX_APPEND_11_LENGTH1]);;

let APPEND_11_LENGTH = prove
 (`(!(l1:A list) l2 l1' l2'.
      LENGTH l1 = LENGTH l1'
      ==> (APPEND l1 l2 = APPEND l1' l2' <=> l1 = l1' /\ l2 = l2')) /\
   (!(l1:A list) l2 l1' l2'.
      LENGTH l2 = LENGTH l2'
      ==> (APPEND l1 l2 = APPEND l1' l2' <=> l1 = l1' /\ l2 = l2'))`,
  CONJ_TAC THENL [ACCEPT_TAC RICHAUX_APPEND_11_LENGTH1; ALL_TAC] THEN
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [DISCH_TAC THEN
    SUBGOAL_THEN `LENGTH (l1:A list) = LENGTH (l1':A list)` ASSUME_TAC THENL
     [FIRST_ASSUM(MP_TAC o AP_TERM `LENGTH:A list->num`) THEN
      ASM_REWRITE_TAC[LENGTH_APPEND; EQ_ADD_RCANCEL]; ALL_TAC] THEN
    ASM_MESON_TAC[RICHAUX_APPEND_11_LENGTH1];
    MESON_TAC[]]);;

(* HOL4: LENGTH_ZIP (HOL Light's LENGTH_ZIP has only the second conjunct) *)

let rich_list_LENGTH_ZIP = prove
 (`!(l1:A list) (l2:B list).
     LENGTH l1 = LENGTH l2
     ==> LENGTH (ZIP l1 l2) = LENGTH l1 /\ LENGTH (ZIP l1 l2) = LENGTH l2`,
  MESON_TAC[LENGTH_ZIP]);;

let MAP2_ZIP = prove
 (`!(l1:A list) (l2:B list).
     LENGTH l1 = LENGTH l2
     ==> !f:A->B->C. MAP2 f l1 l2 = MAP (UNCURRY f) (ZIP l1 l2)`,
  LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  ASM_SIMP_TAC[LENGTH; NOT_SUC; GSYM NOT_SUC; SUC_INJ; MAP2; ZIP; MAP;
               UNCURRY_DEF]);;

let EL_MEM = prove
 (`!n (l:A list). n < LENGTH l ==> MEM (EL n l) l`,
  MESON_TAC[MEM_EL]);;

let REVERSE_EQ_NIL = REVERSE_EQ_EMPTY;;

let FILTER_REVERSE = prove
 (`!(l:A list) P. FILTER P (REVERSE l) = REVERSE (FILTER P l)`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[REVERSE; FILTER; FILTER_APPEND] THEN
  GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[REVERSE; APPEND_NIL]);;

let LAST_CONS = prove
 (`(!x:A. LAST [x] = x) /\
   (!(x:A) y z. LAST (CONS x (CONS y z)) = LAST (CONS y z))`,
  REWRITE_TAC[LAST_CLAUSES]);;

let EL_TAKE = prove
 (`!n x (l:A list). x < n ==> EL x (TAKE n l) = EL x l`,
  INDUCT_TAC THEN REWRITE_TAC[CONJUNCT1 LT] THEN
  INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  ASM_SIMP_TAC[RICHAUX_TAKE_CLAUSES; EL; HD; TL; LT_SUC]);;

let DROP_LENGTH_NIL = prove
 (`!l:A list. DROP (LENGTH l) l = []`,
  SIMP_TAC[RICHAUX_DROP_LENGTH_TOO_LONG; LE_REFL]);;

let DROP_APPEND = prove
 (`!n (l1:A list) l2.
     DROP n (APPEND l1 l2) = APPEND (DROP n l1) (DROP (n - LENGTH l1) l2)`,
  ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[APPEND; LENGTH; SUB_0; RICHAUX_DROP_CLAUSES] THEN
  INDUCT_TAC THEN
  ASM_REWRITE_TAC[RICHAUX_DROP_CLAUSES; SUB_0; SUB_SUC; APPEND]);;

let DROP_APPEND1 = prove
 (`!n (l1:A list).
     n <= LENGTH l1 ==> !l2. DROP n (APPEND l1 l2) = APPEND (DROP n l1) l2`,
  SIMP_TAC[DROP_APPEND; ARITH_RULE `!n m. n <= m ==> n - m = 0`; DROP]);;

let DROP_APPEND2 = prove
 (`!(l1:A list) n.
     LENGTH l1 <= n ==> !l2. DROP n (APPEND l1 l2) = DROP (n - LENGTH l1) l2`,
  SIMP_TAC[DROP_APPEND; RICHAUX_DROP_LENGTH_TOO_LONG; APPEND]);;

let EL_DROP = prove
 (`!m n (l:A list). m + n < LENGTH l ==> EL m (DROP n l) = EL (m + n) l`,
  GEN_TAC THEN INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  ASM_SIMP_TAC[RICHAUX_DROP_CLAUSES; ADD_CLAUSES; LENGTH; LT_SUC; EL; TL;
               CONJUNCT1 LT]);;

let SNOC_APPEND = prove
 (`!(x:A) l. SNOC x l = APPEND l [x]`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[SNOC; APPEND]);;

let LENGTH_SNOC = prove
 (`!(x:A) l. LENGTH (SNOC x l) = SUC (LENGTH l)`,
  REWRITE_TAC[SNOC_APPEND; LENGTH_APPEND; LENGTH; ADD_CLAUSES]);;

let MAP_SNOC = prove
 (`!(f:A->B) x l. MAP f (SNOC x l) = SNOC (f x) (MAP f l)`,
  REWRITE_TAC[SNOC_APPEND; MAP_APPEND; MAP]);;

let EL_APPEND1 = prove
 (`!n (l1:A list) l2. n < LENGTH l1 ==> EL n (APPEND l1 l2) = EL n l1`,
  SIMP_TAC[EL_APPEND]);;

let EL_SNOC = prove
 (`!n (l:A list). n < LENGTH l ==> !x. EL n (SNOC x l) = EL n l`,
  SIMP_TAC[SNOC_APPEND; EL_APPEND1]);;

let EL_LENGTH_SNOC = prove
 (`!(l:A list) x. EL (LENGTH l) (SNOC x l) = x`,
  REWRITE_TAC[SNOC_APPEND; EL_APPEND; LT_REFL; SUB_REFL; EL; HD]);;

let REVERSE_SNOC = prove
 (`!(x:A) l. REVERSE (SNOC x l) = CONS x (REVERSE l)`,
  REWRITE_TAC[SNOC_APPEND; REVERSE_APPEND; REVERSE; APPEND]);;

let SNOC_INDUCT = prove
 (`!P:A list->bool. P [] /\ (!l. P l ==> !x. P (SNOC x l)) ==> !l. P l`,
  GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!l:A list. P (REVERSE l)`
    (fun th -> MESON_TAC[th; REVERSE_REVERSE]) THEN
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[REVERSE; GSYM SNOC_APPEND] THEN
  ASM_MESON_TAC[]);;

let SNOC_CASES = prove
 (`!l:A list. l = [] \/ ?x l'. l = SNOC x l'`,
  GEN_TAC THEN ASM_CASES_TAC `l:A list = []` THEN
  ASM_REWRITE_TAC[SNOC_APPEND] THEN ASM_MESON_TAC[APPEND_BUTLAST_LAST]);;

(* HOL4: MAP_REVERSE (HOL Light's MAP_REVERSE is the reversed equation) *)

let rich_list_MAP_REVERSE = prove
 (`!(f:A->B) l. MAP f (REVERSE l) = REVERSE (MAP f l)`,
  REWRITE_TAC[MAP_REVERSE]);;

let GENLIST = prove
 (`(!f:num->A. list_of_seq f 0 = []) /\
   (!(f:num->A) n. list_of_seq f (SUC n) = SNOC (f n) (list_of_seq f n))`,
  REWRITE_TAC[list_of_seq; SNOC_APPEND]);;

let LENGTH_GENLIST = LENGTH_LIST_OF_SEQ;;

let MAP_GENLIST = prove
 (`!(f:A->B) (g:num->A) n. MAP f (list_of_seq g n) = list_of_seq (f o g) n`,
  REWRITE_TAC[MAP_LIST_OF_SEQ]);;

let EL_GENLIST = prove
 (`!(f:num->A) n x. x < n ==> EL x (list_of_seq f n) = f x`,
  SIMP_TAC[EL_LIST_OF_SEQ]);;

let GENLIST_FUN_EQ = prove
 (`!n (f:num->A) g. list_of_seq f n = list_of_seq g n <=> !x. x < n ==> f x = g x`,
  SIMP_TAC[LIST_EQ; LENGTH_LIST_OF_SEQ; EL_LIST_OF_SEQ]);;

let GENLIST_APPEND = prove
 (`!(f:num->A) a b.
     list_of_seq f (a + b) =
     APPEND (list_of_seq f b) (list_of_seq (\t. f (t + b)) a)`,
  GEN_TAC THEN INDUCT_TAC THEN
  ASM_REWRITE_TAC[list_of_seq; ADD_CLAUSES; APPEND_NIL; APPEND_ASSOC]);;

let EVERY_GENLIST = prove
 (`!(P:A->bool) f n. ALL P (list_of_seq f n) <=> !i. i < n ==> P (f i)`,
  REWRITE_TAC[GSYM ALL_EL; LENGTH_LIST_OF_SEQ] THEN
  MESON_TAC[EL_LIST_OF_SEQ]);;

let RICHAUX_EL_ZIP = prove
 (`!(l1:A list) (l2:B list) n.
     LENGTH l1 = LENGTH l2 /\ n < LENGTH l1
     ==> EL n (ZIP l1 l2) = (EL n l1, EL n l2)`,
  LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[LENGTH; NOT_SUC; GSYM NOT_SUC; SUC_INJ; CONJUNCT1 LT; ZIP] THEN
  INDUCT_TAC THEN ASM_SIMP_TAC[EL; HD; TL; LT_SUC]);;

let ZIP_GENLIST = prove
 (`!(l:A list) (f:num->B) n.
     LENGTH l = n ==> ZIP l (list_of_seq f n) = list_of_seq (\x. (EL x l, f x)) n`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[LIST_EQ; LENGTH_LIST_OF_SEQ] THEN
  ASM_SIMP_TAC[LENGTH_ZIP; LENGTH_LIST_OF_SEQ; RICHAUX_EL_ZIP; EL_LIST_OF_SEQ]);;

let GENLIST_CONS = CONJUNCT2 LIST_OF_SEQ;;

let IS_PREFIX_NIL = prove
 (`!x:A list. [] <<= x /\ (x <<= [] <=> x = [])`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[RICHAUX_isPREFIX_THM; NOT_CONS_NIL]);;

let IS_PREFIX_REFL = prove
 (`!x:A list. x <<= x`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[RICHAUX_isPREFIX_THM]);;

let IS_PREFIX_APPEND = prove
 (`!l1 (l2:A list). l2 <<= l1 <=> ?l. l1 = APPEND l2 l`,
  ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[RICHAUX_isPREFIX_THM; APPEND] THENL
   [MESON_TAC[];
    LIST_INDUCT_TAC THEN
    ASM_REWRITE_TAC[RICHAUX_isPREFIX_THM; NOT_NIL_CONS; CONS_11] THEN
    MESON_TAC[]]);;

let IS_PREFIX_LENGTH = prove
 (`!x y:A list. x <<= y ==> LENGTH x <= LENGTH y`,
  REWRITE_TAC[IS_PREFIX_APPEND] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[LENGTH_APPEND] THEN ARITH_TAC);;

let IS_PREFIX_LENGTH_ANTI = prove
 (`!x y:A list. x <<= y /\ LENGTH x = LENGTH y <=> x = y`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [REWRITE_TAC[IS_PREFIX_APPEND] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `l:A list` ASSUME_TAC)
                               MP_TAC) THEN
    ASM_REWRITE_TAC[LENGTH_APPEND; ARITH_RULE `!a b. a = a + b <=> b = 0`;
                    LENGTH_EQ_NIL] THEN
    SIMP_TAC[APPEND_NIL];
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[IS_PREFIX_REFL]]);;

let IS_PREFIX_ANTISYM = prove
 (`!x y:A list. x <<= y /\ y <<= x ==> x = y`,
  MESON_TAC[IS_PREFIX_LENGTH; IS_PREFIX_LENGTH_ANTI; LE_ANTISYM]);;

let FOLDL_APPEND = prove
 (`!(f:B->A->B) e l1 l2. FOLDL f e (APPEND l1 l2) = FOLDL f (FOLDL f e l1) l2`,
  GEN_TAC THEN ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[FOLDL; APPEND]);;

let FOLDL_SNOC = prove
 (`!(f:B->A->B) e x l. FOLDL f e (SNOC x l) = f (FOLDL f e l) x`,
  REWRITE_TAC[SNOC_APPEND; FOLDL_APPEND; FOLDL]);;

let SUM_APPEND = prove
 (`!l1 l2. SUM (APPEND l1 l2) = SUM l1 + SUM l2`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[SUM; APPEND; ADD_CLAUSES; ADD_ASSOC]);;

let SUM_SNOC = prove
 (`!x l. SUM (SNOC x l) = SUM l + x`,
  REWRITE_TAC[SNOC_APPEND; SUM_APPEND; SUM; ADD_CLAUSES]);;

let EL_REVERSE = prove
 (`!n (l:A list).
     n < LENGTH l ==> EL n (REVERSE l) = EL (PRE (LENGTH l - n)) l`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[LENGTH; CONJUNCT1 LT] THEN
  REWRITE_TAC[REVERSE; EL_APPEND; LENGTH_REVERSE; LT_SUC_LE; LE_LT] THEN
  STRIP_TAC THENL
   [ASM_SIMP_TAC[] THEN
    SUBGOAL_THEN `PRE (SUC (LENGTH (t:A list)) - n) = SUC (PRE (LENGTH t - n))`
      SUBST1_TAC THENL [ASM_ARITH_TAC; REWRITE_TAC[EL; TL]];
    ASM_REWRITE_TAC[LT_REFL; SUB_REFL; EL; HD;
                    ARITH_RULE `!n. PRE (SUC n - n) = 0`]]);;

let EVERY2_APPEND_suff = prove
 (`!(R:A->B->bool) l1 l2 l3 l4.
     ALL2 R l1 l2 /\ ALL2 R l3 l4 ==> ALL2 R (APPEND l1 l3) (APPEND l2 l4)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[ALL2; APPEND] THEN ASM_MESON_TAC[]);;

let RICHAUX_ALL2_APPEND_EQ_LENGTH = prove
 (`!(R:A->B->bool) l1 l2 l3 l4.
     LENGTH l1 = LENGTH l2
     ==> (ALL2 R (APPEND l1 l3) (APPEND l2 l4) <=>
          ALL2 R l1 l2 /\ ALL2 R l3 l4)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  ASM_SIMP_TAC[LENGTH; APPEND; ALL2; NOT_SUC; GSYM NOT_SUC; SUC_INJ;
               CONJ_ASSOC]);;

let EVERY2_APPEND = prove
 (`!(R:A->B->bool) l1 l2 l3 l4.
     ALL2 R l1 l2 /\ ALL2 R l3 l4 <=>
     ALL2 R (APPEND l1 l3) (APPEND l2 l4) /\
     LENGTH l1 = LENGTH l2 /\ LENGTH l3 = LENGTH l4`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [MESON_TAC[EVERY2_APPEND_suff; RICHAUX_ALL2_LENGTH];
    STRIP_TAC THEN ASM_MESON_TAC[RICHAUX_ALL2_APPEND_EQ_LENGTH]]);;

(* ------------------------------------------------------------------------- *)
(* The theorems of rich_list (in rich_listScript order; helpers              *)
(* RICHAUX_... just before their use).                                       *)
(* ------------------------------------------------------------------------- *)

let SPLITP = SPLITP_DEF;;

let RICHAUX_SPLITP_JOIN = prove
 (`!(P:A->bool) ls. APPEND (FST (SPLITP P ls)) (SND (SPLITP P ls)) = ls`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[SPLITP_DEF; FST; SND; APPEND] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[FST; SND; APPEND]);;

let SPLITP_JOIN = prove
 (`!(P:A->bool) ls l r. SPLITP P ls = (l,r) ==> ls = APPEND l r`,
  REPEAT GEN_TAC THEN DISCH_THEN(fun th ->
    MP_TAC(SPECL [`P:A->bool`; `ls:A list`] RICHAUX_SPLITP_JOIN) THEN
    REWRITE_TAC[th; FST; SND]) THEN
  MESON_TAC[]);;

let RICHAUX_SPLITP_IMP = prove
 (`!(P:A->bool) ls.
     ALL ((~) o P) (FST (SPLITP P ls)) /\
     (~NULL (SND (SPLITP P ls)) ==> P (HD (SND (SPLITP P ls))))`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[SPLITP_DEF; ALL; NULL; FST; SND] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[ALL; NULL; HD; o_THM; FST; SND]);;

let SPLITP_IMP = prove
 (`!(P:A->bool) ls l r.
     SPLITP P ls = (l,r) ==> ALL ((~) o P) l /\ (~NULL r ==> P (HD r))`,
  REPEAT GEN_TAC THEN DISCH_THEN(fun th ->
    MP_TAC(SPECL [`P:A->bool`; `ls:A list`] RICHAUX_SPLITP_IMP) THEN
    REWRITE_TAC[th; FST; SND]));;

let SPLITP_LENGTH = prove
 (`!(P:A->bool) l.
     LENGTH (FST (SPLITP P l)) + LENGTH (SND (SPLITP P l)) = LENGTH l`,
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC (RAND_CONV o RAND_CONV)
    [GSYM(SPECL [`P:A->bool`; `l:A list`] RICHAUX_SPLITP_JOIN)] THEN
  REWRITE_TAC[LENGTH_APPEND]);;

let RICHAUX_SPLITP_SND_NIL = prove
 (`!(P:A->bool) ls. SND (SPLITP P ls) = [] <=> ALL ((~) o P) ls`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[SPLITP_DEF; ALL; SND] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[NOT_CONS_NIL; o_THM; SND]);;

let RICHAUX_SPLITP_FST_ALL = prove
 (`!(P:A->bool) ls. ALL ((~) o P) ls ==> FST (SPLITP P ls) = ls`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[SPLITP_DEF; ALL; FST; o_THM] THEN
  STRIP_TAC THEN ASM_SIMP_TAC[FST; CONS_11]);;

let SPLITP_NIL_SND_EVERY = prove
 (`!(P:A->bool) ls r. SPLITP P ls = (r,[]) <=> r = ls /\ ALL ((~) o P) ls`,
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [GSYM PAIR] THEN
  REWRITE_TAC[PAIR_EQ; RICHAUX_SPLITP_SND_NIL] THEN
  MESON_TAC[RICHAUX_SPLITP_FST_ALL]);;

let SPLITP_NIL_FST_IMP = prove
 (`!(P:A->bool) ls r. SPLITP P ls = ([],r) ==> r = ls`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[SPLITP_DEF; PAIR_EQ] THENL
   [MESON_TAC[];
    GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[PAIR_EQ; NOT_CONS_NIL] THEN
    MESON_TAC[]]);;

let SPLITL_def = new_definition
  `SPLITL (P:A->bool) = SPLITP ((~) o P)`;;

let COUNT_LIST_def = COUNT_LIST_DEF;;

let NOT_NULL_SNOC = prove
 (`!(x:A) l. ~NULL (SNOC x l)`,
  REWRITE_TAC[NULL_EQ_NIL; SNOC_APPEND; APPEND_EQ_NIL; NOT_CONS_NIL]);;

let SNOC_ACYCLIC = prove
 (`!(x:A) l. ~(l = SNOC x l) /\ ~(SNOC x l = l)`,
  REPEAT GEN_TAC THEN CONJ_TAC THEN
  DISCH_THEN(MP_TAC o AP_TERM `LENGTH:A list->num`) THEN
  REWRITE_TAC[LENGTH_SNOC] THEN ARITH_TAC);;

let LASTN_def = LASTN_DEF;;

let LASTN = prove
 (`(!l:A list. LASTN 0 l = []) /\
   (!n (x:A) l. LASTN (SUC n) (SNOC x l) = SNOC x (LASTN n l))`,
  REWRITE_TAC[LASTN_DEF; TAKE; REVERSE_SNOC; REVERSE; SNOC_APPEND]);;

let BUTLASTN_def = BUTLASTN_DEF;;

let BUTLASTN = prove
 (`(!l:A list. BUTLASTN 0 l = l) /\
   (!n (x:A) l. BUTLASTN (SUC n) (SNOC x l) = BUTLASTN n l)`,
  REWRITE_TAC[BUTLASTN_DEF; DROP; REVERSE_REVERSE; REVERSE_SNOC]);;

let RICHAUX_IS_SUBLIST_CONS = prove
 (`!(x1:A) l1 x2 l2.
      IS_SUBLIST (CONS x1 l1) (CONS x2 l2) <=>
      x1 = x2 /\ l2 <<= l1 \/ IS_SUBLIST l1 (CONS x2 l2)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IS_SUBLIST_DEF; IS_PREFIX_APPEND; APPEND] THEN
  EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `a:A list` MP_TAC) THEN
    STRUCT_CASES_TAC(ISPEC `a:A list` list_CASES) THEN
    REWRITE_TAC[APPEND; CONS_11] THEN MESON_TAC[];
    MESON_TAC[APPEND]]);;

let IS_SUBLIST = prove
 (`(!l:A list. IS_SUBLIST l [] <=> T) /\
   (!(x:A) l. IS_SUBLIST [] (CONS x l) <=> F) /\
   (!(x1:A) l1 x2 l2.
      IS_SUBLIST (CONS x1 l1) (CONS x2 l2) <=>
      x1 = x2 /\ l2 <<= l1 \/ IS_SUBLIST l1 (CONS x2 l2))`,
  REWRITE_TAC[RICHAUX_IS_SUBLIST_CONS] THEN
  REWRITE_TAC[IS_SUBLIST_DEF; APPEND] THEN CONJ_TAC THENL
   [MESON_TAC[APPEND];
    REWRITE_TAC[NOT_EXISTS_THM] THEN
    MESON_TAC[APPEND_EQ_NIL; NOT_CONS_NIL]]);;

let SEG = prove
 (`(!k (l:A list). SEG 0 k l = []) /\
   (!m (x:A) l. SEG (SUC m) 0 (CONS x l) = CONS x (SEG m 0 l)) /\
   (!m k (x:A) l. SEG (SUC m) (SUC k) (CONS x l) = SEG (SUC m) k l)`,
  REWRITE_TAC[SEG_DEF; TAKE; DROP]);;

let LENGTH_NOT_NULL = prove
 (`!l:A list. 0 < LENGTH l <=> ~NULL l`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[LENGTH; NULL; LT_REFL; LT_0]);;

let NOT_NIL_SNOC = prove
 (`!(x:A) l. ~([] = SNOC x l)`,
  REWRITE_TAC[SNOC_APPEND] THEN MESON_TAC[APPEND_EQ_NIL; NOT_CONS_NIL]);;

let NOT_SNOC_NIL = prove
 (`!(x:A) l. ~(SNOC x l = [])`,
  MESON_TAC[NOT_NIL_SNOC]);;

let FOLDR_SNOC = prove
 (`!(f:A->B->B) e x l. ITLIST f (SNOC x l) e = ITLIST f l (f x e)`,
  REWRITE_TAC[SNOC_APPEND; ITLIST_EXTRA]);;

let FILTER_SNOC = prove
 (`!P (x:A) l.
     FILTER P (SNOC x l) = if P x then SNOC x (FILTER P l) else FILTER P l`,
  REWRITE_TAC[SNOC_APPEND; FILTER_APPEND; FILTER] THEN
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[APPEND_NIL]);;

let LENGTH_FILTER_LEQ = LENGTH_FILTER;;

let LENGTH_SEG = prove
 (`!n k (l:A list). n + k <= LENGTH l ==> LENGTH (SEG n k l) = n`,
  SIMP_TAC[SEG_DEF; RICHAUX_LENGTH_TAKE_EQ; RICHAUX_LENGTH_DROP] THEN ARITH_TAC);;

(* HOL4: APPEND_NIL (HOL Light's APPEND_NIL is the first conjunct) *)

let rich_list_APPEND_NIL = prove
 (`(!l:A list. APPEND l [] = l) /\ (!l:A list. APPEND [] l = l)`,
  REWRITE_TAC[APPEND; APPEND_NIL]);;

let FOLDR_APPEND = ITLIST_APPEND;;

let CONS_APPEND = prove
 (`!(x:A) l. CONS x l = APPEND [x] l`,
  REWRITE_TAC[APPEND]);;

let FLAT_SNOC = prove
 (`!(x:A list) l. FLAT (SNOC x l) = APPEND (FLAT l) x`,
  REWRITE_TAC[SNOC_APPEND; FLAT_APPEND; FLAT; APPEND_NIL]);;

let LENGTH_FLAT = prove
 (`!l:(A list) list. LENGTH (FLAT l) = SUM (MAP LENGTH l)`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[FLAT; MAP; SUM; LENGTH; LENGTH_APPEND]);;

let ALL_EL_MAP = ALL_MAP;;

(* HOL4: IS_PREFIX (the clauses of isPREFIX in IS_PREFIX form) *)

let IS_PREFIX = prove
 (`(!l:A list. [] <<= l <=> T) /\
   (!(x:A) l. CONS x l <<= [] <=> F) /\
   (!(x1:A) l1 x2 l2. CONS x2 l2 <<= CONS x1 l1 <=> x1 = x2 /\ l2 <<= l1)`,
  REWRITE_TAC[RICHAUX_isPREFIX_THM] THEN MESON_TAC[]);;

let IS_SUFFIX_APPEND = prove
 (`!(l1:A list) l2. IS_SUFFIX l1 l2 <=> ?l. l1 = APPEND l l2`,
  REWRITE_TAC[IS_SUFFIX_DEF; IS_PREFIX_APPEND] THEN REPEAT GEN_TAC THEN
  EQ_TAC THEN DISCH_THEN(X_CHOOSE_TAC `l:A list`) THEN
  EXISTS_TAC `REVERSE (l:A list)` THENL
   [FIRST_ASSUM(MP_TAC o AP_TERM `REVERSE:A list->A list`) THEN
    REWRITE_TAC[REVERSE_REVERSE; REVERSE_APPEND];
    ASM_REWRITE_TAC[REVERSE_APPEND]]);;

let IS_SUBLIST_APPEND = prove
 (`!(l1:A list) l2. IS_SUBLIST l1 l2 <=> ?l l'. l1 = APPEND l (APPEND l2 l')`,
  REWRITE_TAC[IS_SUBLIST_DEF]);;

let IS_PREFIX_IS_SUBLIST = prove
 (`!(l1:A list) l2. l2 <<= l1 ==> IS_SUBLIST l1 l2`,
  REWRITE_TAC[IS_PREFIX_APPEND; IS_SUBLIST_DEF] THEN MESON_TAC[APPEND]);;

let IS_SUFFIX_CONS = prove
 (`!(l1:A list) l2 a. IS_SUFFIX l1 l2 ==> IS_SUFFIX (CONS a l1) l2`,
  REWRITE_TAC[IS_SUFFIX_APPEND] THEN MESON_TAC[APPEND]);;

let IS_SUFFIX_TRANS = prove
 (`!(l1:A list) l2 l3. IS_SUFFIX l1 l2 /\ IS_SUFFIX l2 l3 ==> IS_SUFFIX l1 l3`,
  REWRITE_TAC[IS_SUFFIX_APPEND] THEN MESON_TAC[APPEND_ASSOC]);;

let IS_SUFFIX_REFL = prove
 (`!l:A list. IS_SUFFIX l l`,
  REWRITE_TAC[IS_SUFFIX_DEF; IS_PREFIX_REFL]);;

let FOLDR_REVERSE = prove
 (`!(f:A->B->B) e l. ITLIST f (REVERSE l) e = FOLDL (\x y. f y x) e l`,
  GEN_TAC THEN ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[REVERSE; ITLIST; FOLDL; ITLIST_APPEND]);;

let FOLDR_FOLDL_REVERSE = prove
 (`!(f:A->B->B) e l. ITLIST f l e = FOLDL (\x y. f y x) e (REVERSE l)`,
  REWRITE_TAC[GSYM FOLDR_REVERSE; REVERSE_REVERSE]);;

let FOLDL_FOLDR_REVERSE = prove
 (`!(f:B->A->B) e l. FOLDL f e l = ITLIST (\x y. f y x) (REVERSE l) e`,
  REWRITE_TAC[FOLDR_REVERSE] THEN REWRITE_TAC[ETA_AX]);;

let FOLDR_MAP = prove
 (`!(f:B->C->C) e (g:A->B) l.
     ITLIST f (MAP g l) e = ITLIST (\x y. f (g x) y) l e`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[ITLIST; MAP]);;

(* HOL4: ASSOC_FOLDR_FLAT, with operator ASSOC f and LEFT_ID f e written out *)

(* (HOL Light's ASSOC is association-list lookup)                           *)

let RICHAUX_ITLIST_ASSOC_LEFT_ID = prove
 (`!(f:A->A->A) e.
     (!x y z. f x (f y z) = f (f x y) z) /\ (!x. f e x = x)
     ==> !l b. ITLIST f l b = f (ITLIST f l e) b`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN LIST_INDUCT_TAC THENL
   [ASM_REWRITE_TAC[ITLIST];
    REWRITE_TAC[ITLIST] THEN GEN_TAC THEN
    FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [th]) THEN
    ASM_REWRITE_TAC[]]);;

let ASSOC_FOLDR_FLAT = prove
 (`!f:A->A->A.
     (!x y z. f x (f y z) = f (f x y) z)
     ==> !e. (!x. f e x = x)
             ==> !l. ITLIST f (FLAT l) e = ITLIST f (MAP (\l. ITLIST f l e) l) e`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN DISCH_TAC THEN
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[FLAT; MAP; ITLIST; ITLIST_APPEND] THEN
  ASM_MESON_TAC[RICHAUX_ITLIST_ASSOC_LEFT_ID]);;

let MAP_FLAT = prove
 (`!(f:A->B) l. MAP f (FLAT l) = FLAT (MAP (MAP f) l)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[FLAT; MAP; MAP_APPEND]);;

let SEG_LENGTH_ID = prove
 (`!l:A list. SEG (LENGTH l) 0 l = l`,
  REWRITE_TAC[SEG_DEF; DROP; RICHAUX_TAKE_LENGTH_ID]);;

let TAKE_APPEND1 = prove
 (`!n (l1:A list). n <= LENGTH l1 ==> !l2. TAKE n (APPEND l1 l2) = TAKE n l1`,
  ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[LENGTH; APPEND] THENL
   [SIMP_TAC[ARITH_RULE `n <= 0 <=> n = 0`; TAKE];
    INDUCT_TAC THEN ASM_SIMP_TAC[TAKE; LE_SUC]]);;

let SEG_0_SNOC = prove
 (`!m (l:A list) x. m <= LENGTH l ==> SEG m 0 (SNOC x l) = SEG m 0 l`,
  SIMP_TAC[SEG_DEF; DROP; SNOC_APPEND; TAKE_APPEND1]);;

let LASTN_CONS = prove
 (`!n (l:A list). n <= LENGTH l ==> !x. LASTN n (CONS x l) = LASTN n l`,
  SIMP_TAC[LASTN_DEF; REVERSE; TAKE_APPEND1; LENGTH_REVERSE]);;

let LENGTH_LASTN = prove
 (`!n (l:A list). n <= LENGTH l ==> LENGTH (LASTN n l) = n`,
  SIMP_TAC[LASTN_DEF; LENGTH_REVERSE; RICHAUX_LENGTH_TAKE]);;

let LASTN_LENGTH_ID = prove
 (`!l:A list. LASTN (LENGTH l) l = l`,
  SIMP_TAC[LASTN_DEF; RICHAUX_TAKE_LENGTH_TOO_LONG; LENGTH_REVERSE; LE_REFL;
           REVERSE_REVERSE]);;

let TAKE_EL_SNOC = prove
 (`!(ls:A list) n.
     n < LENGTH ls ==> TAKE (n + 1) ls = SNOC (EL n ls) (TAKE n ls)`,
  REWRITE_TAC[GSYM ADD1] THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[LENGTH; CONJUNCT1 LT] THEN
  INDUCT_TAC THEN
  ASM_SIMP_TAC[TAKE; SNOC; EL; HD; TL; LT_SUC; RICHAUX_TAKE_CLAUSES]);;

let SNOC_EL_TAKE = prove
 (`!n (l:A list). n < LENGTH l ==> SNOC (EL n l) (TAKE n l) = TAKE (SUC n) l`,
  MESON_TAC[TAKE_EL_SNOC; ADD1]);;

let APPEND_BUTLASTN_LASTN = prove
 (`!n (l:A list). n <= LENGTH l ==> APPEND (BUTLASTN n l) (LASTN n l) = l`,
  REWRITE_TAC[BUTLASTN_DEF; LASTN_DEF; GSYM REVERSE_APPEND; RICHAUX_TAKE_DROP;
              REVERSE_REVERSE]);;

let TAKE_LENGTH_APPEND = prove
 (`!(l1:A list) l2. TAKE (LENGTH l1) (APPEND l1 l2) = l1`,
  SIMP_TAC[TAKE_APPEND1; LE_REFL; RICHAUX_TAKE_LENGTH_ID]);;

let LASTN_LENGTH_APPEND = prove
 (`!(l2:A list) l1. LASTN (LENGTH l2) (APPEND l1 l2) = l2`,
  REWRITE_TAC[LASTN_DEF; REVERSE_APPEND] THEN
  ONCE_REWRITE_TAC[GSYM LENGTH_REVERSE] THEN
  REWRITE_TAC[TAKE_LENGTH_APPEND; REVERSE_REVERSE]);;

let TAKE_TAKE_T = prove
 (`!m (l:A list) n. n <= m ==> TAKE n (TAKE m l) = TAKE n l`,
  INDUCT_TAC THENL
   [SIMP_TAC[ARITH_RULE `n <= 0 <=> n = 0`; TAKE];
    LIST_INDUCT_TAC THEN REWRITE_TAC[RICHAUX_TAKE_CLAUSES] THEN
    INDUCT_TAC THEN ASM_SIMP_TAC[RICHAUX_TAKE_CLAUSES; LE_SUC]]);;

let TAKE_TAKE = prove
 (`!m (l:A list). m <= LENGTH l ==> !n. n <= m ==> TAKE n (TAKE m l) = TAKE n l`,
  SIMP_TAC[TAKE_TAKE_T]);;

let DROP_DROP_T = prove
 (`!n m (l:A list). DROP n (DROP m l) = DROP (n + m) l`,
  GEN_TAC THEN INDUCT_TAC THEN REWRITE_TAC[DROP; ADD_CLAUSES] THEN
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[RICHAUX_DROP_CLAUSES]);;

let DROP_DROP = prove
 (`!n m (l:A list). n + m <= LENGTH l ==> DROP n (DROP m l) = DROP (n + m) l`,
  REWRITE_TAC[DROP_DROP_T]);;

let TAKE_SEG = prove
 (`!n (l:A list). n <= LENGTH l ==> TAKE n l = SEG n 0 l`,
  REWRITE_TAC[SEG_DEF; DROP]);;

let DROP_SEG = prove
 (`!n (l:A list). n <= LENGTH l ==> DROP n l = SEG (LENGTH l - n) n l`,
  SIMP_TAC[SEG_DEF; RICHAUX_TAKE_LENGTH_TOO_LONG; RICHAUX_LENGTH_DROP; LE_REFL]);;

let SEG_APPEND1 = prove
 (`!n m (l1:A list).
     n + m <= LENGTH l1 ==> !l2. SEG n m (APPEND l1 l2) = SEG n m l1`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[SEG_DEF] THEN
  SUBGOAL_THEN `m <= LENGTH (l1:A list) /\ n <= LENGTH (DROP m l1)`
    STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[RICHAUX_LENGTH_DROP] THEN ASM_ARITH_TAC;
    ASM_SIMP_TAC[DROP_APPEND1; TAKE_APPEND1]]);;

let SEG_APPEND2 = prove
 (`!(l1:A list) m n l2.
     LENGTH l1 <= m /\ n <= LENGTH l2
     ==> SEG n m (APPEND l1 l2) = SEG n (m - LENGTH l1) l2`,
  SIMP_TAC[SEG_DEF; DROP_APPEND2]);;

let SEG_TAKE_DROP = prove
 (`!n m (l:A list). n + m <= LENGTH l ==> SEG n m l = TAKE n (DROP m l)`,
  REWRITE_TAC[SEG_DEF]);;

let FILTER_FILTER = prove
 (`!P Q (l:A list). FILTER P (FILTER Q l) = FILTER (\x. P x /\ Q x) l`,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[FILTER] THEN
  ASM_CASES_TAC `(Q:A->bool) h` THEN ASM_REWRITE_TAC[FILTER]);;

let EL_LENGTH_APPEND = prove
 (`!(l2:A list) l1. ~NULL l2 ==> EL (LENGTH l1) (APPEND l1 l2) = HD l2`,
  REWRITE_TAC[EL_APPEND; LT_REFL; SUB_REFL; EL]);;

let LENGTH_FRONT = prove
 (`!l:A list. ~(l = []) ==> LENGTH (BUTLAST l) = PRE (LENGTH l)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[NOT_CONS_NIL; BUTLAST; LENGTH] THEN
  COND_CASES_TAC THEN ASM_SIMP_TAC[LENGTH; PRE] THEN
  ASM_MESON_TAC[LENGTH_EQ_NIL; ARITH_RULE `~(n = 0) ==> SUC (PRE n) = n`]);;

let DROP_LENGTH_APPEND = prove
 (`!(l1:A list) l2. DROP (LENGTH l1) (APPEND l1 l2) = l2`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[LENGTH; APPEND; DROP]);;

let TAKE_APPEND = prove
 (`!n (l1:A list) l2.
     TAKE n (APPEND l1 l2) = APPEND (TAKE n l1) (TAKE (n - LENGTH l1) l2)`,
  ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[APPEND; LENGTH; SUB_0; RICHAUX_TAKE_CLAUSES] THEN
  INDUCT_TAC THEN
  ASM_REWRITE_TAC[RICHAUX_TAKE_CLAUSES; SUB_0; SUB_SUC; APPEND]);;

let TAKE_APPEND2 = prove
 (`!(l1:A list) n.
     LENGTH l1 <= n
     ==> !l2. TAKE n (APPEND l1 l2) = APPEND l1 (TAKE (n - LENGTH l1) l2)`,
  SIMP_TAC[TAKE_APPEND; RICHAUX_TAKE_LENGTH_TOO_LONG]);;

let MAP_FILTER = prove
 (`!(f:A->A) P l.
     (!x. P (f x) <=> P x) ==> MAP f (FILTER P l) = FILTER P (MAP f l)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN SPEC_TAC(`l:A list`,`l:A list`) THEN
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[FILTER; MAP] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[MAP]);;

let EXISTS_REVERSE = prove
 (`!(P:A->bool) l. EX P (REVERSE l) <=> EX P l`,
  REWRITE_TAC[GSYM EX_MEM; RICHAUX_MEM_REVERSE]);;

let MEM_TAKE = prove
 (`!(l:A list) m x. MEM x (TAKE m l) ==> MEM x l`,
  LIST_INDUCT_TAC THEN INDUCT_TAC THEN
  REWRITE_TAC[RICHAUX_TAKE_CLAUSES; MEM] THEN ASM_MESON_TAC[]);;

let MEM_DROP_IMP = prove
 (`!(l:A list) m x. MEM x (DROP m l) ==> MEM x l`,
  LIST_INDUCT_TAC THEN INDUCT_TAC THEN
  REWRITE_TAC[RICHAUX_DROP_CLAUSES; MEM] THEN ASM_MESON_TAC[]);;

let MEM_LASTN = prove
 (`!m (l:A list) x. MEM x (LASTN m l) ==> MEM x l`,
  REWRITE_TAC[LASTN_DEF; RICHAUX_MEM_REVERSE] THEN
  MESON_TAC[MEM_TAKE; RICHAUX_MEM_REVERSE]);;

let EVERY_TAKE = prove
 (`!(P:A->bool) l m. ALL P l ==> ALL P (TAKE m l)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN INDUCT_TAC THEN
  ASM_SIMP_TAC[RICHAUX_TAKE_CLAUSES; ALL]);;

let EVERY_DROP = prove
 (`!(P:A->bool) l m. ALL P l ==> ALL P (DROP m l)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN INDUCT_TAC THEN
  ASM_SIMP_TAC[RICHAUX_DROP_CLAUSES; ALL]);;

let EVERY_REVERSE = prove
 (`!(P:A->bool) l. ALL P (REVERSE l) <=> ALL P l`,
  REWRITE_TAC[GSYM ALL_MEM; RICHAUX_MEM_REVERSE]);;

let ZIP_APPEND = prove
 (`!(a:A list) (b:B list) c d.
     LENGTH a = LENGTH b /\ LENGTH c = LENGTH d
     ==> APPEND (ZIP a b) (ZIP c d) = ZIP (APPEND a c) (APPEND b d)`,
  LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  ASM_SIMP_TAC[LENGTH; APPEND; ZIP; NOT_SUC; GSYM NOT_SUC; SUC_INJ]);;

let ZIP_SNOC = prove
 (`!(l1:A list) (l2:B list).
     LENGTH l1 = LENGTH l2
     ==> !x1 x2. ZIP (SNOC x1 l1) (SNOC x2 l2) = SNOC (x1,x2) (ZIP l1 l2)`,
  SIMP_TAC[SNOC_APPEND; GSYM ZIP_APPEND; LENGTH; ZIP]);;

let SUM_REVERSE = prove
 (`!l. SUM (REVERSE l) = SUM l`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[REVERSE; SUM; SUM_APPEND] THEN
  ARITH_TAC);;

let EL_APPEND2 = prove
 (`!(l1:A list) n.
     LENGTH l1 <= n ==> !l2. EL n (APPEND l1 l2) = EL (n - LENGTH l1) l2`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[EL_APPEND; GSYM NOT_LE]);;

let RICHAUX_LUPDATE_CLAUSES = prove
 (`(!(e:A) n. LUPDATE e n [] = []) /\
   (!(e:A) x l. LUPDATE e 0 (CONS x l) = CONS e l) /\
   (!(e:A) n x l. LUPDATE e (SUC n) (CONS x l) = CONS x (LUPDATE e n l))`,
  REWRITE_TAC[LUPDATE_DEF; NOT_SUC; SUC_SUB1]);;

let LUPDATE_APPEND2 = prove
 (`!(l1:A list) l2 n x.
     LENGTH l1 <= n
     ==> LUPDATE x n (APPEND l1 l2) = APPEND l1 (LUPDATE x (n - LENGTH l1) l2)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[APPEND; LENGTH; SUB_0] THEN
  GEN_TAC THEN INDUCT_TAC THEN
  ASM_SIMP_TAC[RICHAUX_LUPDATE_CLAUSES; LE_SUC; SUB_SUC; LE; NOT_SUC]);;

let LUPDATE_APPEND1 = prove
 (`!(l1:A list) l2 n x.
     n < LENGTH l1
     ==> LUPDATE x n (APPEND l1 l2) = APPEND (LUPDATE x n l1) l2`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[APPEND; LENGTH; CONJUNCT1 LT] THEN
  GEN_TAC THEN INDUCT_TAC THEN
  ASM_SIMP_TAC[RICHAUX_LUPDATE_CLAUSES; LT_SUC; APPEND]);;

let is_prefix_el = prove
 (`!n (l1:A list) l2.
     l1 <<= l2 /\ n < LENGTH l1 /\ n < LENGTH l2 ==> EL n l1 = EL n l2`,
  REWRITE_TAC[IS_PREFIX_APPEND] THEN REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[EL_APPEND1]);;

(* HOL4: EL_CONS (HOL Light's EL_CONS is unconditional, with n - 1) *)

let rich_list_EL_CONS = prove
 (`!n. 0 < n ==> !(x:A) l. EL n (CONS x l) = EL (PRE n) l`,
  INDUCT_TAC THEN REWRITE_TAC[LT_REFL; EL; TL; PRE]);;

let DROP_EL_CONS = prove
 (`!(ls:A list) n.
     n < LENGTH ls ==> DROP n ls = CONS (EL n ls) (DROP (n + 1) ls)`,
  REWRITE_TAC[GSYM ADD1] THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[LENGTH; CONJUNCT1 LT] THEN
  INDUCT_TAC THEN ASM_SIMP_TAC[RICHAUX_DROP_CLAUSES; EL; HD; TL; LT_SUC]);;

let DROP_CONS_EL = prove
 (`!n (l:A list).
     n < LENGTH l ==> DROP n l = CONS (EL n l) (DROP (SUC n) l)`,
  MESON_TAC[DROP_EL_CONS; ADD1]);;

let SEG1 = prove
 (`!n (l:A list). n < LENGTH l ==> SEG 1 n l = [EL n l]`,
  SIMP_TAC[SEG_DEF; DROP_CONS_EL; ONE; TAKE]);;

let SEG_SUC_EL = prove
 (`!n i (l:A list).
     i + n < LENGTH l ==> SEG (SUC n) i l = CONS (EL i l) (SEG n (i + 1) l)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[SEG_DEF; GSYM ADD1] THEN
  SUBGOAL_THEN `i < LENGTH (l:A list)` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ASM_SIMP_TAC[DROP_CONS_EL; TAKE]]);;

let TAKE_SEG_DROP = prove
 (`!n i (l:A list).
     i + n <= LENGTH l
     ==> APPEND (APPEND (TAKE i l) (SEG n i l)) (DROP (i + n) l) = l`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[SEG_DEF; GSYM APPEND_ASSOC] THEN
  ONCE_REWRITE_TAC[ADD_SYM] THEN
  REWRITE_TAC[GSYM DROP_DROP_T; RICHAUX_TAKE_DROP]);;

let LASTN_DROP_UNCOND = prove
 (`!n (l:A list). LASTN n l = DROP (LENGTH l - n) l`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[LASTN_DEF; REVERSE; RICHAUX_TAKE_NIL; RICHAUX_DROP_NIL] THEN
  REWRITE_TAC[TAKE_APPEND; REVERSE_APPEND; LENGTH_REVERSE; LENGTH] THEN
  ASM_CASES_TAC `n <= LENGTH (t:A list)` THENL
   [SUBGOAL_THEN
     `n - LENGTH (t:A list) = 0 /\ SUC (LENGTH t) - n = SUC (LENGTH t - n)`
      (fun th -> REWRITE_TAC[th]) THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[TAKE; REVERSE; APPEND; DROP; GSYM LASTN_DEF];
    SUBGOAL_THEN
     `n - LENGTH (t:A list) = SUC (n - SUC (LENGTH t)) /\
      SUC (LENGTH t) - n = 0 /\ LENGTH t <= n`
      STRIP_ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[RICHAUX_TAKE_LENGTH_TOO_LONG; LENGTH_REVERSE] THEN
    REWRITE_TAC[RICHAUX_TAKE_CLAUSES; REVERSE; APPEND; DROP;
                REVERSE_REVERSE]]);;

let LASTN_DROP = prove
 (`!n (l:A list). n <= LENGTH l ==> LASTN n l = DROP (LENGTH l - n) l`,
  REWRITE_TAC[LASTN_DROP_UNCOND]);;

let BUTLASTN_TAKE = prove
 (`!n (l:A list). n <= LENGTH l ==> BUTLASTN n l = TAKE (LENGTH l - n) l`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[BUTLASTN_DEF] THEN
  MP_TAC(ISPECL [`LENGTH (l:A list) - n`; `REVERSE (l:A list)`] LASTN_DROP) THEN
  REWRITE_TAC[LENGTH_REVERSE; ARITH_RULE `!m n:num. m - n <= m`] THEN
  ASM_SIMP_TAC[ARITH_RULE `!m n:num. n <= m ==> m - (m - n) = n`] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[LASTN_DEF; REVERSE_REVERSE]);;

let DROP_REVERSE = prove
 (`!n (l:A list). n <= LENGTH l ==> DROP n (REVERSE l) = REVERSE (BUTLASTN n l)`,
  REWRITE_TAC[BUTLASTN_DEF; REVERSE_REVERSE]);;

let TAKE_REVERSE = prove
 (`!n (l:A list). n <= LENGTH l ==> TAKE n (REVERSE l) = REVERSE (LASTN n l)`,
  REWRITE_TAC[LASTN_DEF; REVERSE_REVERSE]);;

(* HOL4: MEM_REPLICATE (HOL Light's MEM_REPLICATE has ~(n = 0)) *)

let rich_list_MEM_REPLICATE = prove
 (`!n (x:A) y. MEM y (REPLICATE n x) <=> x = y /\ 0 < n`,
  REWRITE_TAC[MEM_REPLICATE; LT_NZ] THEN MESON_TAC[]);;

let RICHAUX_isPREFIX_TRANS = prove
 (`!(z:A list) y x. z <<= y /\ y <<= x ==> z <<= x`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[RICHAUX_isPREFIX_THM] THEN
  LIST_INDUCT_TAC THEN REWRITE_TAC[RICHAUX_isPREFIX_THM] THEN
  LIST_INDUCT_TAC THEN REWRITE_TAC[RICHAUX_isPREFIX_THM] THEN
  ASM_MESON_TAC[]);;

(* HOL4: IS_PREFIX x y is isPREFIX y x (an overload with swapped arguments) *)

let IS_PREFIX_TRANS = prove
 (`!x y z:A list. y <<= x /\ z <<= y ==> z <<= x`,
  MESON_TAC[RICHAUX_isPREFIX_TRANS]);;

let IS_PREFIX_BUTLAST = prove
 (`!(x:A) y. BUTLAST (CONS x y) <<= CONS x y`,
  MESON_TAC[IS_PREFIX_APPEND; APPEND_BUTLAST_LAST; NOT_CONS_NIL]);;

let IS_PREFIX_APPEND1 = prove
 (`!(a:A list) b c. APPEND a b <<= c ==> a <<= c`,
  REWRITE_TAC[IS_PREFIX_APPEND] THEN MESON_TAC[APPEND_ASSOC]);;

let IS_PREFIX_APPENDS = prove
 (`!(a:A list) b c. APPEND a b <<= APPEND a c <=> b <<= c`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[APPEND; RICHAUX_isPREFIX_THM]);;

let IS_PREFIX_APPEND3 = prove
 (`!(c:A list) a. a <<= APPEND a c`,
  REWRITE_TAC[IS_PREFIX_APPEND] THEN MESON_TAC[]);;

let COUNT_LIST_GENLIST = prove
 (`!n. COUNT_LIST n = list_of_seq I n`,
  INDUCT_TAC THEN
  ASM_REWRITE_TAC[COUNT_LIST_DEF; LIST_OF_SEQ; MAP_LIST_OF_SEQ; I_O_ID; I_THM]);;

let LENGTH_COUNT_LIST = prove
 (`!n. LENGTH (COUNT_LIST n) = n`,
  REWRITE_TAC[COUNT_LIST_GENLIST; LENGTH_LIST_OF_SEQ]);;

let EL_COUNT_LIST = prove
 (`!m n. m < n ==> EL m (COUNT_LIST n) = m`,
  SIMP_TAC[COUNT_LIST_GENLIST; EL_LIST_OF_SEQ; I_THM]);;

let MEM_COUNT_LIST = prove
 (`!m n. MEM m (COUNT_LIST n) <=> m < n`,
  REWRITE_TAC[COUNT_LIST_GENLIST; MEM_EXISTS_EL; LENGTH_LIST_OF_SEQ] THEN
  MESON_TAC[EL_LIST_OF_SEQ; I_THM]);;

let COUNT_LIST_SNOC = prove
 (`(COUNT_LIST 0 = []) /\ (!n. COUNT_LIST (SUC n) = SNOC n (COUNT_LIST n))`,
  REWRITE_TAC[COUNT_LIST_GENLIST; GENLIST; I_THM]);;

let COUNT_LIST_COUNT = prove
 (`!n. set_of_list (COUNT_LIST n) = count n`,
  REWRITE_TAC[EXTENSION; IN_SET_OF_LIST; MEM_COUNT_LIST; count_DEF;
              IN_ELIM_THM]);;

let COUNT_LIST_ADD = prove
 (`!n m. COUNT_LIST (n + m) =
         APPEND (COUNT_LIST n) (MAP (\n'. n' + n) (COUNT_LIST m))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[COUNT_LIST_GENLIST; MAP_LIST_OF_SEQ] THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [ADD_SYM] THEN
  REWRITE_TAC[GENLIST_APPEND] THEN
  AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; o_THM; I_THM]);;

let MAP_COUNT_LIST = prove
 (`!(f:num->A) n. MAP f (COUNT_LIST n) = list_of_seq f n`,
  REWRITE_TAC[COUNT_LIST_GENLIST; MAP_LIST_OF_SEQ; I_O_ID]);;

let SUM_IMAGE_count_SUM_GENLIST = prove
 (`!(f:num->num) n. SUM_IMAGE f (count n) = SUM (list_of_seq f n)`,
  GEN_TAC THEN REWRITE_TAC[SUM_IMAGE_DEF; count_DEF] THEN INDUCT_TAC THENL
   [REWRITE_TAC[CONJUNCT1 LT; EMPTY_GSPEC; NSUM_CLAUSES; list_of_seq; SUM];
    SUBGOAL_THEN `{m | m < SUC n} = n INSERT {m | m < n}` SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_INSERT; IN_ELIM_THM] THEN ARITH_TAC;
      ALL_TAC] THEN
    SIMP_TAC[NSUM_CLAUSES; FINITE_NUMSEG_LT; IN_ELIM_THM; LT_REFL] THEN
    ASM_REWRITE_TAC[list_of_seq; SUM_APPEND; SUM] THEN ARITH_TAC]);;

let APPEND_ASSOC_CONS = prove
 (`!(l1:A list) h l2 l3.
     APPEND (APPEND l1 (CONS h l2)) l3 = APPEND l1 (CONS h (APPEND l2 l3))`,
  REWRITE_TAC[GSYM APPEND_ASSOC; APPEND]);;

let MEM_FRONT_NOT_NIL = prove
 (`!(l:A list) y. ~(l = []) /\ MEM y (BUTLAST l) ==> MEM y l`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(fun th -> GEN_REWRITE_TAC RAND_CONV
    [GSYM(MATCH_MP APPEND_BUTLAST_LAST th)]) THEN
  ASM_REWRITE_TAC[MEM_APPEND]);;

let MEM_FRONT = prove
 (`!(l:A list) e y. MEM y (BUTLAST (CONS e l)) ==> MEM y (CONS e l)`,
  MESON_TAC[MEM_FRONT_NOT_NIL; NOT_CONS_NIL]);;

let FRONT_APPEND = prove
 (`!(l1:A list) l2 e.
     BUTLAST (APPEND l1 (CONS e l2)) = APPEND l1 (BUTLAST (CONS e l2))`,
  REWRITE_TAC[BUTLAST_APPEND; NOT_CONS_NIL]);;

let MEM_LAST_NOT_NIL = prove
 (`!(e:A) (l:A list). ~(l = []) ==> MEM (LAST l) l`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(fun th -> GEN_REWRITE_TAC RAND_CONV
    [GSYM(MATCH_MP APPEND_BUTLAST_LAST th)]) THEN
  REWRITE_TAC[MEM_APPEND; MEM]);;

let MEM_LAST = prove
 (`!(e:A) l. MEM (LAST (CONS e l)) (CONS e l)`,
  MESON_TAC[MEM_LAST_NOT_NIL; NOT_CONS_NIL]);;

let LIST_ELEM_COUNT_THM = prove
 (`(!e:A. LIST_ELEM_COUNT e [] = 0) /\
   (!(e:A) l1 l2.
      LIST_ELEM_COUNT e (APPEND l1 l2) =
      LIST_ELEM_COUNT e l1 + LIST_ELEM_COUNT e l2) /\
   (!(e:A) h l.
      h = e ==> LIST_ELEM_COUNT e (CONS h l) = SUC (LIST_ELEM_COUNT e l)) /\
   (!(e:A) h l.
      ~(h = e) ==> LIST_ELEM_COUNT e (CONS h l) = LIST_ELEM_COUNT e l)`,
  REWRITE_TAC[LIST_ELEM_COUNT_DEF; FILTER; FILTER_APPEND; LENGTH;
              LENGTH_APPEND] THEN
  SIMP_TAC[LENGTH]);;

let EL_REPLICATE = prove
 (`!n1 n2 (x:A). n1 < n2 ==> EL n1 (REPLICATE n2 x) = x`,
  MESON_TAC[MEM_EL; MEM_REPLICATE; LENGTH_REPLICATE]);;

let REPLICATE_GENLIST = prove
 (`!n (x:A). REPLICATE n x = list_of_seq (K x) n`,
  REWRITE_TAC[LIST_EQ; LENGTH_REPLICATE; LENGTH_LIST_OF_SEQ] THEN
  SIMP_TAC[EL_REPLICATE; EL_LIST_OF_SEQ; K_THM]);;

let EVERY_REPLICATE = prove
 (`!(f:A->bool) n x. ALL f (REPLICATE n x) <=> n = 0 \/ f x`,
  GEN_TAC THEN INDUCT_TAC THEN ASM_REWRITE_TAC[REPLICATE; ALL; NOT_SUC] THEN
  MESON_TAC[]);;

let DROP_LENGTH_NIL_rwt = prove
 (`!(l:A list) m. m = LENGTH l ==> DROP m l = []`,
  SIMP_TAC[DROP_LENGTH_NIL]);;

let LENGTH_FILTER_LESS = prove
 (`!(P:A->bool) ls. EX ((~) o P) ls ==> LENGTH (FILTER P ls) < LENGTH ls`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[EX; FILTER; o_THM] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[LENGTH; LT_SUC] THEN
  ASM_MESON_TAC[LENGTH_FILTER; LT_SUC_LE]);;

let EVERY2_DROP = prove
 (`!(R:A->B->bool) l1 l2 n.
     ALL2 R l1 l2 ==> ALL2 R (DROP n l1) (DROP n l2)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[ALL2; RICHAUX_DROP_CLAUSES] THEN
  INDUCT_TAC THEN REWRITE_TAC[ALL2; RICHAUX_DROP_CLAUSES] THEN
  ASM_MESON_TAC[]);;

let EVERY2_TAKE = prove
 (`!(P:A->B->bool) xs ys n.
     ALL2 P xs ys ==> ALL2 P (TAKE n xs) (TAKE n ys)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[ALL2; RICHAUX_TAKE_CLAUSES] THEN
  INDUCT_TAC THEN REWRITE_TAC[ALL2; RICHAUX_TAKE_CLAUSES] THEN
  ASM_MESON_TAC[]);;

let RICHAUX_ALL2_NIL = prove
 (`(!(P:A->B->bool) l. ALL2 P [] l <=> l = []) /\
   (!(P:A->B->bool) l. ALL2 P l [] <=> l = [])`,
  CONJ_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[ALL2; NOT_CONS_NIL]);;

let LIST_REL_APPEND_SING = prove
 (`!(R:A->B->bool) l1 l2 x1 x2.
     ALL2 R (APPEND l1 [x1]) (APPEND l2 [x2]) <=> ALL2 R l1 l2 /\ R x1 x2`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[APPEND; ALL2; RICHAUX_ALL2_NIL; APPEND_EQ_NIL; NOT_CONS_NIL;
                  CONJ_ACI]);;

let LIST_REL_GENLIST = prove
 (`!(P:A->B->bool) f g l.
     ALL2 P (list_of_seq f l) (list_of_seq g l) <=>
     !i. i < l ==> P (f i) (g i)`,
  SIMP_TAC[RICHAUX_ALL2_EL; LENGTH_LIST_OF_SEQ; EL_LIST_OF_SEQ]);;

let REVERSE_ZIP = prove
 (`!(l1:A list) (l2:B list).
     LENGTH l1 = LENGTH l2
     ==> REVERSE (ZIP l1 l2) = ZIP (REVERSE l1) (REVERSE l2)`,
  LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[LENGTH; NOT_SUC; GSYM NOT_SUC; SUC_INJ; ZIP; REVERSE] THEN
  DISCH_TAC THEN
  ASM_SIMP_TAC[GSYM ZIP_APPEND; LENGTH_REVERSE; LENGTH; ZIP; REVERSE]);;

let LIST_REL_REVERSE_EQ = prove
 (`!(R:A->B->bool) l1 l2. ALL2 R (REVERSE l1) (REVERSE l2) <=> ALL2 R l1 l2`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[REVERSE; ALL2; RICHAUX_ALL2_NIL; LIST_REL_APPEND_SING;
                  APPEND_EQ_NIL; NOT_CONS_NIL; CONJ_ACI]);;

let EVERY2_REVERSE1 = prove
 (`!(R:A->B->bool) l1 l2. ALL2 R l1 (REVERSE l2) <=> ALL2 R (REVERSE l1) l2`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [GSYM LIST_REL_REVERSE_EQ] THEN
  REWRITE_TAC[REVERSE_REVERSE]);;

let every_count_list = prove
 (`!P n. ALL P (COUNT_LIST n) <=> !m. m < n ==> P m`,
  REWRITE_TAC[COUNT_LIST_GENLIST; EVERY_GENLIST; I_THM]);;

let count_list_sub1 = prove
 (`!n. ~(n = 0) ==> COUNT_LIST n = CONS 0 (MAP SUC (COUNT_LIST (n - 1)))`,
  INDUCT_TAC THEN REWRITE_TAC[NOT_SUC; SUC_SUB1; COUNT_LIST_DEF]);;

let el_map_count = prove
 (`!n (f:num->A) m. n < m ==> EL n (MAP f (COUNT_LIST m)) = f n`,
  SIMP_TAC[MAP_COUNT_LIST; EL_LIST_OF_SEQ]);;

let map_replicate = prove
 (`!(f:A->B) n x. MAP f (REPLICATE n x) = REPLICATE n (f x)`,
  GEN_TAC THEN INDUCT_TAC THEN ASM_REWRITE_TAC[REPLICATE; MAP]);;

let REPLICATE_NIL = prove
 (`!x (y:A). REPLICATE x y = [] <=> x = 0`,
  REWRITE_TAC[GSYM LENGTH_EQ_NIL; LENGTH_REPLICATE]);;

let REPLICATE_APPEND = prove
 (`!n m (a:A). APPEND (REPLICATE n a) (REPLICATE m a) = REPLICATE (n + m) a`,
  INDUCT_TAC THEN ASM_REWRITE_TAC[REPLICATE; APPEND; ADD_CLAUSES]);;

let DROP_REPLICATE = prove
 (`!n m (a:A). DROP n (REPLICATE m a) = REPLICATE (m - n) a`,
  INDUCT_TAC THEN REWRITE_TAC[DROP; SUB_0] THEN
  INDUCT_TAC THEN ASM_REWRITE_TAC[REPLICATE; RICHAUX_DROP_CLAUSES; SUB_0; SUB_SUC]);;

let LIST_REL_REPLICATE_same = prove
 (`!(P:A->B->bool) n x y.
     ALL2 P (REPLICATE n x) (REPLICATE n y) <=> (0 < n ==> P x y)`,
  GEN_TAC THEN INDUCT_TAC THEN
  ASM_REWRITE_TAC[REPLICATE; ALL2; LT_REFL; LT_0] THEN MESON_TAC[]);;

let SNOC_REPLICATE = prove
 (`!n (x:A). SNOC x (REPLICATE n x) = REPLICATE (SUC n) x`,
  INDUCT_TAC THEN ASM_REWRITE_TAC[REPLICATE; SNOC]);;

let REVERSE_REPLICATE = prove
 (`!n (x:A). REVERSE (REPLICATE n x) = REPLICATE n x`,
  INDUCT_TAC THEN
  ASM_REWRITE_TAC[REPLICATE; REVERSE; GSYM SNOC_APPEND; SNOC_REPLICATE]);;

let SUM_REPLICATE = prove
 (`!n k. SUM (REPLICATE n k) = n * k`,
  INDUCT_TAC THEN ASM_REWRITE_TAC[REPLICATE; SUM; MULT_CLAUSES] THEN ARITH_TAC);;

let LENGTH_FLAT_REPLICATE = prove
 (`!n (ls:A list). LENGTH (FLAT (REPLICATE n ls)) = n * LENGTH ls`,
  INDUCT_TAC THEN
  ASM_REWRITE_TAC[REPLICATE; FLAT; LENGTH; LENGTH_APPEND; MULT_CLAUSES] THEN
  ARITH_TAC);;

let RICHAUX_ALL_DISTINCT_MAP_INJ = prove
 (`!(f:A->B) l.
     (!x y. f x = f y ==> x = y) /\ ALL_DISTINCT l ==> ALL_DISTINCT (MAP f l)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  ASM_SIMP_TAC[ALL_DISTINCT; MAP; MEM_MAP] THEN ASM_MESON_TAC[]);;

let all_distinct_count_list = prove
 (`!n. ALL_DISTINCT (COUNT_LIST n)`,
  INDUCT_TAC THEN REWRITE_TAC[COUNT_LIST_DEF; ALL_DISTINCT; MEM_MAP] THEN
  CONJ_TAC THENL
   [MESON_TAC[NOT_SUC];
    MATCH_MP_TAC RICHAUX_ALL_DISTINCT_MAP_INJ THEN ASM_REWRITE_TAC[SUC_INJ]]);;

let list_rel_lastn = prove
 (`!(f:A->B->bool) l1 l2 n.
     n <= LENGTH l1 /\ ALL2 f l1 l2 ==> ALL2 f (LASTN n l1) (LASTN n l2)`,
  REWRITE_TAC[LASTN_DEF; LIST_REL_REVERSE_EQ] THEN
  MESON_TAC[EVERY2_TAKE; LIST_REL_REVERSE_EQ]);;

let list_rel_butlastn = prove
 (`!(f:A->B->bool) l1 l2 n.
     n <= LENGTH l1 /\ ALL2 f l1 l2
     ==> ALL2 f (BUTLASTN n l1) (BUTLASTN n l2)`,
  REWRITE_TAC[BUTLASTN_DEF; LIST_REL_REVERSE_EQ] THEN
  MESON_TAC[EVERY2_DROP; LIST_REL_REVERSE_EQ]);;

let IS_SUFFIX_compute = prove
 (`!(l1:A list) l2. IS_SUFFIX l1 l2 <=> REVERSE l2 <<= REVERSE l1`,
  REWRITE_TAC[IS_SUFFIX_DEF]);;

let TAIL_BY_DROP = prove
 (`!ls:A list. ~(ls = []) ==> TL ls = DROP 1 ls`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[NOT_CONS_NIL; TL; ONE; DROP]);;

let DROP_SUC = prove
 (`!n (x:A list). DROP (SUC n) x = DROP 1 (DROP n x)`,
  REWRITE_TAC[DROP_DROP_T; ARITH_RULE `!n. SUC n = 1 + n`]);;

let DROP_TAKE_EQ_NIL = prove
 (`!(ls:A list) n. DROP n (TAKE n ls) = []`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC RICHAUX_DROP_LENGTH_TOO_LONG THEN
  REWRITE_TAC[RICHAUX_LENGTH_TAKE_EQ] THEN ARITH_TAC);;

let RICHAUX_TAKE_DROP_SWAP = prove
 (`!n m (ls:A list). TAKE m (DROP n ls) = DROP n (TAKE (n + m) ls)`,
  INDUCT_TAC THEN REWRITE_TAC[DROP; ADD_CLAUSES] THEN
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[RICHAUX_DROP_CLAUSES; RICHAUX_TAKE_CLAUSES]);;

let TAKE_DROP_SWAP = prove
 (`!(ls:A list) m n. TAKE m (DROP n ls) = DROP n (TAKE (n + m) ls)`,
  REWRITE_TAC[RICHAUX_TAKE_DROP_SWAP]);;

let GENLIST_K_CONS = prove
 (`!(e:A) n. list_of_seq (K e) (SUC n) = CONS e (list_of_seq (K e) n)`,
  REWRITE_TAC[LIST_OF_SEQ; K_THM] THEN
  REPEAT GEN_TAC THEN AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; o_THM; K_THM]);;

let MAX_LIST_def = MAX_LIST;;

let MAX_LIST_NIL = prove
 (`MAX_LIST [] = 0`,
  REWRITE_TAC[MAX_LIST]);;

let MAX_LIST_CONS = prove
 (`!h t. MAX_LIST (CONS h t) = MAX h (MAX_LIST t)`,
  REWRITE_TAC[MAX_LIST]);;

let MAX_LIST_MEM = prove
 (`!l. ~(l = []) ==> MEM (MAX_LIST l) l`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[NOT_CONS_NIL; MAX_LIST; MEM] THEN
  ASM_CASES_TAC `t:num list = []` THEN ASM_REWRITE_TAC[MAX_LIST; MEM] THENL
   [ARITH_TAC; REWRITE_TAC[MAX] THEN COND_CASES_TAC THEN ASM_MESON_TAC[]]);;

let MAX_LIST_PROPERTY = prove
 (`!l x. MEM x l ==> x <= MAX_LIST l`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[MEM; MAX_LIST] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
   [ARITH_TAC;
    FIRST_X_ASSUM(MP_TAC o SPEC `x:num`) THEN ASM_REWRITE_TAC[] THEN
    ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Registration of the HOL4 [simp] theorems of this file.                    *)
(* ------------------------------------------------------------------------- *)

let _ = cake_add_simps
  [EVERY_REVERSE; EVERY_REPLICATE; map_replicate; DROP_REPLICATE;
   LENGTH_FLAT_REPLICATE; LIST_REL_REVERSE_EQ; REPLICATE_NIL;
   IS_PREFIX_REFL; IS_SUFFIX_REFL; LIST_REL_APPEND_SING; IS_PREFIX_APPENDS;
   IS_PREFIX_APPEND3; rich_list_MEM_REPLICATE; NOT_NULL_SNOC; NOT_NIL_SNOC;
   NOT_SNOC_NIL; SNOC_ACYCLIC; SNOC_REPLICATE; REVERSE_REPLICATE;
   SUM_REPLICATE; MAX_LIST_NIL; MAX_LIST_CONS; REPLICATE; LENGTH_REPLICATE;
   LENGTH_GENLIST; EL_GENLIST; DROP_LENGTH_NIL; FLAT_APPEND; LAST_CONS;
   LENGTH_SNOC; REVERSE_EQ_NIL; MAP_APPEND; LENGTH_APPEND; LENGTH_MAP;
   LENGTH_REVERSE; REVERSE_REVERSE];;

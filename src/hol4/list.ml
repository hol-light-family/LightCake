(* ========================================================================= *)
(* list: port of HOL4 src/list/src/listScript.sml and                       *)
(* src/list/src/indexedListsScript.sml (the HOL4 library of CakeML v3479).  *)
(* The theorems of HOL4's listTheory and indexedListsTheory that the CakeML  *)
(* closure uses, with HOL4 names, over the vocabulary of hol4/vocab.ml       *)
(* (EVERY = ALL, EXISTS = EX, LIST_REL = ALL2, set = set_of_list,            *)
(* FRONT = BUTLAST, GENLIST = list_of_seq, FOLDR f e l = ITLIST f l e,       *)
(* ZIP (l1,l2) = ZIP l1 l2, SET_TO_LIST = list_of_set).  HOL4 l1 ++ l2 ++ l3 *)
(* is left associative: APPEND (APPEND l1 l2) l3.  A HOL4 name that HOL      *)
(* Light already uses for another statement gets the prefix list_ (e.g.     *)
(* list_MEM_EL); helper lemmas that are not HOL4 theorems get LISTAUX_.      *)
(* ========================================================================= *)

needs "hol4/vocab.ml";;

prioritize_num();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Basic clauses, MAP2, searching (INDEX_FIND, FIND, INDEX_OF).             *)
(* ------------------------------------------------------------------------- *)

let LISTAUX_SET_OF_LIST_APPLY = prove
 (`!l (x:A). set_of_list l x <=> MEM x l`,
  REWRITE_TAC[GSYM IN_SET_OF_LIST] THEN REWRITE_TAC[IN]);;

let LIST_TO_SET_DEF = prove
 (`(!x:A. set_of_list [] x <=> F) /\
   (!h t (x:A). set_of_list (CONS h t) x <=> x = h \/ set_of_list t x)`,
  REWRITE_TAC[LISTAUX_SET_OF_LIST_APPLY; MEM]);;

let EVERY_DEF = ALL;;

let list_EXISTS_DEF = EX;;

let EL_def = EL;;

let LISTAUX_LENGTH_MAP2 = prove
 (`!(f:A->B->C) xs ys. LENGTH (MAP2 f xs ys) = LENGTH xs`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[MAP2_DEF; LENGTH]);;

(* HOL4 LENGTH_MAP2 (MIN form) holds in HOL Light when LENGTH xs <= LENGTH ys *)
let list_LENGTH_MAP2 = prove
 (`!xs ys. LENGTH xs <= LENGTH ys ==>
     LENGTH (MAP2 (f:A->B->C) xs ys) = MIN (LENGTH xs) (LENGTH ys)`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[LISTAUX_LENGTH_MAP2; MIN]);;

let list_EL_MAP2 = prove
 (`!ts tt n. n < MIN (LENGTH ts) (LENGTH tt) ==>
     EL n (MAP2 (f:A->B->C) ts tt) = f (EL n ts) (EL n tt)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC EL_MAP2 THEN
  POP_ASSUM MP_TAC THEN ARITH_TAC);;

let MAP2_APPEND = prove
 (`!xs ys xs1 ys1 (f:A->B->C). LENGTH xs = LENGTH xs1 ==>
     MAP2 f (APPEND xs ys) (APPEND xs1 ys1) =
     APPEND (MAP2 f xs xs1) (MAP2 f ys ys1)`,
  LIST_INDUCT_TAC THEN REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `xs1:B list` list_CASES) THEN
  ASM_SIMP_TAC[LENGTH; APPEND; MAP2; NOT_SUC; SUC_INJ]);;
let INDEX_FIND_def = INDEX_FIND_DEF;;

let FIND_def = prove
 (`!P:A->bool. FIND P = OPTION_MAP SND o INDEX_FIND 0 P`,
  REWRITE_TAC[FUN_EQ_THM; o_THM; FIND_DEF]);;

let INDEX_OF_def = new_definition
  `INDEX_OF (x:A) = OPTION_MAP FST o INDEX_FIND 0 ((=) x)`;;

let LISTAUX_INDEX_FIND_SUC = prove
 (`!l n (P:A->bool). INDEX_FIND (SUC n) P l =
     OPTION_MAP (\p. (SUC (FST p), SND p)) (INDEX_FIND n P l)`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[INDEX_FIND_DEF; OPTION_MAP_DEF] THEN
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[OPTION_MAP_DEF]);;

let LISTAUX_OPTION_MAP_SUC = prove
 (`!y n. (OPTION_MAP SUC y = SOME 0 <=> F) /\
         (OPTION_MAP SUC y = SOME (SUC n) <=> y = SOME n)`,
  MATCH_MP_TAC option_INDUCT THEN
  REWRITE_TAC[OPTION_MAP_DEF; option_DISTINCT; option_INJ; NOT_SUC; SUC_INJ]);;

let LISTAUX_INDEX_OF_THM = prove
 (`(!x:A. INDEX_OF x [] = NONE) /\
   (!x h t. INDEX_OF (x:A) (CONS h t) =
      if x = h then SOME 0 else OPTION_MAP SUC (INDEX_OF x t))`,
  REWRITE_TAC[INDEX_OF_def; o_THM; INDEX_FIND_DEF; OPTION_MAP_DEF] THEN
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[OPTION_MAP_DEF; LISTAUX_INDEX_FIND_SUC] THEN
  SPEC_TAC(`INDEX_FIND 0 ((=) (x:A)) t`,`y:(num#A)option`) THEN
  MATCH_MP_TAC option_INDUCT THEN REWRITE_TAC[OPTION_MAP_DEF]);;

let LISTAUX_FORALL_LT_SUC = prove
 (`!P k. (!j. j < SUC k ==> P j) <=> P 0 /\ (!j. j < k ==> P (SUC j))`,
  REPEAT GEN_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THENL
  [FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC;
   FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
   POP_ASSUM MP_TAC THEN STRUCT_CASES_TAC(SPEC `j:num` num_CASES) THEN
   ASM_REWRITE_TAC[LT_SUC] THEN ASM_MESON_TAC[]]);;

let INDEX_OF_eq_SOME = prove
 (`!x:A l i. INDEX_OF x l = SOME i <=>
     i < LENGTH l /\ EL i l = x /\ (!j. j < i ==> ~(EL j l = x))`,
  GEN_TAC THEN LIST_INDUCT_TAC THENL
  [REWRITE_TAC[LISTAUX_INDEX_OF_THM; LENGTH; CONJUNCT1 LT; option_DISTINCT];
   ALL_TAC] THEN
  INDUCT_TAC THEN
  ASM_REWRITE_TAC[LISTAUX_INDEX_OF_THM; LENGTH; EL; HD; TL; LT_SUC; LT_0;
                  CONJUNCT1 LT; LISTAUX_FORALL_LT_SUC] THEN
  COND_CASES_TAC THEN
  ASM_REWRITE_TAC[option_INJ; NOT_SUC; LISTAUX_OPTION_MAP_SUC] THEN
  ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Case analysis, MAP, EVERY, EXISTS, MEM, LENGTH, APPEND, FILTER.          *)
(* ------------------------------------------------------------------------- *)

let list_nchotomy = list_CASES;;
let list_case_def = list_CASE;;
let list_size_def = list_size;;

let list_MAP_ID = prove
 (`(MAP (\x:A. x) l = l) /\ (MAP (I:A->A) l = l)`,
  REWRITE_TAC[MAP_ID; MAP_I; I_THM]);;

let list_MAP_EQ_NIL = prove
 (`(MAP (f:A->B) l = [] <=> l = []) /\ ([] = MAP f l <=> l = [])`,
  MESON_TAC[MAP_EQ_NIL]);;

let MAP_EQ_CONS = prove
 (`MAP (f:A->B) l = CONS h t <=>
   ?x0 t0. l = CONS x0 t0 /\ h = f x0 /\ t = MAP f t0`,
  STRUCT_CASES_TAC(ISPEC `l:A list` list_CASES) THEN
  REWRITE_TAC[MAP; NOT_CONS_NIL; GSYM NOT_CONS_NIL; CONS_11] THEN
  MESON_TAC[]);;

let MAP_EQ_SING = prove
 (`(MAP (f:A->B) l = [x]) <=> ?x0. (l = [x0]) /\ (x = f x0)`,
  REWRITE_TAC[MAP_EQ_CONS; list_MAP_EQ_NIL] THEN MESON_TAC[]);;

let list_MAP_o = prove
 (`!f:B->C. !g:A->B. MAP (f o g) = (MAP f) o (MAP g)`,
  REWRITE_TAC[FUN_EQ_THM; o_THM; MAP_o]);;

let EL_APPEND_EQN = prove
 (`!l1 l2 (n:num). EL n (APPEND l1 l2):A =
     if n < LENGTH l1 then EL n l1 else EL (n - LENGTH l1) l2`,
  REWRITE_TAC[EL_APPEND]);;

let MAP_TL = prove
 (`!l (f:A->B). ~(l = []) ==> MAP f (TL l) = TL (MAP f l)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[MAP; TL; NOT_CONS_NIL]);;

let EVERY_EL = prove
 (`!(l:A list) P. ALL P l <=> !n. n < LENGTH l ==> P (EL n l)`,
  REWRITE_TAC[ALL_EL]);;

let EVERY_CONJ = prove
 (`!P Q l. ALL (\x:A. P x /\ Q x) l <=> ALL P l /\ ALL Q l`,
  REWRITE_TAC[AND_ALL]);;

let EVERY_MEM = prove
 (`!P l:A list. ALL P l <=> !e. MEM e l ==> P e`,
  REWRITE_TAC[ALL_MEM]);;

let EVERY_MAP = prove
 (`!P (f:A->B) l. ALL P (MAP f l) <=> ALL (\x. P (f x)) l`,
  REWRITE_TAC[ALL_MAP; o_DEF]);;

let MONO_EVERY = MONO_ALL;;

let EXISTS_MEM = prove
 (`!P l:A list. EX P l <=> ?e. MEM e l /\ P e`,
  REWRITE_TAC[GSYM EX_MEM] THEN MESON_TAC[]);;

let EXISTS_MAP = prove
 (`!P (f:A->B) l. EX P (MAP f l) <=> EX (\x. P (f x)) l`,
  REWRITE_TAC[EX_MAP; o_DEF]);;

let MEM_FLAT = prove
 (`!x:A L. MEM x (FLAT L) <=> ?l. MEM l L /\ MEM x l`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[FLAT; MEM; MEM_APPEND] THEN
  MESON_TAC[]);;

let EVERY_FLAT = prove
 (`ALL (P:A->bool) (FLAT ls) <=> ALL (ALL P) ls`,
  SPEC_TAC(`ls:(A list)list`,`ls:(A list)list`) THEN
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[FLAT; ALL; ALL_APPEND]);;

let EVERY_APPEND = ALL_APPEND;;

let NOT_EVERY = prove
 (`!P l:A list. ~ALL P l <=> EX ((~) o P) l`,
  REWRITE_TAC[NOT_ALL; o_DEF]);;

let NOT_EXISTS = prove
 (`!P l:A list. ~EX P l <=> ALL ((~) o P) l`,
  REWRITE_TAC[NOT_EX; o_DEF]);;

let list_MEM_MAP = prove
 (`!(l:A list) (f:A->B) x. MEM x (MAP f l) <=> ?y. x = f y /\ MEM y l`,
  REWRITE_TAC[MEM_MAP] THEN MESON_TAC[]);;

let MEM_MAP_f = prove
 (`!(f:A->B) l a. MEM a l ==> MEM (f a) (MAP f l)`,
  REWRITE_TAC[MEM_MAP] THEN MESON_TAC[]);;

let LENGTH_NIL = LENGTH_EQ_NIL;;

let LENGTH_NIL_SYM = prove
 (`(0 = LENGTH (l:A list)) <=> (l = [])`,
  MESON_TAC[LENGTH_EQ_NIL]);;

let SING_HD = prove
 (`(([HD xs] = xs) <=> (LENGTH xs = 1)) /\
   ((xs = [HD xs]) <=> (LENGTH (xs:A list) = 1))`,
  STRUCT_CASES_TAC(ISPEC `xs:A list` list_CASES) THEN
  REWRITE_TAC[HD; LENGTH; CONS_11; NOT_CONS_NIL; GSYM NOT_CONS_NIL] THEN
  REWRITE_TAC[ONE; SUC_INJ; NOT_SUC; LENGTH_EQ_NIL] THEN MESON_TAC[]);;

let NULL_EQ = prove
 (`!l:A list. NULL l <=> l = []`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[NULL; NOT_CONS_NIL]);;

let NULL_LENGTH = prove
 (`!l:A list. NULL l <=> LENGTH l = 0`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[NULL; LENGTH; NOT_SUC]);;

let LENGTH_CONS = prove
 (`!l n. (LENGTH l = SUC n) <=> ?h:A. ?l'. (LENGTH l' = n) /\ (l = CONS h l')`,
  REWRITE_TAC[LENGTH_EQ_CONS] THEN MESON_TAC[]);;
let LENGTH_EQ_SUM = prove
 (`!l:A list n1 n2.
     LENGTH l = n1 + n2 <=>
     ?l1 l2. LENGTH l1 = n1 /\ LENGTH l2 = n2 /\ l = APPEND l1 l2`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
  [ALL_TAC; STRIP_TAC THEN ASM_REWRITE_TAC[LENGTH_APPEND]] THEN
  SPEC_TAC(`l:A list`,`l:A list`) THEN SPEC_TAC(`n1:num`,`n1:num`) THEN
  INDUCT_TAC THEN GEN_TAC THENL
  [DISCH_TAC THEN MAP_EVERY EXISTS_TAC [`[]:A list`; `l:A list`] THEN
   ASM_REWRITE_TAC[LENGTH; APPEND; ADD_CLAUSES];
   ALL_TAC] THEN
  REWRITE_TAC[ADD_CLAUSES] THEN
  DISCH_THEN(X_CHOOSE_THEN `h:A` (X_CHOOSE_THEN `t:A list`
    STRIP_ASSUME_TAC) o REWRITE_RULE[LENGTH_EQ_CONS]) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `t:A list`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `l1:A list` (X_CHOOSE_THEN `l2:A list`
    STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`CONS (h:A) l1`; `l2:A list`] THEN
  ASM_REWRITE_TAC[LENGTH; APPEND]);;

let LENGTH_EQ_NUM = prove
 (`(!l:A list. LENGTH l = 0 <=> l = []) /\
   (!l:A list n. LENGTH l = SUC n <=> ?h l'. LENGTH l' = n /\ l = CONS h l') /\
   (!l:A list n1 n2.
      LENGTH l = n1 + n2 <=>
      ?l1 l2. LENGTH l1 = n1 /\ LENGTH l2 = n2 /\ l = APPEND l1 l2)`,
  REWRITE_TAC[LENGTH_EQ_NIL; LENGTH_CONS; LENGTH_EQ_SUM]);;

let LISTAUX_LENGTH_EQ_POS = prove
 (`!l:A list m. 0 < m ==>
     (LENGTH l = m <=> ?h l'. LENGTH l' = m - 1 /\ l = CONS h l')`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`l:A list`; `m - 1`] LENGTH_CONS) THEN
  SUBGOAL_THEN `SUC (m - 1) = m` (fun th -> REWRITE_TAC[th]) THEN
  ASM_ARITH_TAC);;

(* HOL4: LENGTH_EQ_NUM_compute (numLib.SUC_TO_NUMERAL_DEFN_CONV applied to
   LENGTH_EQ_NUM): HOL Light numerals are binary, so the SUC clause becomes
   one clause for odd and one for even numerals; the even one tests 0. *)
let LENGTH_EQ_NUM_compute = prove
 (`(!l:A list. LENGTH l = 0 <=> l = []) /\
   (!l:A list n. LENGTH l = NUMERAL (BIT1 n) <=>
      ?h l'. LENGTH l' = NUMERAL (BIT1 n) - 1 /\ l = CONS h l') /\
   (!l:A list n. LENGTH l = NUMERAL (BIT0 n) <=>
      if NUMERAL (BIT0 n) = 0 then l = []
      else ?h l'. LENGTH l' = NUMERAL (BIT0 n) - 1 /\ l = CONS h l') /\
   (!l:A list n1 n2.
      LENGTH l = n1 + n2 <=>
      ?l1 l2. LENGTH l1 = n1 /\ LENGTH l2 = n2 /\ l = APPEND l1 l2)`,
  REWRITE_TAC[LENGTH_EQ_NIL; LENGTH_EQ_SUM] THEN CONJ_TAC THEN
  REPEAT GEN_TAC THENL
  [MATCH_MP_TAC LISTAUX_LENGTH_EQ_POS THEN
   GEN_REWRITE_TAC RAND_CONV [NUMERAL] THEN REWRITE_TAC[BIT1; LT_0];
   COND_CASES_TAC THEN ASM_REWRITE_TAC[LENGTH_EQ_NIL] THEN
   MATCH_MP_TAC LISTAUX_LENGTH_EQ_POS THEN ASM_ARITH_TAC]);;

let APPEND_eq_NIL = prove
 (`(!l1 l2:A list. ([] = APPEND l1 l2) <=> (l1 = []) /\ (l2 = [])) /\
   (!l1 l2:A list. (APPEND l1 l2 = []) <=> (l1 = []) /\ (l2 = []))`,
  MESON_TAC[APPEND_EQ_NIL]);;

let MAP_EQ_APPEND = prove
 (`MAP (f:A->B) l = APPEND l1 l2 <=>
   ?l10 l20. l = APPEND l10 l20 /\ l1 = MAP f l10 /\ l2 = MAP f l20`,
  EQ_TAC THENL [ALL_TAC; STRIP_TAC THEN ASM_REWRITE_TAC[MAP_APPEND]] THEN
  SPEC_TAC(`l:A list`,`l:A list`) THEN SPEC_TAC(`l1:B list`,`l1:B list`) THEN
  LIST_INDUCT_TAC THEN REWRITE_TAC[APPEND] THENL
  [REPEAT STRIP_TAC THEN MAP_EVERY EXISTS_TAC [`[]:A list`; `l:A list`] THEN
   ASM_REWRITE_TAC[APPEND; MAP];
   ALL_TAC] THEN
  REWRITE_TAC[MAP_EQ_CONS] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `t0:A list`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `l10:A list` (X_CHOOSE_THEN `l20:A list`
    STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`CONS (x0:A) l10`; `l20:A list`] THEN
  ASM_REWRITE_TAC[APPEND; MAP]);;

let APPEND_EQ_SING = prove
 (`(APPEND l1 l2 = [e:A]) <=>
   (l1 = [e]) /\ (l2 = []) \/ (l1 = []) /\ (l2 = [e])`,
  STRUCT_CASES_TAC(ISPEC `l1:A list` list_CASES) THEN
  REWRITE_TAC[APPEND; CONS_11; NOT_CONS_NIL; GSYM NOT_CONS_NIL;
              APPEND_EQ_NIL] THEN
  MESON_TAC[]);;

let APPEND_11 = prove
 (`(!l1 l2 l3:A list. (APPEND l1 l2 = APPEND l1 l3) <=> (l2 = l3)) /\
   (!l1 l2 l3:A list. (APPEND l2 l1 = APPEND l3 l1) <=> (l2 = l3))`,
  REWRITE_TAC[APPEND_LCANCEL; APPEND_RCANCEL]);;

let APPEND_LENGTH_EQ = prove
 (`!l1 l1':A list. (LENGTH l1 = LENGTH l1') ==>
   !l2 l2':A list. (LENGTH l2 = LENGTH l2') ==>
     ((APPEND l1 l2 = APPEND l1' l2') <=> (l1 = l1') /\ (l2 = l2'))`,
  LIST_INDUCT_TAC THEN GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `l1':A list` list_CASES) THEN
  REWRITE_TAC[LENGTH; APPEND; NOT_SUC; GSYM NOT_SUC; SUC_INJ; CONS_11] THEN
  ASM_MESON_TAC[]);;

let APPEND_11_LENGTH = prove
 (`(!l1 l2 l1' l2':A list. LENGTH l1 = LENGTH l1' ==>
      (APPEND l1 l2 = APPEND l1' l2' <=> l1 = l1' /\ l2 = l2')) /\
   (!l1 l2 l1' l2':A list. LENGTH l2 = LENGTH l2' ==>
      (APPEND l1 l2 = APPEND l1' l2' <=> l1 = l1' /\ l2 = l2'))`,
  CONJ_TAC THEN REPEAT STRIP_TAC THEN EQ_TAC THENL
  [ALL_TAC; SIMP_TAC[]; ALL_TAC; SIMP_TAC[]] THEN
  DISCH_TAC THEN
  (SUBGOAL_THEN
    `LENGTH (APPEND (l1:A list) l2) = LENGTH (APPEND (l1':A list) l2')`
    MP_TAC THENL [ASM_REWRITE_TAC[]; REWRITE_TAC[LENGTH_APPEND]]) THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`l1:A list`; `l1':A list`] APPEND_LENGTH_EQ) THEN
  (ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC]) THEN
  DISCH_THEN(MP_TAC o SPECL [`l2:A list`; `l2':A list`]) THEN
  (ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC]) THEN ASM_REWRITE_TAC[]);;

let MEM_SPLIT = MEM_APPEND_DECOMPOSE;;

let LIST_EQ_REWRITE = prove
 (`!l1 l2:A list. (l1 = l2) <=>
     ((LENGTH l1 = LENGTH l2) /\
      (!x. x < LENGTH l1 ==> EL x l1 = EL x l2))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[LIST_EQ] THEN MESON_TAC[]);;

let list_LIST_EQ = prove
 (`!l1 l2:A list.
     (LENGTH l1 = LENGTH l2) /\ (!x. x < LENGTH l1 ==> (EL x l1 = EL x l2))
     ==> (l1 = l2)`,
  MESON_TAC[LIST_EQ_REWRITE]);;

let FILTER_EQ_NIL = prove
 (`!P l:A list. (FILTER P l = []) <=> (ALL (\x. ~(P x)) l)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[FILTER; ALL] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[NOT_CONS_NIL]);;

let FILTER_EQ_ID = prove
 (`!P l:A list. (FILTER P l = l) <=> (ALL P l)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[FILTER; ALL] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[CONS_11] THEN
  DISCH_THEN(MP_TAC o AP_TERM `LENGTH:A list->num`) THEN
  MP_TAC(ISPECL [`P:A->bool`; `t:A list`] LENGTH_FILTER) THEN
  REWRITE_TAC[LENGTH] THEN ARITH_TAC);;

let FILTER_EQ_CONS = prove
 (`!P l (h:A) lr.
     FILTER P l = CONS h lr <=>
     ?l1 l2. l = APPEND (APPEND l1 [h]) l2 /\ FILTER P l1 = [] /\
             FILTER P l2 = lr /\ P h`,
  GEN_TAC THEN LIST_INDUCT_TAC THENL
  [REWRITE_TAC[FILTER; APPEND_eq_NIL; NOT_CONS_NIL; GSYM NOT_CONS_NIL];
   ALL_TAC] THEN
  X_GEN_TAC `y:A` THEN X_GEN_TAC `lr:A list` THEN
  REWRITE_TAC[FILTER] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[CONS_11] THEN
  EQ_TAC THEN STRIP_TAC THENL
  [MAP_EVERY EXISTS_TAC [`[]:A list`; `t:A list`] THEN
   ASM_REWRITE_TAC[APPEND; FILTER] THEN ASM_MESON_TAC[];
   POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
   STRUCT_CASES_TAC(ISPEC `l1:A list` list_CASES) THEN
   REWRITE_TAC[APPEND; FILTER; CONS_11] THENL
   [MESON_TAC[];
    COND_CASES_TAC THEN REWRITE_TAC[NOT_CONS_NIL] THEN ASM_MESON_TAC[]];
   MAP_EVERY EXISTS_TAC [`CONS (h:A) l1`; `l2:A list`] THEN
   ASM_REWRITE_TAC[APPEND; FILTER];
   POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
   STRUCT_CASES_TAC(ISPEC `l1:A list` list_CASES) THEN
   REWRITE_TAC[APPEND; FILTER; CONS_11] THENL
   [MESON_TAC[];
    COND_CASES_TAC THEN REWRITE_TAC[NOT_CONS_NIL] THEN ASM_MESON_TAC[]]]);;

let FILTER_F = prove
 (`!xs:A list. FILTER (\x. F) xs = []`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[FILTER]);;

let FILTER_T = prove
 (`!xs:A list. FILTER (\x. T) xs = xs`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[FILTER]);;

let EVERY_FILTER = ALL_FILTER;;

let EVERY_FILTER_IMP = prove
 (`!P1 P2 l:A list. ALL P1 l ==> ALL P1 (FILTER P2 l)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ALL_FILTER] THEN
  MATCH_MP_TAC MONO_ALL THEN SIMP_TAC[]);;

let SUM_eq_0 = prove
 (`!ls. (SUM ls = 0) <=> !x. MEM x ls ==> (x = 0)`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[SUM; MEM; ADD_EQ_0] THEN
  MESON_TAC[]);;

let NULL_FILTER = prove
 (`!P ls:A list. NULL (FILTER P ls) <=> !x. MEM x ls ==> ~P x`,
  REWRITE_TAC[NULL_EQ; FILTER_EQ_NIL; ALL_MEM]);;

(* ------------------------------------------------------------------------- *)
(* LIST_REL (= EVERY2 = ALL2).                                               *)
(* ------------------------------------------------------------------------- *)

let LIST_REL_def = ALL2;;

let LIST_REL_ind = prove
 (`!R LIST_REL'.
     LIST_REL' [] [] /\
     (!h1 h2 t1 t2. R h1 h2 /\ LIST_REL' t1 t2 ==>
                    LIST_REL' (CONS h1 t1) (CONS h2 t2)) ==>
     !a0 a1. ALL2 (R:A->B->bool) a0 a1 ==> LIST_REL' a0 a1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN LIST_INDUCT_TAC THEN GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `a1:B list` list_CASES) THEN
  REWRITE_TAC[ALL2] THEN ASM_MESON_TAC[]);;

let LIST_REL_EL_EQN = prove
 (`!R l1 l2. ALL2 (R:A->B->bool) l1 l2 <=>
     (LENGTH l1 = LENGTH l2) /\
     !n. n < LENGTH l1 ==> R (EL n l1) (EL n l2)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `l2:B list` list_CASES) THEN
  ASM_REWRITE_TAC[ALL2; LENGTH; NOT_SUC; GSYM NOT_SUC; SUC_INJ;
                  CONJUNCT1 LT; LISTAUX_FORALL_LT_SUC; EL; HD; TL] THEN
  MESON_TAC[]);;

let LIST_REL_mono = MONO_ALL2;;

let LIST_REL_NIL = prove
 (`(ALL2 (R:A->B->bool) [] y <=> (y = [])) /\ (ALL2 R x [] <=> (x = []))`,
  CONJ_TAC THENL
  [STRUCT_CASES_TAC(ISPEC `y:B list` list_CASES);
   STRUCT_CASES_TAC(ISPEC `x:A list` list_CASES)] THEN
  REWRITE_TAC[ALL2; NOT_CONS_NIL]);;

let LIST_REL_CONS1 = prove
 (`ALL2 (R:A->B->bool) (CONS h t) xs <=>
   ?h' t'. (xs = CONS h' t') /\ R h h' /\ ALL2 R t t'`,
  STRUCT_CASES_TAC(ISPEC `xs:B list` list_CASES) THEN
  REWRITE_TAC[ALL2; NOT_CONS_NIL; GSYM NOT_CONS_NIL; CONS_11] THEN
  MESON_TAC[]);;

let LIST_REL_CONS2 = prove
 (`ALL2 (R:A->B->bool) xs (CONS h t) <=>
   ?h' t'. (xs = CONS h' t') /\ R h' h /\ ALL2 R t' t`,
  STRUCT_CASES_TAC(ISPEC `xs:A list` list_CASES) THEN
  REWRITE_TAC[ALL2; NOT_CONS_NIL; GSYM NOT_CONS_NIL; CONS_11] THEN
  MESON_TAC[]);;

let LIST_REL_CONJ = prove
 (`ALL2 (\a b. (P:A->B->bool) a b /\ Q a b) l1 l2 <=>
   ALL2 (\a b. P a b) l1 l2 /\ ALL2 (\a b. Q a b) l1 l2`,
  REWRITE_TAC[AND_ALL2; ETA_AX]);;

let LIST_REL_MAP1 = prove
 (`ALL2 (R:B->C->bool) (MAP (f:A->B) l1) l2 <=> ALL2 (R o f) l1 l2`,
  SPEC_TAC(`l2:C list`,`l2:C list`) THEN SPEC_TAC(`l1:A list`,`l1:A list`) THEN
  LIST_INDUCT_TAC THEN GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `l2:C list` list_CASES) THEN
  ASM_REWRITE_TAC[MAP; ALL2; o_THM]);;

let LIST_REL_MAP2 = prove
 (`ALL2 (R:A->C->bool) l1 (MAP (f:B->C) l2) <=>
   ALL2 (\a b. R a (f b)) l1 l2`,
  SPEC_TAC(`l2:B list`,`l2:B list`) THEN SPEC_TAC(`l1:A list`,`l1:A list`) THEN
  LIST_INDUCT_TAC THEN GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `l2:B list` list_CASES) THEN
  ASM_REWRITE_TAC[MAP; ALL2]);;

let LIST_REL_LENGTH = prove
 (`!x y. ALL2 (R:A->B->bool) x y ==> (LENGTH x = LENGTH y)`,
  SIMP_TAC[LIST_REL_EL_EQN]);;

let LIST_REL_SPLIT1 = prove
 (`!xs1 zs. ALL2 (P:A->B->bool) (APPEND xs1 xs2) zs <=>
     ?ys1 ys2. (zs = APPEND ys1 ys2) /\ ALL2 P xs1 ys1 /\ ALL2 P xs2 ys2`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[APPEND; LIST_REL_NIL; LIST_REL_CONS1] THENL
  [MESON_TAC[APPEND]; ALL_TAC] THEN
  X_GEN_TAC `zs:B list` THEN EQ_TAC THEN STRIP_TAC THENL
  [MAP_EVERY EXISTS_TAC [`CONS (h':B) ys1`; `ys2:B list`] THEN
   ASM_REWRITE_TAC[APPEND; CONS_11] THEN
   MAP_EVERY EXISTS_TAC [`h':B`; `ys1:B list`] THEN ASM_REWRITE_TAC[];
   MAP_EVERY EXISTS_TAC [`h':B`; `APPEND (t':B list) ys2`] THEN
   ASM_REWRITE_TAC[APPEND] THEN
   MAP_EVERY EXISTS_TAC [`t':B list`; `ys2:B list`] THEN ASM_REWRITE_TAC[]]);;

let LIST_REL_SPLIT2 = prove
 (`!xs1 zs. ALL2 (P:A->B->bool) zs (APPEND xs1 xs2) <=>
     ?ys1 ys2. (zs = APPEND ys1 ys2) /\ ALL2 P ys1 xs1 /\ ALL2 P ys2 xs2`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[APPEND; LIST_REL_NIL; LIST_REL_CONS2] THENL
  [MESON_TAC[APPEND]; ALL_TAC] THEN
  X_GEN_TAC `zs:A list` THEN EQ_TAC THEN STRIP_TAC THENL
  [MAP_EVERY EXISTS_TAC [`CONS (h':A) ys1`; `ys2:A list`] THEN
   ASM_REWRITE_TAC[APPEND; CONS_11] THEN
   MAP_EVERY EXISTS_TAC [`h':A`; `ys1:A list`] THEN ASM_REWRITE_TAC[];
   MAP_EVERY EXISTS_TAC [`h':A`; `APPEND (t':A list) ys2`] THEN
   ASM_REWRITE_TAC[APPEND] THEN
   MAP_EVERY EXISTS_TAC [`t':A list`; `ys2:A list`] THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* list_size, congruences.                                                   *)
(* ------------------------------------------------------------------------- *)

let list_size_append = prove
 (`!(f:A->num) xs ys.
     list_size f (APPEND xs ys) = list_size f xs + list_size f ys`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[APPEND; list_size] THEN
  ARITH_TAC);;

let FOLDR_CONG = prove
 (`!l l' b b' (f:A->B->B) f'.
     l = l' /\ b = b' /\ (!x a. MEM x l' ==> (f x a = f' x a))
     ==> ITLIST f l b = ITLIST f' l' b'`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 SUBST1_TAC (CONJUNCTS_THEN2 SUBST1_TAC MP_TAC)) THEN
  SPEC_TAC(`l':A list`,`l':A list`) THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[ITLIST; MEM] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  ASM_MESON_TAC[]);;

let MAP_CONG = prove
 (`!l1 l2 (f:A->B) f'.
     l1 = l2 /\ (!x. MEM x l2 ==> (f x = f' x)) ==> MAP f l1 = MAP f' l2`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 SUBST1_TAC MP_TAC) THEN
  REWRITE_TAC[ALL_MEM] THEN DISCH_TAC THEN MATCH_MP_TAC MAP_EQ THEN
  ASM_REWRITE_TAC[]);;

let EVERY_MONOTONIC = MONO_ALL;;

(* ------------------------------------------------------------------------- *)
(* ZIP and UNZIP.  HOL Light's ZIP l1 l2 recurses on l1 (HD/TL of l2), so it *)
(* has the length of l1; facts about unequal lengths need hypotheses.       *)
(* ------------------------------------------------------------------------- *)

let LISTAUX_EXISTS_LT_SUC = prove
 (`!P k. (?j. j < SUC k /\ P j) <=> P 0 \/ (?j. j < k /\ P (SUC j))`,
  REPEAT GEN_TAC THEN
  MP_TAC(BETA_RULE(SPECL [`\j. ~((P:num->bool) j)`; `k:num`]
                         LISTAUX_FORALL_LT_SUC)) THEN
  MESON_TAC[]);;

(* HOL4 ZIP_def: the clause ZIP (l1,[]) = [] is false in HOL Light for a
   non-empty l1 and is left out. *)
let ZIP_def = prove
 (`(!l2:B list. ZIP ([]:A list) l2 = []) /\
   (!(x1:A) l1 (x2:B) l2.
      ZIP (CONS x1 l1) (CONS x2 l2) = CONS (x1,x2) (ZIP l1 l2))`,
  REWRITE_TAC[ZIP_DEF; HD; TL]);;

let UNZIP_MAP = UNZIP_DEF;;

let LISTAUX_LENGTH_ZIP = prove
 (`!(xs:A list) (ys:B list). LENGTH (ZIP xs ys) = LENGTH xs`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[ZIP_DEF; LENGTH]);;

(* HOL4 LENGTH_ZIP_MIN holds in HOL Light when LENGTH xs <= LENGTH ys. *)
let LENGTH_ZIP_MIN = prove
 (`!(xs:A list) (ys:B list). LENGTH xs <= LENGTH ys ==>
     LENGTH (ZIP xs ys) = MIN (LENGTH xs) (LENGTH ys)`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[LISTAUX_LENGTH_ZIP; MIN]);;

let ZIP_MAP = prove
 (`!(l1:A list) (l2:B list) (f1:A->C) (f2:B->D).
     (LENGTH l1 = LENGTH l2) ==>
     (ZIP (MAP f1 l1) l2 = MAP (\p. (f1 (FST p), SND p)) (ZIP l1 l2)) /\
     (ZIP l1 (MAP f2 l2) = MAP (\p. (FST p, f2 (SND p))) (ZIP l1 l2))`,
  LIST_INDUCT_TAC THEN GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `l2:B list` list_CASES) THEN
  ASM_SIMP_TAC[LENGTH; MAP; ZIP_def; NOT_SUC; GSYM NOT_SUC; SUC_INJ]);;

let MEM_ZIP = prove
 (`!(l1:A list) (l2:B list) p.
     (LENGTH l1 = LENGTH l2) ==>
     (MEM p (ZIP l1 l2) <=> ?n. n < LENGTH l1 /\ (p = (EL n l1, EL n l2)))`,
  LIST_INDUCT_TAC THEN GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `l2:B list` list_CASES) THEN
  ASM_SIMP_TAC[LENGTH; MEM; ZIP_def; NOT_SUC; GSYM NOT_SUC; SUC_INJ;
               CONJUNCT1 LT; LISTAUX_EXISTS_LT_SUC; EL; HD; TL]);;

let EL_ZIP = prove
 (`!(l1:A list) (l2:B list) n.
     (LENGTH l1 = LENGTH l2) /\ n < LENGTH l1 ==>
     (EL n (ZIP l1 l2) = (EL n l1, EL n l2))`,
  LIST_INDUCT_TAC THEN GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `l2:B list` list_CASES) THEN
  REWRITE_TAC[LENGTH; NOT_SUC; GSYM NOT_SUC; SUC_INJ; CONJUNCT1 LT] THEN
  INDUCT_TAC THEN ASM_SIMP_TAC[ZIP_def; EL; HD; TL; LT_SUC]);;

let MAP2_MAP = prove
 (`!(l1:A list) (l2:B list). (LENGTH l1 = LENGTH l2) ==>
     !f:A->B->C. MAP2 f l1 l2 = MAP (UNCURRY f) (ZIP l1 l2)`,
  LIST_INDUCT_TAC THEN GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `l2:B list` list_CASES) THEN
  ASM_SIMP_TAC[LENGTH; NOT_SUC; GSYM NOT_SUC; SUC_INJ; MAP2; MAP; ZIP_def;
               UNCURRY_DEF]);;

let MAP_ZIP = prove
 (`(LENGTH (l1:A list) = LENGTH (l2:B list)) ==>
     (MAP FST (ZIP l1 l2) = l1) /\
     (MAP SND (ZIP l1 l2) = l2) /\
     (MAP ((f:A->C) o FST) (ZIP l1 l2) = MAP f l1) /\
     (MAP ((g:B->D) o SND) (ZIP l1 l2) = MAP g l2)`,
  SIMP_TAC[MAP_FST_ZIP; MAP_SND_ZIP; MAP_o]);;

let list_MEM_EL = MEM_EXISTS_EL;;

(* ------------------------------------------------------------------------- *)
(* REVERSE, LAST and FRONT (= BUTLAST).                                      *)
(* ------------------------------------------------------------------------- *)

let REVERSE_DEF = REVERSE;;

let REVERSE_11 = prove
 (`!l1 l2:A list. (REVERSE l1 = REVERSE l2) <=> (l1 = l2)`,
  MESON_TAC[REVERSE_REVERSE]);;

let MEM_REVERSE = prove
 (`!l (x:A). MEM x (REVERSE l) <=> MEM x l`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[REVERSE; MEM; MEM_APPEND] THEN
  MESON_TAC[]);;

let LAST_DEF = LAST;;

let FRONT_DEF = BUTLAST;;

let list_LAST_EL = prove
 (`!ls:A list. ~(ls = []) ==> (LAST ls = EL (PRE (LENGTH ls)) ls)`,
  SIMP_TAC[LAST_EL; ARITH_RULE `PRE n = n - 1`]);;

let LAST_MAP = prove
 (`!l (f:A->B). ~(l = []) ==> (LAST (MAP f l) = f (LAST l))`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[MAP; LAST; NOT_CONS_NIL; MAP_EQ_NIL] THEN
  GEN_TAC THEN COND_CASES_TAC THEN ASM_SIMP_TAC[]);;

let APPEND_FRONT_LAST = APPEND_BUTLAST_LAST;;

let LAST_CONS_cond = LAST;;

(* ------------------------------------------------------------------------- *)
(* TAKE and DROP.                                                            *)
(* ------------------------------------------------------------------------- *)

let TAKE_def = TAKE_DEF;;

let DROP_def = DROP_DEF;;

let TAKE_nil = CONJUNCT1 TAKE_DEF;;

let TAKE_cons = prove
 (`0 < n ==> (TAKE n (CONS (x:A) xs) = CONS x (TAKE (n - 1) xs))`,
  REWRITE_TAC[TAKE_DEF] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[LT_REFL]);;

let DROP_nil = CONJUNCT1 DROP_DEF;;

let DROP_cons = prove
 (`0 < n ==> (DROP n (CONS (x:A) xs) = DROP (n - 1) xs)`,
  REWRITE_TAC[DROP_DEF] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[LT_REFL]);;

let TAKE_0 = prove
 (`TAKE 0 (l:A list) = []`,
  STRUCT_CASES_TAC(ISPEC `l:A list` list_CASES) THEN REWRITE_TAC[TAKE_DEF]);;

let DROP_0 = prove
 (`DROP 0 (l:A list) = l`,
  STRUCT_CASES_TAC(ISPEC `l:A list` list_CASES) THEN REWRITE_TAC[DROP_DEF]);;

let TAKE_LENGTH_ID = prove
 (`!l:A list. TAKE (LENGTH l) l = l`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[TAKE_DEF; LENGTH; NOT_SUC; SUC_SUB1]);;

let LENGTH_TAKE = prove
 (`!n l:A list. n <= LENGTH l ==> (LENGTH (TAKE n l) = n)`,
  ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[TAKE_DEF; LENGTH] THENL [ARITH_TAC; ALL_TAC] THEN
  GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[LENGTH] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `n - 1`) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN ASM_ARITH_TAC);;

let TAKE_LENGTH_TOO_LONG = prove
 (`!l:A list n. LENGTH l <= n ==> (TAKE n l = l)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[TAKE_DEF; LENGTH] THEN
  GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[CONS_11] THENL
  [ARITH_TAC; DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC]);;

let LENGTH_TAKE_EQ = prove
 (`LENGTH (TAKE n (xs:A list)) = if n <= LENGTH xs then n else LENGTH xs`,
  COND_CASES_TAC THEN ASM_SIMP_TAC[LENGTH_TAKE] THEN
  AP_TERM_TAC THEN MATCH_MP_TAC TAKE_LENGTH_TOO_LONG THEN ASM_ARITH_TAC);;

let MAP_TAKE = prove
 (`!(f:A->B) n l. MAP f (TAKE n l) = TAKE n (MAP f l)`,
  GEN_TAC THEN ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[TAKE_DEF; MAP] THEN
  GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[MAP]);;

let TAKE_DROP = prove
 (`!n l:A list. APPEND (TAKE n l) (DROP n l) = l`,
  ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[TAKE_DEF; DROP_DEF; APPEND] THEN
  GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[APPEND]);;

let TAKE1 = prove
 (`!l:A list. ~(l = []) ==> (TAKE 1 l = [EL 0 l])`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[NOT_CONS_NIL; TAKE_DEF; EL; HD] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[TAKE_0]);;

let TAKE1_DROP = prove
 (`!n l:A list. n < LENGTH l ==> (TAKE 1 (DROP n l) = [EL n l])`,
  ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN
  LIST_INDUCT_TAC THEN REWRITE_TAC[LENGTH; CONJUNCT1 LT] THEN
  GEN_TAC THEN REWRITE_TAC[DROP_DEF; EL_CONS] THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[] THENL
  [REWRITE_TAC[TAKE_DEF] THEN CONV_TAC NUM_REDUCE_CONV THEN
   REWRITE_TAC[TAKE_0];
   DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC]);;

let LENGTH_DROP = prove
 (`!n l:A list. LENGTH (DROP n l) = LENGTH l - n`,
  ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[DROP_DEF; LENGTH; SUB_0] THEN
  GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[LENGTH; SUB_0] THEN
  ASM_ARITH_TAC);;

let DROP_LENGTH_TOO_LONG = prove
 (`!l:A list n. LENGTH l <= n ==> (DROP n l = [])`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[DROP_DEF; LENGTH] THEN
  GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL
  [ARITH_TAC; DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC]);;

let HD_DROP = prove
 (`!n l:A list. n < LENGTH l ==> (HD (DROP n l) = EL n l)`,
  ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN
  LIST_INDUCT_TAC THEN REWRITE_TAC[LENGTH; CONJUNCT1 LT] THEN
  GEN_TAC THEN REWRITE_TAC[DROP_DEF; EL_CONS] THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[HD] THEN
  DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC);;

let MAP_DROP = prove
 (`!l i. MAP (f:A->B) (DROP i l) = DROP i (MAP f l)`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[DROP_DEF; MAP] THEN
  GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[MAP]);;

let MAP_FRONT = prove
 (`!ls. MAP (f:A->B) (BUTLAST ls) = BUTLAST (MAP f ls)`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[BUTLAST; MAP; MAP_EQ_NIL] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[MAP]);;

let TAKE_EQ_NIL = prove
 (`(TAKE n (l:A list) = []) <=> (n = 0) \/ (l = [])`,
  STRUCT_CASES_TAC(ISPEC `l:A list` list_CASES) THEN
  REWRITE_TAC[TAKE_DEF; NOT_CONS_NIL] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[NOT_CONS_NIL]);;

let DROP_EQ_NIL = prove
 (`!ls:A list n. DROP n ls = [] <=> LENGTH ls <= n`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[DROP_DEF; LENGTH; LE_0] THEN
  GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[NOT_CONS_NIL] THEN
  ASM_ARITH_TAC);;

let TAKE_LENGTH_ID_rwt = prove
 (`!l:A list m. (m = LENGTH l) ==> (TAKE m l = l)`,
  SIMP_TAC[TAKE_LENGTH_ID]);;

let TAKE_LENGTH_ID_rwt2 = prove
 (`!l:A list m. TAKE m l = l <=> LENGTH l <= m`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[TAKE_DEF; LENGTH; LE_0] THEN
  GEN_TAC THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[CONS_11; GSYM NOT_CONS_NIL] THEN ASM_ARITH_TAC);;

let MAP_EQ_EVERY2 = prove
 (`!(f1:A->C) (f2:B->C) l1 l2.
     (MAP f1 l1 = MAP f2 l2) <=>
     (LENGTH l1 = LENGTH l2) /\ ALL2 (\x y. f1 x = f2 y) l1 l2`,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `l2:B list` list_CASES) THEN
  ASM_REWRITE_TAC[MAP; ALL2; LENGTH; CONS_11; NOT_CONS_NIL;
                  GSYM NOT_CONS_NIL; NOT_SUC; GSYM NOT_SUC; SUC_INJ] THEN
  MESON_TAC[]);;

let EVERY2_EVERY = prove
 (`!l1 l2 (f:A->B->bool).
     ALL2 f l1 l2 <=> LENGTH l1 = LENGTH l2 /\ ALL (UNCURRY f) (ZIP l1 l2)`,
  LIST_INDUCT_TAC THEN GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `l2:B list` list_CASES) THEN
  ASM_REWRITE_TAC[ALL2; LENGTH; ZIP_def; ALL; UNCURRY_DEF; NOT_SUC;
                  GSYM NOT_SUC; SUC_INJ] THEN
  MESON_TAC[]);;

let EVERY2_LENGTH = prove
 (`!P l1 l2. ALL2 (P:A->B->bool) l1 l2 ==> (LENGTH l1 = LENGTH l2)`,
  SIMP_TAC[LIST_REL_EL_EQN]);;

(* ------------------------------------------------------------------------- *)
(* ALL_DISTINCT.                                                             *)
(* ------------------------------------------------------------------------- *)

let LISTAUX_ALL_DISTINCT_PAIRWISE = prove
 (`!l:A list. ALL_DISTINCT l <=> PAIRWISE (\x y. ~(x = y)) l`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[ALL_DISTINCT; PAIRWISE; GSYM ALL_MEM] THEN
  MESON_TAC[]);;

let LISTAUX_FILTER_EQ_NIL_MEM = prove
 (`!(x:A) l. FILTER ((=) x) l = [] <=> ~MEM x l`,
  REWRITE_TAC[FILTER_EQ_NIL; GSYM ALL_MEM] THEN MESON_TAC[]);;

let ALL_DISTINCT_FILTER = prove
 (`!l:A list. ALL_DISTINCT l <=> !x. MEM x l ==> (FILTER ((=) x) l = [x])`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[ALL_DISTINCT; MEM] THEN
  ASM_REWRITE_TAC[FILTER] THEN EQ_TAC THENL
  [STRIP_TAC THEN X_GEN_TAC `x:A` THEN
   ASM_CASES_TAC `(x:A) = h` THEN
   ASM_REWRITE_TAC[CONS_11; LISTAUX_FILTER_EQ_NIL_MEM];
   DISCH_TAC THEN
   SUBGOAL_THEN `~MEM (h:A) t` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `h:A`) THEN
    REWRITE_TAC[CONS_11; LISTAUX_FILTER_EQ_NIL_MEM];
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    SUBGOAL_THEN `~((x:A) = h)` ASSUME_TAC THENL
    [UNDISCH_TAC `~MEM (h:A) t` THEN UNDISCH_TAC `MEM (x:A) t` THEN
     MESON_TAC[];
     FIRST_X_ASSUM(MP_TAC o SPEC `x:A`) THEN ASM_REWRITE_TAC[]]]]);;

let FILTER_ALL_DISTINCT = prove
 (`!P l:A list. ALL_DISTINCT l ==> ALL_DISTINCT (FILTER P l)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[ALL_DISTINCT; FILTER] THEN
  COND_CASES_TAC THEN ASM_SIMP_TAC[ALL_DISTINCT; MEM_FILTER]);;

let ALL_DISTINCT_MAP = prove
 (`!(f:A->B) ls. ALL_DISTINCT (MAP f ls) ==> ALL_DISTINCT ls`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[ALL_DISTINCT; MAP] THEN
  ASM_MESON_TAC[MEM_MAP_f]);;

let LISTAUX_FORALL2_LT_SUC = prove
 (`!Q k. (!n1 n2. n1 < SUC k /\ n2 < SUC k ==> Q n1 n2) <=>
         Q 0 0 /\ (!j. j < k ==> Q 0 (SUC j)) /\
         (!j. j < k ==> Q (SUC j) 0) /\
         (!i j. i < k /\ j < k ==> Q (SUC i) (SUC j))`,
  REWRITE_TAC[GSYM IMP_IMP; RIGHT_FORALL_IMP_THM] THEN
  REWRITE_TAC[LISTAUX_FORALL_LT_SUC] THEN MESON_TAC[]);;

let EL_ALL_DISTINCT_EL_EQ = prove
 (`!l:A list. ALL_DISTINCT l <=>
     (!n1 n2. n1 < LENGTH l /\ n2 < LENGTH l ==>
              ((EL n1 l = EL n2 l) <=> (n1 = n2)))`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[ALL_DISTINCT; LENGTH; CONJUNCT1 LT] THEN
  ASM_REWRITE_TAC[LISTAUX_FORALL2_LT_SUC; EL; HD; TL; NOT_SUC; GSYM NOT_SUC;
                  SUC_INJ] THEN
  REWRITE_TAC[MEM_EXISTS_EL] THEN MESON_TAC[]);;

let ALL_DISTINCT_APPEND = prove
 (`!l1 l2:A list. ALL_DISTINCT (APPEND l1 l2) <=>
     (ALL_DISTINCT l1 /\ ALL_DISTINCT l2 /\ (!e. MEM e l1 ==> ~(MEM e l2)))`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[APPEND; ALL_DISTINCT; MEM; MEM_APPEND] THEN
  MESON_TAC[]);;

let ALL_DISTINCT_APPEND' = prove
 (`!l1 l2:A list. ALL_DISTINCT (APPEND l1 l2) <=>
     ALL_DISTINCT l1 /\ ALL_DISTINCT l2 /\
     DISJOINT (set_of_list l1) (set_of_list l2)`,
  REWRITE_TAC[ALL_DISTINCT_APPEND; DISJOINT; EXTENSION; IN_INTER;
              NOT_IN_EMPTY; IN_SET_OF_LIST] THEN
  MESON_TAC[]);;

let ALL_DISTINCT_ZIP = prove
 (`!(l1:A list) (l2:B list).
     ALL_DISTINCT l1 /\ (LENGTH l1 = LENGTH l2) ==> ALL_DISTINCT (ZIP l1 l2)`,
  LIST_INDUCT_TAC THEN GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `l2:B list` list_CASES) THEN
  REWRITE_TAC[ALL_DISTINCT; LENGTH; ZIP_def; NOT_SUC; GSYM NOT_SUC;
              SUC_INJ] THEN
  STRIP_TAC THEN CONJ_TAC THENL
  [DISCH_THEN(MP_TAC o MATCH_MP (ISPEC `FST:A#B->A` MEM_MAP_f)) THEN
   ASM_SIMP_TAC[MAP_FST_ZIP];
   ASM_MESON_TAC[]]);;

let ALL_DISTINCT_REVERSE = prove
 (`!l:A list. ALL_DISTINCT (REVERSE l) <=> ALL_DISTINCT l`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[REVERSE; ALL_DISTINCT_APPEND; ALL_DISTINCT; MEM;
                  MEM_REVERSE] THEN
  MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* LRC: a path of R steps, listing the elements but the last.               *)
(* ------------------------------------------------------------------------- *)

let LRC_def = new_recursive_definition list_RECURSION
  `(LRC (R:A->A->bool) [] x y <=> (x = y)) /\
   (LRC R (CONS h t) x y <=> x = h /\ ?z. R x z /\ LRC R t z y)`;;

(* ------------------------------------------------------------------------- *)
(* set (= set_of_list) and SET_TO_LIST (= list_of_set).                     *)
(* ------------------------------------------------------------------------- *)

let LIST_TO_SET_APPEND = SET_OF_LIST_APPEND;;

let SUM_MAP_MEM_bound = prove
 (`!(f:A->num) x ls. MEM x ls ==> f x <= SUM (MAP f ls)`,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[MEM; MAP; SUM] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
  [ARITH_TAC;
   FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN ASM_REWRITE_TAC[] THEN
   ARITH_TAC]);;

let LISTAUX_MAP_EQ_IMP = prove
 (`!(f:A->B) l1 l2.
     (!x y. MEM x l1 /\ MEM y l2 /\ f x = f y ==> x = y) /\
     MAP f l1 = MAP f l2 ==> l1 = l2`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `l2:A list` list_CASES) THEN
  REWRITE_TAC[MAP; NOT_CONS_NIL; GSYM NOT_CONS_NIL; CONS_11; MEM] THEN
  STRIP_TAC THEN CONJ_TAC THENL
  [ASM_MESON_TAC[]; FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[]]);;

let INJ_MAP_EQ = prove
 (`!(f:A->B) l1 l2.
     INJ f (set_of_list l1 UNION set_of_list l2) UNIV /\ MAP f l1 = MAP f l2
     ==> l1 = l2`,
  REWRITE_TAC[INJ; IN_UNION; IN_SET_OF_LIST; IN_UNIV] THEN
  MESON_TAC[LISTAUX_MAP_EQ_IMP]);;

let INJ_MAP_EQ_IFF = prove
 (`!(f:A->B) l1 l2.
     INJ f (set_of_list l1 UNION set_of_list l2) UNIV ==>
     ((MAP f l1 = MAP f l2) <=> (l1 = l2))`,
  MESON_TAC[INJ_MAP_EQ]);;

let ALL_DISTINCT_CARD_LIST_TO_SET = prove
 (`!ls:A list. ALL_DISTINCT ls ==> (CARD (set_of_list ls) = LENGTH ls)`,
  LIST_INDUCT_TAC THEN
  ASM_SIMP_TAC[ALL_DISTINCT; set_of_list; LENGTH; CARD_CLAUSES;
               FINITE_SET_OF_LIST; IN_SET_OF_LIST]);;

let LIST_TO_SET_REVERSE = prove
 (`!ls:A list. set_of_list (REVERSE ls) = set_of_list ls`,
  REWRITE_TAC[EXTENSION; IN_SET_OF_LIST; MEM_REVERSE]);;

let LIST_TO_SET_MAP = SET_OF_LIST_MAP;;

let LIST_TO_SET_FILTER = prove
 (`set_of_list (FILTER P l) = {x:A | P x} INTER set_of_list l`,
  REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM; IN_SET_OF_LIST; MEM_FILTER]);;

let SET_TO_LIST_INV = SET_OF_LIST_OF_SET;;

let MEM_SET_TO_LIST = MEM_LIST_OF_SET;;

let ALL_DISTINCT_SET_TO_LIST = prove
 (`!s:A->bool. FINITE s ==> ALL_DISTINCT (list_of_set s)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[LISTAUX_ALL_DISTINCT_PAIRWISE; GSYM HAS_SIZE_SET_OF_LIST] THEN
  ASM_SIMP_TAC[SET_OF_LIST_OF_SET; LENGTH_LIST_OF_SET; HAS_SIZE]);;

(* ------------------------------------------------------------------------- *)
(* SNOC.                                                                     *)
(* ------------------------------------------------------------------------- *)

let LISTAUX_SNOC_APPEND = prove
 (`!(x:A) l. SNOC x l = APPEND l [x]`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[SNOC; APPEND]);;

let LAST_SNOC = prove
 (`!x:A l. LAST (SNOC x l) = x`,
  REWRITE_TAC[LISTAUX_SNOC_APPEND; LAST_APPEND; LAST; NOT_CONS_NIL]);;

let FRONT_SNOC = prove
 (`!x:A l. BUTLAST (SNOC x l) = l`,
  REWRITE_TAC[LISTAUX_SNOC_APPEND; BUTLAST_APPEND; NOT_CONS_NIL; BUTLAST;
              APPEND_NIL]);;

let LIST_TO_SET_SNOC = prove
 (`set_of_list (SNOC (x:A) ls) = x INSERT set_of_list ls`,
  REWRITE_TAC[EXTENSION; IN_INSERT; IN_SET_OF_LIST; LISTAUX_SNOC_APPEND;
              MEM_APPEND; MEM] THEN
  MESON_TAC[]);;

let APPEND_SNOC = prove
 (`!l1 (x:A) l2. APPEND l1 (SNOC x l2) = SNOC x (APPEND l1 l2)`,
  REWRITE_TAC[LISTAUX_SNOC_APPEND; APPEND_ASSOC]);;

let EVERY_SNOC = prove
 (`!P (x:A) l. ALL P (SNOC x l) <=> ALL P l /\ P x`,
  REWRITE_TAC[LISTAUX_SNOC_APPEND; ALL_APPEND; ALL]);;

let MEM_SNOC = prove
 (`!(y:A) x l. MEM y (SNOC x l) <=> (y = x) \/ MEM y l`,
  REWRITE_TAC[LISTAUX_SNOC_APPEND; MEM_APPEND; MEM] THEN MESON_TAC[]);;

let SNOC_11 = prove
 (`!(x:A) y a b. (SNOC x y = SNOC a b) <=> (x = a) /\ (y = b)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[LISTAUX_SNOC_APPEND] THEN EQ_TAC THENL
  [DISCH_TAC THEN
   SUBGOAL_THEN `LENGTH (y:A list) = LENGTH (b:A list)` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o AP_TERM `LENGTH:A list->num`) THEN
    REWRITE_TAC[LENGTH_APPEND; LENGTH] THEN ARITH_TAC;
    MP_TAC(ISPECL [`y:A list`; `b:A list`] APPEND_LENGTH_EQ) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPECL [`[x:A]`; `[a:A]`]) THEN
    ASM_REWRITE_TAC[LENGTH; CONS_11] THEN MESON_TAC[]];
   STRIP_TAC THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* isPREFIX (HOL4 infix <<=).                                                *)
(* ------------------------------------------------------------------------- *)

let isPREFIX_THM = prove
 (`(([]:A list) <<= l <=> T) /\
   ((CONS (h:A) t) <<= [] <=> F) /\
   ((CONS (h1:A) t1) <<= CONS h2 t2 <=> (h1 = h2) /\ isPREFIX t1 t2)`,
  REWRITE_TAC[isPREFIX; list_CASE]);;

let isPREFIX_NILR = prove
 (`(x:A list) <<= [] <=> (x = [])`,
  STRUCT_CASES_TAC(ISPEC `x:A list` list_CASES) THEN
  REWRITE_TAC[isPREFIX; list_CASE; NOT_CONS_NIL]);;

let isPREFIX_SNOC = prove
 (`(l:A list) <<= SNOC x l`,
  SPEC_TAC(`l:A list`,`l:A list`) THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[isPREFIX; SNOC; list_CASE]);;

let isPREFIX_TRANS = prove
 (`!x y z:A list. x <<= y /\ y <<= z ==> x <<= z`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[isPREFIX] THEN
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `y:A list` list_CASES) THEN
  STRUCT_CASES_TAC(ISPEC `z:A list` list_CASES) THEN
  REWRITE_TAC[isPREFIX; list_CASE] THEN ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* PAD_LEFT, PAD_RIGHT.                                                      *)
(* ------------------------------------------------------------------------- *)

let PAD_LEFT = new_definition
  `PAD_LEFT (c:A) n s = APPEND (list_of_seq (K c) (n - LENGTH s)) s`;;

let PAD_RIGHT = new_definition
  `PAD_RIGHT (c:A) n s = APPEND s (list_of_seq (K c) (n - LENGTH s))`;;

(* ------------------------------------------------------------------------- *)
(* GENLIST (= list_of_seq).                                                  *)
(* ------------------------------------------------------------------------- *)

let EL_GENLIST = prove
 (`!(f:num->A) n x. x < n ==> (EL x (list_of_seq f n) = f x)`,
  SIMP_TAC[EL_LIST_OF_SEQ]);;

let GENLIST_ID = LIST_OF_SEQ_EQ_SELF;;

let NULL_GENLIST = prove
 (`!n (f:num->A). NULL (list_of_seq f n) <=> (n = 0)`,
  REWRITE_TAC[NULL_EQ; LIST_OF_SEQ_EQ_NIL]);;

let MEM_GENLIST = prove
 (`MEM (x:A) (list_of_seq f n) <=> ?m. m < n /\ (x = f m)`,
  REWRITE_TAC[MEM_EXISTS_EL; LENGTH_LIST_OF_SEQ] THEN
  MESON_TAC[EL_LIST_OF_SEQ]);;

let ALL_DISTINCT_GENLIST = prove
 (`ALL_DISTINCT (list_of_seq (f:num->A) n) <=>
   (!m1 m2. m1 < n /\ m2 < n /\ (f m1 = f m2) ==> (m1 = m2))`,
  REWRITE_TAC[EL_ALL_DISTINCT_EL_EQ; LENGTH_LIST_OF_SEQ] THEN
  MESON_TAC[EL_LIST_OF_SEQ]);;

let GENLIST_CONG = prove
 (`!n1 n2 (f1:num->A) f2.
     n1 = n2 /\ (!m. m < n2 ==> f1 m = f2 m)
     ==> list_of_seq f1 n1 = list_of_seq f2 n2`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[LIST_EQ; LENGTH_LIST_OF_SEQ] THEN
  ASM_SIMP_TAC[EL_LIST_OF_SEQ]);;

let GENLIST_EQ_NIL = LIST_OF_SEQ_EQ_NIL;;

let REVERSE_GENLIST = prove
 (`REVERSE (list_of_seq (f:num->A) n) = list_of_seq (\m. f (PRE n - m)) n`,
  SPEC_TAC(`n:num`,`n:num`) THEN INDUCT_TAC THENL
  [REWRITE_TAC[list_of_seq; REVERSE]; ALL_TAC] THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [CONJUNCT2 list_of_seq] THEN
  GEN_REWRITE_TAC RAND_CONV [CONJUNCT2 LIST_OF_SEQ] THEN
  ASM_REWRITE_TAC[REVERSE_APPEND; REVERSE; APPEND; PRE; SUB_0; CONS_11] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; o_THM] THEN GEN_TAC THEN
  AP_TERM_TAC THEN ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* REV, SUM_ACC (accumulator versions).                                      *)
(* ------------------------------------------------------------------------- *)

let REV_DEF = new_recursive_definition list_RECURSION
  `(REV ([]:A list) acc = acc) /\ (REV (CONS h t) acc = REV t (CONS h acc))`;;

let REV_REVERSE_LEM = prove
 (`!L1 L2:A list. REV L1 L2 = APPEND (REVERSE L1) L2`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[REV_DEF; REVERSE; APPEND; GSYM APPEND_ASSOC]);;

let SUM_ACC_DEF = new_recursive_definition list_RECURSION
  `(SUM_ACC [] acc = acc) /\ (SUM_ACC (CONS h t) acc = SUM_ACC t (h + acc))`;;

(* ------------------------------------------------------------------------- *)
(* More equations between lists.                                             *)
(* ------------------------------------------------------------------------- *)

let EXISTS_LIST = prove
 (`(?l:A list. P l) <=> P [] \/ ?h t. P (CONS h t)`,
  MESON_TAC[list_CASES]);;

let APPEND_EQ_APPEND = prove
 (`(APPEND l1 l2 = APPEND m1 m2) <=>
   (?l:A list. (l1 = APPEND m1 l) /\ (m2 = APPEND l l2)) \/
   (?l. (m1 = APPEND l1 l) /\ (l2 = APPEND l m2))`,
  SPEC_TAC(`m1:A list`,`m1:A list`) THEN SPEC_TAC(`l1:A list`,`l1:A list`) THEN
  LIST_INDUCT_TAC THEN GEN_TAC THENL
  [REWRITE_TAC[APPEND; APPEND_eq_NIL] THEN MESON_TAC[APPEND];
   STRUCT_CASES_TAC(ISPEC `m1:A list` list_CASES) THEN
   ASM_REWRITE_TAC[APPEND; CONS_11; NOT_CONS_NIL; GSYM NOT_CONS_NIL] THEN
   MESON_TAC[APPEND]]);;

let APPEND_EQ_CONS = prove
 (`(APPEND l1 l2 = CONS (h:A) t) <=>
   ((l1 = []) /\ (l2 = CONS h t)) \/ ?lt. (l1 = CONS h lt) /\ (t = APPEND lt l2)`,
  STRUCT_CASES_TAC(ISPEC `l1:A list` list_CASES) THEN
  REWRITE_TAC[APPEND; CONS_11; NOT_CONS_NIL] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* LUPDATE.                                                                  *)
(* ------------------------------------------------------------------------- *)

(* HOL4 LUPDATE_DEF (with PRE n; hol4/vocab.ml's LUPDATE_DEF has n - 1) *)
let list_LUPDATE_DEF = prove
 (`(LUPDATE (e:A) n [] = []) /\
   (LUPDATE e n (CONS x l) = if n = 0 then CONS e l else CONS x (LUPDATE e (PRE n) l))`,
  REWRITE_TAC[LUPDATE_DEF; ARITH_RULE `PRE n = n - 1`]);;

let LUPDATE_def = prove
 (`(!(e:A) n. LUPDATE e n [] = []) /\
   (!(e:A) x l. LUPDATE e 0 (CONS x l) = CONS e l) /\
   (!(e:A) n x l. LUPDATE e (SUC n) (CONS x l) = CONS x (LUPDATE e n l))`,
  REWRITE_TAC[LUPDATE_DEF; NOT_SUC; SUC_SUB1]);;

let LISTAUX_NUMERAL_BIT1_NZ = prove
 (`!n. ~(NUMERAL (BIT1 n) = 0)`,
  GEN_TAC THEN GEN_REWRITE_TAC (RAND_CONV o LAND_CONV) [NUMERAL] THEN
  REWRITE_TAC[BIT1; NOT_SUC]);;

(* HOL4: LUPDATE_compute (numLib.SUC_RULE LUPDATE_def), for binary numerals *)
let LUPDATE_compute = prove
 (`(!(e:A) n. LUPDATE e n [] = []) /\
   (!(e:A) x l. LUPDATE e 0 (CONS x l) = CONS e l) /\
   (!(e:A) n x l. LUPDATE e (NUMERAL (BIT1 n)) (CONS x l) =
                  CONS x (LUPDATE e (NUMERAL (BIT1 n) - 1) l)) /\
   (!(e:A) n x l. LUPDATE e (NUMERAL (BIT0 n)) (CONS x l) =
                  if NUMERAL (BIT0 n) = 0 then CONS e l
                  else CONS x (LUPDATE e (NUMERAL (BIT0 n) - 1) l))`,
  REWRITE_TAC[LUPDATE_DEF; LISTAUX_NUMERAL_BIT1_NZ]);;

let LENGTH_LUPDATE = prove
 (`!(x:A) n ys. LENGTH (LUPDATE x n ys) = LENGTH ys`,
  GEN_TAC THEN ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[LUPDATE_DEF; LENGTH] THEN
  GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[LENGTH]);;

let EL_LUPDATE = prove
 (`!ys (x:A) i k.
     EL i (LUPDATE x k ys) = if (i = k) /\ k < LENGTH ys then x else EL i ys`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[LUPDATE_DEF; LENGTH; CONJUNCT1 LT] THEN
  X_GEN_TAC `x:A` THEN INDUCT_TAC THEN X_GEN_TAC `k:num` THEN
  ASM_CASES_TAC `k = 0` THEN ASM_REWRITE_TAC[EL; HD; TL; LT_0; NOT_SUC] THEN
  AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN ASM_ARITH_TAC);;

let LUPDATE_SEM = prove
 (`(!(e:A) n l. LENGTH (LUPDATE e n l) = LENGTH l) /\
   (!(e:A) n l p.
      p < LENGTH l ==> (EL p (LUPDATE e n l) = if p = n then e else EL p l))`,
  REWRITE_TAC[LENGTH_LUPDATE; EL_LUPDATE] THEN REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `p:num = n` THEN ASM_MESON_TAC[]);;

let LUPDATE_LENGTH = prove
 (`!xs (x:A) y ys.
     LUPDATE x (LENGTH xs) (APPEND xs (CONS y ys)) = APPEND xs (CONS x ys)`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[LENGTH; APPEND; LUPDATE_DEF; NOT_SUC; SUC_SUB1]);;

let MEM_LUPDATE_E = prove
 (`!l (x:A) y i. MEM x (LUPDATE y i l) ==> (x = y) \/ MEM x l`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[LUPDATE_DEF; MEM] THEN
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[MEM] THEN
  ASM_MESON_TAC[]);;

let MEM_LUPDATE = prove
 (`!l (x:A) y i. MEM x (LUPDATE y i l) <=>
     i < LENGTH l /\ (x = y) \/
     ?j. j < LENGTH l /\ ~(i = j) /\ (EL j l = x)`,
  REWRITE_TAC[MEM_EXISTS_EL; LENGTH_LUPDATE; EL_LUPDATE] THEN
  MESON_TAC[]);;

let LUPDATE_MAP = prove
 (`!(x:A) n l (f:A->B). MAP f (LUPDATE x n l) = LUPDATE (f x) n (MAP f l)`,
  GEN_TAC THEN ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[LUPDATE_DEF; MAP] THEN
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[MAP]);;

let LUPDATE_NIL = prove
 (`!xs n (x:A). (LUPDATE x n xs = []) <=> (xs = [])`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[LUPDATE_DEF; NOT_CONS_NIL] THEN
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[NOT_CONS_NIL]);;

(* ------------------------------------------------------------------------- *)
(* splitAtPki.                                                               *)
(* ------------------------------------------------------------------------- *)

let splitAtPki_def = new_recursive_definition list_RECURSION
  `(splitAtPki (P:num->A->bool) (k:A list->A list->B) [] = k [] []) /\
   (splitAtPki P k (CONS h t) =
      if P 0 h then k [] (CONS h t)
      else splitAtPki (P o SUC) (\p s. k (CONS h p) s) t)`;;

let LISTAUX_OLEAST_0 = prove
 (`!Q. Q 0 ==> (OLEAST) Q = SOME 0`,
  GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[OLEAST_DEF] THEN
  COND_CASES_TAC THENL [ALL_TAC; ASM_MESON_TAC[]] THEN
  REWRITE_TAC[option_INJ] THEN MATCH_MP_TAC MINIMAL_UNIQUE THEN
  ASM_REWRITE_TAC[CONJUNCT1 LT]);;

let LISTAUX_OLEAST_SUC = prove
 (`!Q. ~Q 0 ==> (OLEAST) Q = OPTION_MAP SUC ((OLEAST) (\i. Q (SUC i)))`,
  GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[OLEAST_DEF] THEN
  SUBGOAL_THEN `(?n. (Q:num->bool) n) <=> (?n. Q (SUC n))` SUBST1_TAC THENL
  [ASM_MESON_TAC[num_CASES]; ALL_TAC] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[OPTION_MAP_DEF; option_INJ] THEN
  FIRST_ASSUM(MP_TAC o BETA_RULE o GEN_REWRITE_RULE I [MINIMAL]) THEN
  ABBREV_TAC `m = minimal n. (Q:num->bool) (SUC n)` THEN
  STRIP_TAC THEN MATCH_MP_TAC MINIMAL_UNIQUE THEN
  ASM_REWRITE_TAC[LISTAUX_FORALL_LT_SUC] THEN ASM_MESON_TAC[]);;

let splitAtPki_EQN = prove
 (`splitAtPki (P:num->A->bool) (k:A list->A list->B) l =
   option_CASE (OLEAST i. i < LENGTH l /\ P i (EL i l)) (k l [])
               (\i. k (TAKE i l) (DROP i l))`,
  MAP_EVERY (fun t -> SPEC_TAC(t,t))
    [`P:num->A->bool`; `k:A list->A list->B`; `l:A list`] THEN
  LIST_INDUCT_TAC THEN REWRITE_TAC[splitAtPki_def] THENL
  [REWRITE_TAC[LENGTH; CONJUNCT1 LT; OLEAST_DEF; option_CASE]; ALL_TAC] THEN
  REPEAT GEN_TAC THEN COND_CASES_TAC THENL
  [MP_TAC(ISPEC `\i. i < LENGTH (CONS (h:A) t) /\
                     (P:num->A->bool) i (EL i (CONS h t))`
                LISTAUX_OLEAST_0) THEN
   ASM_REWRITE_TAC[LENGTH; LT_0; EL; HD] THEN DISCH_THEN SUBST1_TAC THEN
   REWRITE_TAC[option_CASE; TAKE_0; DROP_0];
   MP_TAC(ISPEC `\i. i < LENGTH (CONS (h:A) t) /\
                     (P:num->A->bool) i (EL i (CONS h t))`
                LISTAUX_OLEAST_SUC) THEN
   ASM_REWRITE_TAC[LENGTH; LT_0; EL; HD; TL; LT_SUC; o_THM] THEN
   DISCH_THEN SUBST1_TAC THEN
   SPEC_TAC(`OLEAST i. i < LENGTH (t:A list) /\
                       (P:num->A->bool) (SUC i) (EL i t)`,
            `x:num option`) THEN
   MATCH_MP_TAC option_INDUCT THEN
   REWRITE_TAC[OPTION_MAP_DEF; option_CASE; TAKE_DEF; DROP_DEF; NOT_SUC;
               SUC_SUB1]]);;

let splitAtPki_RAND = prove
 (`(f:B->C) (splitAtPki (P:num->A->bool) (k:A list->A list->B) l) =
   splitAtPki P ((o) ((o) f) k) l`,
  REWRITE_TAC[splitAtPki_EQN] THEN
  SPEC_TAC(`OLEAST i. i < LENGTH (l:A list) /\ (P:num->A->bool) i (EL i l)`,
           `x:num option`) THEN
  MATCH_MP_TAC option_INDUCT THEN REWRITE_TAC[option_CASE; o_THM]);;

let splitAtPki_MAP = prove
 (`splitAtPki (P:num->B->bool) (k:B list->B list->C) (MAP (f:A->B) l) =
   splitAtPki (flip ((o) (o) P) f) (flip ((o) o k o MAP f) (MAP f)) l`,
  REWRITE_TAC[splitAtPki_EQN; LENGTH_MAP] THEN
  SUBGOAL_THEN
   `(\i. i < LENGTH (l:A list) /\ (P:num->B->bool) i (EL i (MAP (f:A->B) l))) =
    (\i. i < LENGTH l /\ flip ((o) (o) P) f i (EL i l))`
   SUBST1_TAC THENL
  [REWRITE_TAC[FUN_EQ_THM; flip_DEF; o_THM] THEN MESON_TAC[EL_MAP];
   ALL_TAC] THEN
  SPEC_TAC(`OLEAST i. i < LENGTH (l:A list) /\
                      flip ((o) (o) (P:num->B->bool)) (f:A->B) i (EL i l)`,
           `x:num option`) THEN
  MATCH_MP_TAC option_INDUCT THEN
  REWRITE_TAC[option_CASE; flip_DEF; o_THM; MAP; MAP_TAKE; MAP_DROP]);;

let splitAtPki_change_predicate = prove
 (`(!i. i < LENGTH l ==> ((P1:num->A->bool) i (EL i l) <=> P2 i (EL i l)))
   ==> (splitAtPki P1 (k:A list->A list->B) l = splitAtPki P2 k l)`,
  REWRITE_TAC[splitAtPki_EQN] THEN DISCH_TAC THEN
  AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM] THEN ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* LLEX and nub.                                                             *)
(* ------------------------------------------------------------------------- *)

let LLEX_def = new_recursive_definition list_RECURSION
  `(LLEX (R:A->A->bool) [] l2 <=> ~(l2 = [])) /\
   (LLEX R (CONS h1 t1) l2 <=>
      list_CASE l2 F
        (\h2 t2. if R h1 h2 then T else if h1 = h2 then LLEX R t1 t2 else F))`;;

let LLEX_NIL2 = prove
 (`~LLEX (R:A->A->bool) l []`,
  STRUCT_CASES_TAC(ISPEC `l:A list` list_CASES) THEN
  REWRITE_TAC[LLEX_def; list_CASE]);;

let nub_def = nub_DEF;;

let nub_NIL = CONJUNCT1 nub_DEF;;

let LISTAUX_MEM_NUB = prove
 (`!l (x:A). MEM x (nub l) <=> MEM x l`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[nub_DEF; MEM] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[MEM] THEN ASM_MESON_TAC[]);;

let nub_set = prove
 (`!l:A list. set_of_list (nub l) = set_of_list l`,
  REWRITE_TAC[EXTENSION; IN_SET_OF_LIST; LISTAUX_MEM_NUB]);;

let all_distinct_nub = prove
 (`!l:A list. ALL_DISTINCT (nub l)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[nub_DEF; ALL_DISTINCT] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[ALL_DISTINCT; LISTAUX_MEM_NUB]);;

let nub_EQ0 = prove
 (`nub (l:A list) = [] <=> l = []`,
  SPEC_TAC(`l:A list`,`l:A list`) THEN
  LIST_INDUCT_TAC THEN REWRITE_TAC[nub_DEF; NOT_CONS_NIL] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[NOT_CONS_NIL] THEN
  ASM_MESON_TAC[MEM]);;

(* ------------------------------------------------------------------------- *)
(* More about LIST_REL (EVERY2), REVERSE, GENLIST, FLAT.                     *)
(* ------------------------------------------------------------------------- *)

let LIST_TO_SET_FLAT = prove
 (`!ls:(A list) list.
     set_of_list (FLAT ls) = UNIONS (set_of_list (MAP set_of_list ls))`,
  REWRITE_TAC[EXTENSION; IN_UNIONS; IN_SET_OF_LIST; MEM_FLAT; MEM_MAP] THEN
  MESON_TAC[IN_SET_OF_LIST]);;

let LIST_REL_APPEND_suff = prove
 (`ALL2 (R:A->B->bool) l1 l2 /\ ALL2 R l3 l4 ==>
   ALL2 R (APPEND l1 l3) (APPEND l2 l4)`,
  SPEC_TAC(`l2:B list`,`l2:B list`) THEN SPEC_TAC(`l1:A list`,`l1:A list`) THEN
  LIST_INDUCT_TAC THEN GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `l2:B list` list_CASES) THEN
  REWRITE_TAC[ALL2; APPEND] THEN ASM_MESON_TAC[]);;

let EVERY2_REVERSE = prove
 (`!R l1 l2. ALL2 (R:A->B->bool) l1 l2 ==> ALL2 R (REVERSE l1) (REVERSE l2)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `l2:B list` list_CASES) THEN
  REWRITE_TAC[ALL2; REVERSE] THEN STRIP_TAC THEN
  MATCH_MP_TAC LIST_REL_APPEND_suff THEN ASM_SIMP_TAC[ALL2]);;

let LIST_REL_REVERSE = EVERY2_REVERSE;;

let GENLIST_EL = prove
 (`!ls (f:num->A) n. (n = LENGTH ls) /\ (!i. i < n ==> (f i = EL i ls)) ==>
     (list_of_seq f n = ls)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[LIST_EQ; LENGTH_LIST_OF_SEQ] THEN
  ASM_SIMP_TAC[EL_LIST_OF_SEQ]);;

let EVERY2_trans = prove
 (`(!x y z. R x y /\ R y z ==> R x z) ==>
   !x y z. ALL2 (R:A->A->bool) x y /\ ALL2 R y z ==> ALL2 R x z`,
  DISCH_TAC THEN LIST_INDUCT_TAC THEN REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `y:A list` list_CASES) THEN
  STRUCT_CASES_TAC(ISPEC `z:A list` list_CASES) THEN
  REWRITE_TAC[ALL2] THEN ASM_MESON_TAC[]);;

let EVERY2_sym = prove
 (`(!x y. R1 x y ==> R2 y x) ==>
   !x y. ALL2 (R1:A->B->bool) x y ==> ALL2 (R2:B->A->bool) y x`,
  DISCH_TAC THEN LIST_INDUCT_TAC THEN GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `y:B list` list_CASES) THEN
  REWRITE_TAC[ALL2] THEN ASM_MESON_TAC[]);;

let EVERY2_LUPDATE_same = prove
 (`!P l1 l2 v1 v2 n.
     P v1 v2 /\ ALL2 (P:A->B->bool) l1 l2 ==>
     ALL2 P (LUPDATE v1 n l1) (LUPDATE v2 n l2)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `l2:B list` list_CASES) THEN
  REWRITE_TAC[ALL2; LUPDATE_DEF] THEN REPEAT GEN_TAC THEN
  COND_CASES_TAC THEN ASM_SIMP_TAC[ALL2]);;

let EVERY2_refl = prove
 (`(!x. MEM x ls ==> R x x) ==> (ALL2 (R:A->A->bool) ls ls)`,
  REWRITE_TAC[ALL2_ALL; GSYM ALL_MEM]);;

let EVERY2_THM = prove
 (`(!P ys. ALL2 (P:A->B->bool) [] ys <=> (ys = [])) /\
   (!P yys x xs. ALL2 (P:A->B->bool) (CONS x xs) yys <=>
      ?y ys. (yys = CONS y ys) /\ (P x y) /\ (ALL2 P xs ys)) /\
   (!P xs. ALL2 (P:A->B->bool) xs [] <=> (xs = [])) /\
   (!P xxs y ys. ALL2 (P:A->B->bool) xxs (CONS y ys) <=>
      ?x xs. (xxs = CONS x xs) /\ (P x y) /\ (ALL2 P xs ys))`,
  REWRITE_TAC[LIST_REL_NIL; LIST_REL_CONS1; LIST_REL_CONS2]);;

let LIST_REL_trans = prove
 (`!l1 l2 l3.
     (!n. n < LENGTH l1 /\ R (EL n l1) (EL n l2) /\ R (EL n l2) (EL n l3)
          ==> R (EL n l1) (EL n l3)) /\
     ALL2 (R:A->A->bool) l1 l2 /\ ALL2 R l2 l3 ==> ALL2 R l1 l3`,
  REWRITE_TAC[LIST_REL_EL_EQN] THEN MESON_TAC[]);;

let LIST_REL_eq = prove
 (`ALL2 (=) = ((=):A list->A list->bool)`,
  REWRITE_TAC[FUN_EQ_THM] THEN LIST_INDUCT_TAC THEN GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `x':A list` list_CASES) THEN
  ASM_REWRITE_TAC[ALL2; CONS_11; NOT_CONS_NIL; GSYM NOT_CONS_NIL]);;

let LIST_REL_MEM_IMP = prove
 (`!xs ys (P:A->B->bool) x.
     ALL2 P xs ys /\ MEM x xs ==> ?y. MEM y ys /\ P x y`,
  REWRITE_TAC[LIST_REL_EL_EQN; MEM_EXISTS_EL] THEN MESON_TAC[]);;

let LIST_REL_SNOC = prove
 (`(ALL2 (R:A->B->bool) (SNOC x xs) yys <=>
      ?y ys. (yys = SNOC y ys) /\ ALL2 R xs ys /\ R x y) /\
   (ALL2 R xxs (SNOC y ys) <=>
      ?x xs. (xxs = SNOC x xs) /\ ALL2 R xs ys /\ R x y)`,
  REWRITE_TAC[LISTAUX_SNOC_APPEND; LIST_REL_SPLIT1; LIST_REL_SPLIT2;
              LIST_REL_CONS1; LIST_REL_CONS2; LIST_REL_NIL] THEN
  MESON_TAC[]);;

let LIST_REL_APPEND_IMP = prove
 (`!xs ys xs1 ys1.
     ALL2 (P:A->B->bool) (APPEND xs xs1) (APPEND ys ys1) /\
     (LENGTH xs = LENGTH ys) ==> ALL2 P xs ys /\ ALL2 P xs1 ys1`,
  LIST_INDUCT_TAC THEN GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `ys:B list` list_CASES) THEN
  REWRITE_TAC[APPEND; ALL2; LENGTH; NOT_SUC; GSYM NOT_SUC; SUC_INJ] THEN
  ASM_MESON_TAC[]);;

let LIST_REL_APPEND = prove
 (`ALL2 (R:A->B->bool) l1 l2 /\ ALL2 R l3 l4 <=>
   ALL2 R (APPEND l1 l3) (APPEND l2 l4) /\
   (LENGTH l1 = LENGTH l2) /\ (LENGTH l3 = LENGTH l4)`,
  MESON_TAC[LIST_REL_APPEND_suff; LIST_REL_LENGTH; LIST_REL_APPEND_IMP]);;

let LIST_REL_APPEND_EQ = prove
 (`(LENGTH (x1:A list) = LENGTH (x2:B list)) ==>
   (ALL2 (R:A->B->bool) (APPEND x1 y1) (APPEND x2 y2) <=>
    ALL2 R x1 x2 /\ ALL2 R y1 y2)`,
  MESON_TAC[LIST_REL_APPEND_suff; LIST_REL_APPEND_IMP]);;

let LIST_REL_MAP_inv_image = prove
 (`ALL2 (R:B->B->bool) (MAP (f:A->B) l1) (MAP f l2) <=>
   ALL2 (inv_image R f) l1 l2`,
  REWRITE_TAC[ALL2_MAP2; inv_image]);;

let SWAP_REVERSE = prove
 (`!l1 l2:A list. (l1 = REVERSE l2) <=> (l2 = REVERSE l1)`,
  MESON_TAC[REVERSE_REVERSE]);;

let SWAP_REVERSE_SYM = prove
 (`!l1 l2:A list. (REVERSE l1 = l2) <=> (l1 = REVERSE l2)`,
  MESON_TAC[REVERSE_REVERSE]);;

let BIGUNION_IMAGE_set_SUBSET = prove
 (`(UNIONS (IMAGE (f:A->B->bool) (set_of_list ls)) SUBSET s) <=>
   (!x. MEM x ls ==> f x SUBSET s)`,
  REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_IMAGE; IN_SET_OF_LIST]);;

let GENLIST_EL_MAP = prove
 (`!(f:A->B) ls. list_of_seq (\n. f (EL n ls)) (LENGTH ls) = MAP f ls`,
  REWRITE_TAC[LIST_EQ; LENGTH_LIST_OF_SEQ; LENGTH_MAP] THEN
  SIMP_TAC[EL_LIST_OF_SEQ; EL_MAP]);;

let LIST_EQ_MAP_PAIR = prove
 (`!l1 l2:(A#B) list.
     (MAP FST l1 = MAP FST l2) /\ (MAP SND l1 = MAP SND l2) ==> (l1 = l2)`,
  LIST_INDUCT_TAC THEN GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `l2:(A#B) list` list_CASES) THEN
  REWRITE_TAC[MAP; CONS_11; NOT_CONS_NIL; GSYM NOT_CONS_NIL] THEN
  ASM_MESON_TAC[PAIR]);;

let TAKE_SUM = prove
 (`!n m l:A list. TAKE (n + m) l = APPEND (TAKE n l) (TAKE m (DROP n l))`,
  INDUCT_TAC THEN REWRITE_TAC[ADD_CLAUSES; TAKE_0; DROP_0; APPEND] THEN
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[TAKE_DEF; DROP_DEF; APPEND; NOT_SUC; SUC_SUB1]);;

let FLAT_EQ_NIL = prove
 (`!ls:(A list) list. (FLAT ls = []) <=> (ALL ((=) []) ls)`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[FLAT; ALL; APPEND_EQ_NIL] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN MATCH_ACCEPT_TAC EQ_SYM_EQ);;

let ALL_DISTINCT_MAP_INJ = prove
 (`!ls (f:A->B).
     (!x y. MEM x ls /\ MEM y ls /\ (f x = f y) ==> (x = y)) /\
     ALL_DISTINCT ls ==> ALL_DISTINCT (MAP f ls)`,
  REWRITE_TAC[LISTAUX_ALL_DISTINCT_PAIRWISE; PAIRWISE_MAP] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC PAIRWISE_IMPLIES THEN
  EXISTS_TAC `\x y:A. ~(x = y)` THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

let LIST_TO_SET_GENLIST = prove
 (`!(f:num->A) n. set_of_list (list_of_seq f n) = IMAGE f (count n)`,
  REWRITE_TAC[EXTENSION; IN_SET_OF_LIST; MEM_GENLIST; IN_IMAGE; count_DEF;
              IN_ELIM_THM] THEN
  MESON_TAC[]);;

(* HOL4 MEM_ZIP_MEM_MAP has ZIP ps for a pair ps; HOL Light's ZIP is curried *)
let MEM_ZIP_MEM_MAP = prove
 (`(LENGTH (FST (ps:A list#B list)) = LENGTH (SND ps)) /\
   MEM (p:A#B) (ZIP (FST ps) (SND ps))
   ==> MEM (FST p) (FST ps) /\ MEM (SND p) (SND ps)`,
  STRIP_TAC THEN CONJ_TAC THENL
  [MP_TAC(ISPECL [`FST:A#B->A`; `ZIP (FST (ps:A list#B list)) (SND ps)`;
                  `p:A#B`] MEM_MAP_f);
   MP_TAC(ISPECL [`SND:A#B->B`; `ZIP (FST (ps:A list#B list)) (SND ps)`;
                  `p:A#B`] MEM_MAP_f)] THEN
  ASM_SIMP_TAC[MAP_FST_ZIP; MAP_SND_ZIP]);;

let EVERY2_MAP = prove
 (`(ALL2 (P:B->C->bool) (MAP (f:A->B) l1) l2 <=>
    ALL2 (\x y. P (f x) y) l1 l2) /\
   (ALL2 (Q:A->D->bool) l1 (MAP (g:C->D) l2) <=>
    ALL2 (\x y. Q x (g y)) l1 l2)`,
  REWRITE_TAC[LIST_REL_MAP1; LIST_REL_MAP2; o_DEF; ETA_AX]);;

let exists_list_GENLIST = prove
 (`(?ls:A list. P ls) <=> (?n f. P (list_of_seq f n))`,
  MESON_TAC[LIST_OF_SEQ_EQ_SELF]);;

let EVERY2_MEM_MONO = prove
 (`!P Q l1 l2.
     (!x. MEM x (ZIP l1 l2) /\ UNCURRY P x ==> UNCURRY Q x) /\
     ALL2 (P:A->B->bool) l1 l2 ==> ALL2 (Q:A->B->bool) l1 l2`,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `l2:B list` list_CASES) THEN
  REWRITE_TAC[ALL2; ZIP_def; MEM] THEN STRIP_TAC THEN CONJ_TAC THENL
  [FIRST_X_ASSUM(MP_TAC o SPEC `(h:A,h':B)`) THEN
   ASM_REWRITE_TAC[UNCURRY_DEF];
   FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[]]);;

let mem_exists_set = prove
 (`!(x:A) (y:B) l. MEM (x,y) l ==> ?z. (x = FST z) /\ z IN set_of_list l`,
  REWRITE_TAC[IN_SET_OF_LIST] THEN MESON_TAC[FST]);;

let every_zip_snd = prove
 (`!(l1:A list) (l2:B list) P.
     (LENGTH l1 = LENGTH l2) ==>
     (ALL (\x. P (SND x)) (ZIP l1 l2) <=> ALL P l2)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(fun th -> GEN_REWRITE_TAC (RAND_CONV o RAND_CONV)
    [GSYM(MATCH_MP MAP_SND_ZIP th)]) THEN
  REWRITE_TAC[ALL_MAP; o_DEF]);;

let every_zip_fst = prove
 (`!(l1:A list) (l2:B list) P.
     (LENGTH l1 = LENGTH l2) ==>
     (ALL (\x. P (FST x)) (ZIP l1 l2) <=> ALL P l1)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(fun th -> GEN_REWRITE_TAC (RAND_CONV o RAND_CONV)
    [GSYM(MATCH_MP MAP_FST_ZIP th)]) THEN
  REWRITE_TAC[ALL_MAP; o_DEF]);;

let el_append3 = prove
 (`!l1 (x:A) l2. EL (LENGTH l1) (APPEND (APPEND l1 [x]) l2) = x`,
  REWRITE_TAC[GSYM APPEND_ASSOC] THEN
  REWRITE_TAC[EL_APPEND; LT_REFL; SUB_REFL; APPEND; EL; HD; LENGTH; LT_0]);;

let lupdate_append2 = prove
 (`!v l1 (x:A) l2 (l3:A list).
     LUPDATE v (LENGTH l1) (APPEND (APPEND l1 [x]) l2) =
     APPEND (APPEND l1 [v]) l2`,
  REWRITE_TAC[GSYM APPEND_ASSOC; APPEND; LUPDATE_LENGTH]);;

let NOT_NIL_EQ_LENGTH_NOT_0 = prove
 (`~(x = []) <=> (0 < LENGTH (x:A list))`,
  STRUCT_CASES_TAC(ISPEC `x:A list` list_CASES) THEN
  REWRITE_TAC[NOT_CONS_NIL; LENGTH; LT_0; LT_REFL]);;

let IMP_EVERY_LUPDATE = prove
 (`!xs h i. P h /\ ALL P xs ==> ALL (P:A->bool) (LUPDATE h i xs)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[LUPDATE_DEF; ALL] THEN
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN ASM_SIMP_TAC[ALL]);;

let MAP_APPEND_MAP_EQ = prove
 (`!xs ys.
     ((APPEND (MAP (f1:A->C) xs) (MAP (g1:B->C) ys)) =
      (APPEND (MAP f2 xs) (MAP g2 ys))) <=>
     (MAP f1 xs = MAP f2 xs) /\ (MAP g1 ys = MAP g2 ys)`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`MAP (f1:A->C) xs`; `MAP (f2:A->C) xs`] APPEND_LENGTH_EQ) THEN
  REWRITE_TAC[LENGTH_MAP] THEN
  DISCH_THEN(MP_TAC o SPECL [`MAP (g1:B->C) ys`; `MAP (g2:B->C) ys`]) THEN
  REWRITE_TAC[LENGTH_MAP]);;

let ZIP_EQ_NIL = prove
 (`!(l1:A list) (l2:B list). (LENGTH l1 = LENGTH l2) ==>
     ((ZIP l1 l2 = []) <=> ((l1 = []) /\ (l2 = [])))`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `l1:A list` list_CASES) THEN
  STRUCT_CASES_TAC(ISPEC `l2:B list` list_CASES) THEN
  REWRITE_TAC[ZIP_def; LENGTH; NOT_CONS_NIL; NOT_SUC; GSYM NOT_SUC]);;

let LUPDATE_SAME = prove
 (`!n ls:A list. n < LENGTH ls ==> (LUPDATE (EL n ls) n ls = ls)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[LIST_EQ; LENGTH_LUPDATE; EL_LUPDATE] THEN
  REPEAT STRIP_TAC THEN COND_CASES_TAC THEN ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* OPT_MMAP and oEL.                                                         *)
(* ------------------------------------------------------------------------- *)

let OPT_MMAP_def = OPT_MMAP_DEF;;

let oEL_def = oEL_DEF;;

let oEL_THM = prove
 (`!xs (n:num). oEL n xs:A option =
     if n < LENGTH xs then SOME (EL n xs) else NONE`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[oEL_DEF; LENGTH; CONJUNCT1 LT] THEN
  GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[LT_0; EL; HD; EL_CONS] THEN
  AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN ASM_ARITH_TAC);;

let oEL_EQ_EL = prove
 (`!xs n (y:A). (oEL n xs = SOME y) <=> n < LENGTH xs /\ (y = EL n xs)`,
  REWRITE_TAC[oEL_THM] THEN REPEAT GEN_TAC THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[option_INJ; option_DISTINCT] THEN MESON_TAC[]);;

let LISTAUX_EL_DROP = prove
 (`!(l:A list) m n. m + n < LENGTH l ==> EL n (DROP m l) = EL (m + n) l`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[LENGTH; CONJUNCT1 LT] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[DROP_DEF] THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[ADD_CLAUSES] THEN DISCH_TAC THEN
  SUBGOAL_THEN `m + n = SUC ((m - 1) + n)` SUBST1_TAC THENL
  [ASM_ARITH_TAC; REWRITE_TAC[EL; TL]] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC);;

let LISTAUX_EL_TAKE = prove
 (`!(l:A list) m n. n < m ==> EL n (TAKE m l) = EL n l`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[TAKE_DEF] THEN
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[CONJUNCT1 LT] THEN
  DISCH_TAC THEN REWRITE_TAC[EL_CONS] THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC);;

let oEL_DROP = prove
 (`oEL n (DROP m xs) = oEL (m + n) (xs:A list)`,
  REWRITE_TAC[oEL_THM; LENGTH_DROP] THEN
  ASM_CASES_TAC `m + n < LENGTH (xs:A list)` THEN
  ASM_SIMP_TAC[LISTAUX_EL_DROP; ARITH_RULE `n < l - m <=> m + n < l`]);;

let oEL_TAKE_E = prove
 (`(oEL n (TAKE m xs) = SOME x) ==> (oEL n xs = SOME (x:A))`,
  REWRITE_TAC[oEL_EQ_EL] THEN STRIP_TAC THEN
  SUBGOAL_THEN `n < m /\ n < LENGTH (xs:A list)` STRIP_ASSUME_TAC THENL
  [UNDISCH_TAC `n < LENGTH (TAKE m (xs:A list))` THEN
   REWRITE_TAC[LENGTH_TAKE_EQ] THEN COND_CASES_TAC THEN ASM_ARITH_TAC;
   ASM_SIMP_TAC[LISTAUX_EL_TAKE]]);;

let oEL_LUPDATE = prove
 (`!xs i n (x:A). oEL n (LUPDATE x i xs) =
     if ~(i = n) then oEL n xs else if i < LENGTH xs then SOME x else NONE`,
  REWRITE_TAC[oEL_THM; LENGTH_LUPDATE; EL_LUPDATE] THEN REPEAT GEN_TAC THEN
  ASM_CASES_TAC `i:num = n` THEN ASM_REWRITE_TAC[] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* LIST_REL_O, with relation composition (HOL4 relation$O: (R1 O R2) x z    *)
(* <=> ?y. R2 x y /\ R1 y z) written out.                                    *)
(* ------------------------------------------------------------------------- *)

let LIST_REL_O = prove
 (`!(R1:B->C->bool) (R2:A->B->bool).
     ALL2 (\x z. ?y. R2 x y /\ R1 y z) =
     (\x z. ?y. ALL2 R2 x y /\ ALL2 R1 y z)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN
  LIST_INDUCT_TAC THEN X_GEN_TAC `z:C list` THEN
  STRUCT_CASES_TAC(ISPEC `z:C list` list_CASES) THEN
  ASM_REWRITE_TAC[ALL2; LIST_REL_NIL] THENL
  [MESON_TAC[]; MESON_TAC[ALL2]; MESON_TAC[ALL2]; ALL_TAC] THEN
  EQ_TAC THENL
  [DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `y0:B`) (X_CHOOSE_TAC `ys:B list`)) THEN
   EXISTS_TAC `CONS (y0:B) ys` THEN ASM_REWRITE_TAC[ALL2];
   DISCH_THEN(X_CHOOSE_THEN `y:B list` MP_TAC) THEN
   STRUCT_CASES_TAC(ISPEC `y:B list` list_CASES) THEN REWRITE_TAC[ALL2] THEN
   MESON_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Further HOL4 [simp] and export_rewrites lemmas of listTheory.             *)
(* ------------------------------------------------------------------------- *)

let LIST_TO_SET = set_of_list;;

let MAP_ID_I = MAP_I;;

let FINITE_LIST_TO_SET = FINITE_SET_OF_LIST;;

let SET_TO_LIST_EMPTY = LIST_OF_SET_EMPTY;;

let SET_TO_LIST_SING = LIST_OF_SET_SING;;

let oHD_thm = oHD_DEF;;

let LIST_TO_SET_EQ_EMPTY = prove
 (`((set_of_list (l:A list) = {}) <=> (l = [])) /\
   (({} = set_of_list l) <=> (l = []))`,
  MESON_TAC[SET_OF_LIST_EQ_EMPTY]);;

let CONS_ACYCLIC = prove
 (`!l (x:A). ~(l = CONS x l) /\ ~(CONS x l = l)`,
  REPEAT GEN_TAC THEN CONJ_TAC THEN
  DISCH_THEN(MP_TAC o AP_TERM `LENGTH:A list->num`) THEN
  REWRITE_TAC[LENGTH] THEN ARITH_TAC);;

let EL_restricted = prove
 (`(EL 0 = (HD:A list->A)) /\ (EL (SUC n) (CONS (l:A) ls) = EL n ls)`,
  REWRITE_TAC[FUN_EQ_THM; EL; TL]);;

(* HOL4 EL_simp_restricted, for HOL Light's binary numerals *)
let EL_simp_restricted = prove
 (`(EL (NUMERAL (BIT1 n)) (CONS (l:A) ls) = EL (PRE (NUMERAL (BIT1 n))) ls) /\
   (EL (NUMERAL (BIT0 n)) (CONS (l:A) ls) =
      if NUMERAL (BIT0 n) = 0 then l else EL (NUMERAL (BIT0 n) - 1) ls)`,
  REWRITE_TAC[EL_CONS; LISTAUX_NUMERAL_BIT1_NZ; ARITH_RULE `PRE n = n - 1`]);;

let NULL_MAP = prove
 (`NULL (MAP (f:A->B) ls) <=> NULL ls`,
  REWRITE_TAC[NULL_EQ; MAP_EQ_NIL]);;

let NULL_APPEND = prove
 (`NULL (APPEND l1 l2) <=> NULL l1 /\ NULL (l2:A list)`,
  REWRITE_TAC[NULL_EQ; APPEND_EQ_NIL]);;

let LIST_EXISTS_SIMP = prove
 (`!c l:A list. EX (\x. c) l <=> ~(l = []) /\ c`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[EX; NOT_CONS_NIL] THEN
  CONV_TAC TAUT);;

let EVERY_SIMP = prove
 (`!c l:A list. ALL (\x. c) l <=> l = [] \/ c`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[ALL; NOT_CONS_NIL] THEN
  CONV_TAC TAUT);;

let EXISTS_APPEND = prove
 (`!P (l1:A list) l2. EX P (APPEND l1 l2) <=> EX P l1 \/ EX P l2`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[APPEND; EX; DISJ_ASSOC]);;

let REVERSE_EQ_SING = prove
 (`(REVERSE l = [e:A]) <=> (l = [e])`,
  REWRITE_TAC[SWAP_REVERSE_SYM; REVERSE; APPEND]);;

let FRONT_NIL = CONJUNCT1 BUTLAST;;

let FRONT_CONS = prove
 (`(!x:A. BUTLAST [x] = []) /\
   (!x:A y z. BUTLAST (CONS x (CONS y z)) = CONS x (BUTLAST (CONS y z)))`,
  REWRITE_TAC[BUTLAST_CLAUSES]);;

let LENGTH_FRONT_CONS = prove
 (`!x:A xs. LENGTH (BUTLAST (CONS x xs)) = LENGTH xs`,
  ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[BUTLAST_CLAUSES; LENGTH]);;

let FRONT_CONS_EQ_NIL = prove
 (`(!x:A xs. (BUTLAST (CONS x xs) = []) <=> (xs = [])) /\
   (!x:A xs. ([] = BUTLAST (CONS x xs)) <=> (xs = [])) /\
   (!x:A xs. NULL (BUTLAST (CONS x xs)) <=> NULL xs)`,
  REWRITE_TAC[NULL_EQ] THEN REPEAT STRIP_TAC THEN REWRITE_TAC[BUTLAST] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[NOT_CONS_NIL; GSYM NOT_CONS_NIL]);;

let LAST_APPEND_CONS = prove
 (`!(h:A) l1 l2. LAST (APPEND l1 (CONS h l2)) = LAST (CONS h l2)`,
  REWRITE_TAC[LAST_APPEND; NOT_CONS_NIL]);;

let MAP_ZIP_SAME = prove
 (`!ls (f:A#A->B). MAP f (ZIP ls ls) = MAP (\x. f (x,x)) ls`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[ZIP_def; MAP]);;

let LIST_BIND_THM = prove
 (`(LIST_BIND [] (f:A->B list) = []) /\
   (LIST_BIND (CONS h t) f = APPEND (f h) (LIST_BIND t f))`,
  REWRITE_TAC[LIST_BIND_DEF; MAP; FLAT]);;

(* HOL4 ZIP_UNZIP: ZIP (UNZIP l) = l, with the pair argument split *)
let ZIP_UNZIP = prove
 (`!l:(A#B) list. ZIP (FST (UNZIP l)) (SND (UNZIP l)) = l`,
  REWRITE_TAC[UNZIP_DEF] THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[MAP; ZIP_def; PAIR]);;

let UNZIP_ZIP = prove
 (`!l1:A list. !l2:B list.
     (LENGTH l1 = LENGTH l2) ==> (UNZIP (ZIP l1 l2) = (l1,l2))`,
  SIMP_TAC[UNZIP_DEF; MAP_FST_ZIP; MAP_SND_ZIP]);;

let LENGTH_UNZIP = prove
 (`!pl:(A#B) list. (LENGTH (FST (UNZIP pl)) = LENGTH pl) /\
                   (LENGTH (SND (UNZIP pl)) = LENGTH pl)`,
  REWRITE_TAC[UNZIP_DEF; LENGTH_MAP]);;

(* ------------------------------------------------------------------------- *)
(* list_size (HOL4 [simp] lemmas, used in termination arguments).            *)
(* ------------------------------------------------------------------------- *)

let list_size_reverse = prove
 (`list_size (f:A->num) (REVERSE l) = list_size f l`,
  SPEC_TAC(`l:A list`,`l:A list`) THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[REVERSE; list_size_append; list_size] THEN ARITH_TAC);;

let list_size_map = prove
 (`list_size (f:B->num) (MAP (g:A->B) l) = list_size (\x. f (g x)) l`,
  SPEC_TAC(`l:A list`,`l:A list`) THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[MAP; list_size]);;

let list_size_snoc = prove
 (`list_size (f:A->num) (SNOC x l) = list_size f (CONS x l)`,
  REWRITE_TAC[LISTAUX_SNOC_APPEND; list_size_append; list_size] THEN
  ARITH_TAC);;

let list_size_filter = prove
 (`list_size (f:A->num) (FILTER P l) <= list_size f l`,
  SPEC_TAC(`l:A list`,`l:A list`) THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[FILTER; list_size; LE_REFL] THEN
  COND_CASES_TAC THEN REWRITE_TAC[list_size] THEN ASM_ARITH_TAC);;

let list_size_take = prove
 (`!l n. list_size (f:A->num) (TAKE n l) <= list_size f l`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[TAKE_DEF; list_size; LE_REFL] THEN
  GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[list_size; LE_0] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `n - 1`) THEN ARITH_TAC);;

let list_size_drop = prove
 (`!l n. list_size (f:A->num) (DROP n l) <= list_size f l`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[DROP_DEF; list_size; LE_REFL] THEN
  GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[list_size; LE_REFL] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `n - 1`) THEN ARITH_TAC);;

let filter_size_less = prove
 (`!h t. list_size (f:A->num) (FILTER P t) < list_size f (CONS h t)`,
  REPEAT GEN_TAC THEN
  MP_TAC(INST [`t:A list`,`l:A list`] list_size_filter) THEN
  REWRITE_TAC[list_size] THEN ARITH_TAC);;

(* ========================================================================= *)
(* indexedLists: MAPi, FOLDRi, findi, LIST_RELi.                             *)
(* ========================================================================= *)

let MAPi_def = MAPi_DEF;;

let LENGTH_MAPi = prove
 (`!(f:num->A->B) l. LENGTH (MAPi f l) = LENGTH l`,
  ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[MAPi_DEF; LENGTH]);;

let MEM_MAPi = prove
 (`!x (f:num->A->B) l. MEM x (MAPi f l) <=>
     ?n. n < LENGTH l /\ x = f n (EL n l)`,
  GEN_TAC THEN ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[MAPi_DEF; MEM; LENGTH; CONJUNCT1 LT; LISTAUX_EXISTS_LT_SUC;
                  EL; HD; TL; o_THM]);;

let MAPi_CONG = prove
 (`!l1 l2 (f1:num->A->B) f2.
     l1 = l2 /\ (!x n. MEM x l2 ==> f1 n x = f2 n x) ==>
     MAPi f1 l1 = MAPi f2 l2`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 SUBST1_TAC MP_TAC) THEN
  SPEC_TAC(`f2:num->A->B`,`f2:num->A->B`) THEN
  SPEC_TAC(`f1:num->A->B`,`f1:num->A->B`) THEN
  SPEC_TAC(`l2:A list`,`l2:A list`) THEN
  LIST_INDUCT_TAC THEN REWRITE_TAC[MAPi_DEF; MEM; CONS_11] THEN
  REPEAT STRIP_TAC THENL
  [ASM_MESON_TAC[];
   FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[o_THM]]);;

let EL_MAPi = prove
 (`!(f:num->A->B) n l. n < LENGTH l ==> EL n (MAPi f l) = f n (EL n l)`,
  SUBGOAL_THEN
   `!l (f:num->A->B) n. n < LENGTH l ==> EL n (MAPi f l) = f n (EL n l)`
   (fun th -> MESON_TAC[th]) THEN
  LIST_INDUCT_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
  ASM_SIMP_TAC[MAPi_DEF; EL; HD; TL; LENGTH; LT_SUC; o_THM; CONJUNCT1 LT;
               LT_0]);;

let MAP_MAPi = prove
 (`!(f:B->C) (g:num->A->B) l. MAP f (MAPi g l) = MAPi ((o) f o g) l`,
  GEN_TAC THEN ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[MAPi_DEF; MAP; o_THM; CONS_11] THEN
  GEN_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; o_THM]);;

let MAPi_EQ_MAP = prove
 (`!l. MAPi (\i x. (f:A->B) x) l = MAP f l`,
  SUBGOAL_THEN `!l (g:num->A->B). (!i. g i = f) ==> MAPi g l = MAP f l`
   (fun th -> GEN_TAC THEN MATCH_MP_TAC th THEN REWRITE_TAC[ETA_AX]) THEN
  LIST_INDUCT_TAC THEN REWRITE_TAC[MAPi_DEF; MAP; CONS_11] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[o_THM]);;

let LISTAUX_o_ADD_0 = prove
 (`!(f:num->A). f o (+) 0 = f`,
  REWRITE_TAC[FUN_EQ_THM; o_THM; ADD_CLAUSES]);;

let LISTAUX_o_SUC_ADD = prove
 (`!(f:num->A) n. (f o SUC) o (+) n = f o (+) (SUC n)`,
  REWRITE_TAC[FUN_EQ_THM; o_THM; ADD_CLAUSES]);;

let MAPi_APPEND = prove
 (`!l1 l2 (f:num->A->B).
     MAPi f (APPEND l1 l2) = APPEND (MAPi f l1) (MAPi (f o (+) (LENGTH l1)) l2)`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[APPEND; MAPi_DEF; LENGTH; LISTAUX_o_ADD_0;
                  LISTAUX_o_SUC_ADD]);;

(* HOL4 MAPi_GENLIST has GENLIST (S f (combin$C EL l)) (LENGTH l); the S and
   C combinators are written out as the lambda term. *)
let MAPi_GENLIST = prove
 (`!l (f:num->A->B). MAPi f l = list_of_seq (\i. f i (EL i l)) (LENGTH l)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[LIST_EQ; LENGTH_MAPi; LENGTH_LIST_OF_SEQ] THEN
  SIMP_TAC[EL_MAPi; EL_LIST_OF_SEQ]);;

let FOLDRi_def = new_recursive_definition list_RECURSION
  `(FOLDRi (f:num->A->B->B) a [] = a) /\
   (FOLDRi f a (CONS h t) = f 0 h (FOLDRi (f o SUC) a t))`;;

let FOLDRi_APPEND = prove
 (`!f:num->A->B->B.
     FOLDRi f a (APPEND l1 l2) = FOLDRi f (FOLDRi (f o (+) (LENGTH l1)) a l2) l1`,
  SPEC_TAC(`l1:A list`,`l1:A list`) THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[APPEND; FOLDRi_def; LENGTH; LISTAUX_o_ADD_0;
                  LISTAUX_o_SUC_ADD]);;

let findi_def = new_recursive_definition list_RECURSION
  `(findi (x:A) [] = 0) /\
   (findi x (CONS h t) = if x = h then 0 else 1 + findi x t)`;;

let findi_nil = CONJUNCT1 findi_def;;

let findi_cons = CONJUNCT2 findi_def;;

(* LIST_RELi R l1 l2: l1 and l2 related pointwise by R with the index. *)
let LIST_RELi_rules,LIST_RELi_ind,LIST_RELi_cases = new_inductive_definition
  `LIST_RELi (R:num->A->B->bool) [] [] /\
   (!h1 h2 l1 l2. R (LENGTH l1) h1 h2 /\ LIST_RELi R l1 l2 ==>
                  LIST_RELi R (APPEND l1 [h1]) (APPEND l2 [h2]))`;;

let LISTAUX_SNOC_INDUCT = prove
 (`!P. P [] /\ (!(x:A) l. P l ==> P (APPEND l [x])) ==> !l. P l`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!l:A list. P (REVERSE l)`
    (fun th -> MESON_TAC[th; REVERSE_REVERSE]) THEN
  LIST_INDUCT_TAC THEN ASM_SIMP_TAC[REVERSE]);;

let LISTAUX_SNOC_CASES = prove
 (`!l:A list. l = [] \/ ?x l'. l = APPEND l' [x]`,
  MESON_TAC[APPEND_BUTLAST_LAST]);;

let LIST_RELi_EL_EQN = prove
 (`LIST_RELi (R:num->A->B->bool) l1 l2 <=>
   LENGTH l1 = LENGTH l2 /\ !i. i < LENGTH l1 ==> R i (EL i l1) (EL i l2)`,
  EQ_TAC THENL
  [SPEC_TAC(`l2:B list`,`l2:B list`) THEN SPEC_TAC(`l1:A list`,`l1:A list`) THEN
   MATCH_MP_TAC LIST_RELi_ind THEN
   REWRITE_TAC[LENGTH; CONJUNCT1 LT; LENGTH_APPEND] THEN
   REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
   X_GEN_TAC `i:num` THEN DISCH_TAC THEN REWRITE_TAC[EL_APPEND] THEN
   ASM_CASES_TAC `i < LENGTH (l2:B list)` THEN ASM_SIMP_TAC[] THEN
   SUBGOAL_THEN `i = LENGTH (l2:B list)` SUBST_ALL_TAC THENL
   [ASM_ARITH_TAC; ASM_REWRITE_TAC[SUB_REFL; EL; HD]] THEN
   ASM_MESON_TAC[];
   ALL_TAC] THEN
  SPEC_TAC(`l2:B list`,`l2:B list`) THEN SPEC_TAC(`l1:A list`,`l1:A list`) THEN
  MATCH_MP_TAC LISTAUX_SNOC_INDUCT THEN CONJ_TAC THENL
  [GEN_TAC THEN REWRITE_TAC[LENGTH; LENGTH_NIL_SYM] THEN
   STRIP_TAC THEN ASM_REWRITE_TAC[LIST_RELi_rules];
   ALL_TAC] THEN
  X_GEN_TAC `x:A` THEN X_GEN_TAC `l:A list` THEN DISCH_TAC THEN
  X_GEN_TAC `l2:B list` THEN
  STRUCT_CASES_TAC(ISPEC `l2:B list` LISTAUX_SNOC_CASES) THEN
  REWRITE_TAC[LENGTH_APPEND; LENGTH] THENL [ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[ARITH_RULE `a + SUC 0 = b + SUC 0 <=> a = b`] THEN STRIP_TAC THEN
  MATCH_MP_TAC(CONJUNCT2 (SPEC_ALL LIST_RELi_rules)) THEN CONJ_TAC THENL
  [FIRST_X_ASSUM(MP_TAC o SPEC `LENGTH (l:A list)`) THEN
   REWRITE_TAC[EL_APPEND; LT_REFL; SUB_REFL; EL; HD] THEN
   ASM_REWRITE_TAC[LT_REFL; SUB_REFL; EL; HD] THEN
   SIMP_TAC[ARITH_RULE `n < n + SUC 0`];
   FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
   X_GEN_TAC `i:num` THEN DISCH_TAC THEN
   FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN
   ASM_SIMP_TAC[EL_APPEND; ARITH_RULE `i < n ==> i < n + SUC 0`]]);;

(* ------------------------------------------------------------------------- *)
(* The HOL4 [simp] and export_rewrites theorems of listTheory and            *)
(* indexedListsTheory, for the project simpset (SIMP, FS, GVS, RW).  HOL4's  *)
(* LENGTH_MAP2 and LENGTH_ZIP_MIN are replaced by the unconditional HOL      *)
(* Light facts LENGTH (MAP2 f xs ys) = LENGTH xs and LENGTH (ZIP xs ys) =    *)
(* LENGTH xs; HOL4's MAP2_NIL and LENGTH_TL are false in HOL Light.          *)
(* ------------------------------------------------------------------------- *)

let _ = cake_add_simps
  [LIST_TO_SET_DEF; LIST_TO_SET; LISTAUX_LENGTH_MAP2; MAP2; CONJUNCT1 MAP2_DEF;
   LIST_REL_def; LIST_REL_NIL; EVERY2_THM; LIST_REL_eq;
   LENGTH_APPEND; MAP_APPEND; LENGTH_MAP; list_MAP_ID; MAP_EQ_SING;
   list_MAP_EQ_NIL; MEM_APPEND; SING_HD; NULL_MAP; APPEND_eq_NIL; NULL_APPEND;
   FILTER; FILTER_F; FILTER_T; EL_restricted; EL_simp_restricted;
   LIST_EXISTS_SIMP; EVERY_SIMP; EXISTS_APPEND; EVERY_APPEND; NOT_EVERY;
   NOT_EXISTS; APPEND_11; APPEND_ASSOC; CONS_ACYCLIC; FOLDL; ITLIST; SUM; FLAT;
   ZIP_def; ZIP_UNZIP; UNZIP_ZIP; LENGTH_UNZIP; LISTAUX_LENGTH_ZIP;
   REVERSE_REVERSE; REVERSE_11; MEM_REVERSE; LENGTH_REVERSE; REVERSE_EQ_SING;
   FRONT_NIL; LAST_MAP; FRONT_CONS; LENGTH_FRONT_CONS; FRONT_CONS_EQ_NIL;
   LAST_APPEND_CONS;
   TAKE_nil; TAKE_cons; DROP_nil; DROP_cons; TAKE_0; TAKE_LENGTH_ID;
   LENGTH_TAKE; DROP_0; TAKE_DROP; TAKE1_DROP; TAKE_EQ_NIL; LENGTH_DROP;
   DROP_EQ_NIL; TAKE_LENGTH_ID_rwt2;
   ALL_DISTINCT; ALL_DISTINCT_REVERSE;
   LIST_TO_SET_APPEND; LIST_TO_SET_EQ_EMPTY; FINITE_LIST_TO_SET;
   LIST_TO_SET_REVERSE; SET_TO_LIST_EMPTY; MEM_SET_TO_LIST; SET_TO_LIST_SING;
   ALL_DISTINCT_SET_TO_LIST;
   isPREFIX; isPREFIX_THM; isPREFIX_NILR; isPREFIX_SNOC;
   SNOC; LAST_SNOC; FRONT_SNOC; APPEND_SNOC; EVERY_SNOC; MEM_SNOC; SNOC_11;
   EL_GENLIST; NULL_GENLIST; MAP_ZIP_SAME;
   LUPDATE_NIL; LENGTH_LUPDATE; LUPDATE_LENGTH; LIST_BIND_THM; LLEX_NIL2;
   nub_NIL; nub_EQ0; nub_set; all_distinct_nub; OPT_MMAP_def; oHD_thm;
   MAPi_def; LENGTH_MAPi; MAP_MAPi; EL_MAPi; MAPi_EQ_MAP; FOLDRi_def;
   list_size_reverse; list_size_map; list_size_snoc; list_size_filter;
   list_size_take; list_size_drop; filter_size_less];;


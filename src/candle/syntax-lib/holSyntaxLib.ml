(* ========================================================================= *)
(* holSyntaxLib: port of HOL4 candle/syntax-lib/holSyntaxLibScript.sml       *)
(* (CakeML v3479).  Definitions for manipulating (deeply embedded) HOL       *)
(* syntax.                                                                   *)
(*                                                                           *)
(* Notes on the rendering:                                                   *)
(* - Names as doc/names.tsv says: the type result is hol_result,             *)
(*   its constructors Clash and hol_Result; tyvar_inst_exists is             *)
(*   hol_tyvar_inst_exists.                                                  *)
(* - EVERY is ALL, set is set_of_list, FOLDR f e l is ITLIST f l e, GENLIST  *)
(*   f n is list_of_seq f n, a character literal #"'" is CHR 39, $< on       *)
(*   strings is string_lt.                                                   *)
(* - Local helpers that are not HOL4 theorems are CSYNAUX_.                  *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "basis/pure/mlstring.ml";;

prioritize_num();;
type_invention_error := true;;

let ALPHAVARS_def = cake_def
  `(ALPHAVARS [] (tmp:A#A) <=> FST tmp = SND tmp) /\
   (ALPHAVARS (CONS tp oenv) tmp <=>
      tmp = tp \/
      ~(FST tp = FST tmp) /\ ~(SND tp = SND tmp) /\ ALPHAVARS oenv tmp)`;;

let ALPHAVARS_REFL = prove
 (`!env (t:A). ALL (UNCURRY (=)) env ==> ALPHAVARS env (t,t)`,
  MATCH_MP_TAC list_INDUCT THEN
  REWRITE_TAC[FORALL_PAIR_THM; ALL; ALPHAVARS_def; UNCURRY_DEF; PAIR_EQ] THEN
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `(t:A) = p1` THEN FS[]);;

let ALPHAVARS_MEM = prove
 (`!env (tp:A#A). ALPHAVARS env tp ==> MEM tp env \/ FST tp = SND tp`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[ALPHAVARS_def; MEM] THEN
  ASM_MESON_TAC[]);;

let REV_ASSOCD_def = cake_def
  `(REV_ASSOCD (a:B) [] (d:A) = d) /\
   (REV_ASSOCD a (CONS (p:A#B) t) d =
      if SND p = a then FST p else REV_ASSOCD a t d)`;;

let REV_ASSOCD = prove
 (`(!(a:B) (d:A). REV_ASSOCD a [] d = d) /\
   (!(a:B) (x:A) y t d. REV_ASSOCD a (CONS (x,y) t) d =
                        if y = a then x else REV_ASSOCD a t d)`,
  RW[REV_ASSOCD_def]);;

let REV_ASSOCD_ALOOKUP = prove
 (CASE_TERM
  `!ls (x:B) (d:A). REV_ASSOCD x ls d =
      match ALOOKUP (MAP (\(x,y). (y,x)) ls) x with NONE -> d | SOME y -> y`,
  LIST_INDUCT_TAC THEN SIMP[REV_ASSOCD; MAP; ALOOKUP_def] THEN
  PAIR_CASES_ON `h:A#B` THEN SIMP[REV_ASSOCD; MAP; ALOOKUP_def] THEN
  RW[] THEN FS[]);;

let PRIMED_INFINITE = prove
 (`INFINITE (IMAGE (\n. APPEND x (list_of_seq (combin_K (CHR 39)) n)) (:num))`,
  MATCH_MP_TAC(REWRITE_RULE[RIGHT_IMP_FORALL_THM; IMP_IMP] INFINITE_IMAGE_INJ) THEN
  REWRITE_TAC[num_INFINITE] THEN
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o AP_TERM `LENGTH:(char)list->num`) THEN
  REWRITE_TAC[LENGTH_APPEND; LENGTH_LIST_OF_SEQ] THEN ARITH_TAC);;

let REV_ASSOCD_FILTER = prove
 (`!l (a:B) (b:A) (d:C).
     REV_ASSOCD a (FILTER (\(y,x). P x) l) b =
       if P a then REV_ASSOCD a l b else b`,
  LIST_INDUCT_TAC THEN SIMP[REV_ASSOCD; FILTER] THEN
  PAIR_CASES_ON `h:A#B` THEN SIMP[REV_ASSOCD; FILTER] THEN
  RW[] THEN FS[REV_ASSOCD] THEN RW[] THEN FS[]);;

let REV_ASSOCD_MEM = prove
 (`!l (x:B) (d:A). MEM (REV_ASSOCD x l d,x) l \/ REV_ASSOCD x l d = d`,
  LIST_INDUCT_TAC THEN SIMP[REV_ASSOCD; MEM] THEN
  PAIR_CASES_ON `h:A#B` THEN SIMP[REV_ASSOCD; MEM] THEN RW[] THEN FS[]);;

(* HOL4: tyvar_inst_exists *)
let hol_tyvar_inst_exists = prove
 (`?i. (ty:A) = REV_ASSOCD (tyvar:B) i b`,
  EXISTS_TAC `[(ty:A,tyvar:B)]` THEN REWRITE_TAC[REV_ASSOCD]);;

let hol_result_INDUCT,hol_result_RECURSION =
  cake_type "hol_result = Clash A | hol_Result A";;

let IS_RESULT_def = cake_def
  `(IS_RESULT (Clash (_:A)) <=> F) /\
   (IS_RESULT (hol_Result (_:A)) <=> T)`;;
let _ = cake_add_simps [IS_RESULT_def];;

let IS_CLASH_def = cake_def
  `(IS_CLASH (Clash (_:A)) <=> T) /\
   (IS_CLASH (hol_Result (_:A)) <=> F)`;;
let _ = cake_add_simps [IS_CLASH_def];;

let RESULT_def = cake_def
  `RESULT (hol_Result (t:A)) = t`;;
let _ = cake_add_simps [RESULT_def];;

let CLASH_def = cake_def
  `CLASH (Clash (t:A)) = t`;;
let _ = cake_add_simps [CLASH_def];;

let NOT_IS_CLASH_IS_RESULT = prove
 (`!x:(A)hol_result. IS_CLASH x <=> ~IS_RESULT x`,
  GEN_TAC THEN CASES_ON `x:(A)hol_result` THEN SIMP[]);;

let RESULT_eq_suff = prove
 (`(x:(A)hol_result) = hol_Result y ==> RESULT x = y`,
  CASES_ON `x:(A)hol_result` THEN SIMP[]);;

let IS_CLASH_IMP = prove
 (`!x:(A)hol_result. IS_CLASH x ==> !tm. ~(x = hol_Result tm)`,
  GEN_TAC THEN CASES_ON `x:(A)hol_result` THEN SIMP[]);;

let NOT_IS_CLASH_IMP = prove
 (`!x:(A)hol_result. ~IS_CLASH x ==> !tm. ~(x = Clash tm)`,
  GEN_TAC THEN CASES_ON `x:(A)hol_result` THEN SIMP[]);;

let IS_RESULT_IMP = prove
 (`!x:(A)hol_result. IS_RESULT x ==> (!tm. ~(x = Clash tm))`,
  GEN_TAC THEN CASES_ON `x:(A)hol_result` THEN SIMP[]);;

let NOT_IS_RESULT_IMP_Clash = prove
 (`!x:(A)hol_result. ~IS_RESULT x ==> ?var. x = Clash var`,
  GEN_TAC THEN CASES_ON `x:(A)hol_result` THEN SIMP[]);;

let IS_RESULT_IMP_Result = prove
 (`!x:(A)hol_result. IS_RESULT x ==> ?res. x = hol_Result res`,
  GEN_TAC THEN CASES_ON `x:(A)hol_result` THEN SIMP[]);;

let NOT_IS_CLASH_IMP_Result = prove
 (`!x:(A)hol_result. ~IS_CLASH x ==> ?res. x = hol_Result res`,
  GEN_TAC THEN CASES_ON `x:(A)hol_result` THEN SIMP[]);;

let LIST_INSERT_def = cake_def
  `LIST_INSERT (x:A) xs = if MEM x xs then xs else CONS x xs`;;

let MEM_LIST_INSERT = prove
 (`!l (x:A). set_of_list (LIST_INSERT x l) = x INSERT set_of_list l`,
  REWRITE_TAC[LIST_INSERT_def] THEN RW[set_of_list] THEN
  FS[IN_SET_OF_LIST; SET_RULE `(x:A) IN s ==> x INSERT s = s`]);;

let LIST_UNION_def = cake_def
  `LIST_UNION (xs:A list) ys = ITLIST LIST_INSERT xs ys`;;

let MEM_LIST_UNION = prove
 (`!l1 (l2:A list).
     set_of_list (LIST_UNION l1 l2) = set_of_list l1 UNION set_of_list l2`,
  LIST_INDUCT_TAC THEN FS[LIST_UNION_def; MEM_LIST_INSERT; ITLIST; set_of_list] THEN
  SET_TAC[]);;

let MEM_FOLDR_LIST_UNION = prove
 (`!ls (x:A) (f:B->A list) b.
     MEM x (ITLIST (\x y. LIST_UNION (f x) y) ls b) <=>
     MEM x b \/ ?y. MEM y ls /\ MEM x (f y)`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[ITLIST; MEM;
    REWRITE_RULE[EXTENSION; IN_UNION; IN_SET_OF_LIST] MEM_LIST_UNION] THEN
  MESON_TAC[]);;

let LIST_UNION_NIL = prove
 (`!l2:A list. LIST_UNION [] l2 = l2`,
  SIMP[LIST_UNION_def; ITLIST]);;
let _ = cake_add_simps [LIST_UNION_NIL];;

let set_LIST_UNION = prove
 (`!l1 (l2:A list).
     set_of_list (LIST_UNION l1 l2) = set_of_list l1 UNION set_of_list l2`,
  REWRITE_TAC[MEM_LIST_UNION]);;
let _ = cake_add_simps [set_LIST_UNION];;

let LIST_UNION_NIL_2 = prove
 (`!ls:A list. ALL_DISTINCT ls ==> LIST_UNION ls [] = ls`,
  LIST_INDUCT_TAC THEN SIMP[LIST_UNION_def; LIST_INSERT_def; ITLIST] THEN
  RW[] THEN RFS[LIST_UNION_def] THEN FS[]);;

let LIST_UNION_same = prove
 (`!l1 (l2:A list).
     set_of_list l1 SUBSET set_of_list l2 ==> LIST_UNION l1 l2 = l2`,
  LIST_INDUCT_TAC THEN SIMP[LIST_UNION_def; ITLIST] THEN
  FS[SUBSET; set_of_list; IN_INSERT] THEN
  FS[LIST_UNION_def; LIST_INSERT_def; IN_SET_OF_LIST]);;

let INORDER_INSERT_def = cake_def
  `INORDER_INSERT x xs =
     APPEND (FILTER (\y. string_lt y x) xs)
            (APPEND [x] (FILTER (\y. string_lt x y) xs))`;;

let LENGTH_INORDER_INSERT = prove
 (`!xs. ALL_DISTINCT (CONS x xs)
        ==> LENGTH (INORDER_INSERT x xs) = SUC (LENGTH xs)`,
  REWRITE_TAC[INORDER_INSERT_def; LENGTH_APPEND; LENGTH; ALL_DISTINCT] THEN
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(ARITH_RULE `n = a + b ==> a + SUC 0 + b = SUC n`) THEN
  MATCH_MP_TAC LENGTH_EQ_FILTER_FILTER THEN REWRITE_TAC[GSYM ALL_MEM] THEN
  ASM_MESON_TAC[string_lt_cases; string_lt_antisym]);;

let ALL_DISTINCT_INORDER_INSERT = prove
 (`!xs h. ALL_DISTINCT xs ==> ALL_DISTINCT (INORDER_INSERT h xs)`,
  REWRITE_TAC[INORDER_INSERT_def; ALL_DISTINCT_APPEND; APPEND; ALL_DISTINCT;
              MEM_FILTER; MEM] THEN
  SIMP_TAC[FILTER_ALL_DISTINCT] THEN
  MESON_TAC[string_lt_nonrefl; string_lt_antisym]);;

let ALL_DISTINCT_FOLDR_INORDER_INSERT = prove
 (`!xs. ALL_DISTINCT (ITLIST INORDER_INSERT xs [])`,
  LIST_INDUCT_TAC THEN
  ASM_SIMP_TAC[ALL_DISTINCT; ITLIST; ALL_DISTINCT_INORDER_INSERT]);;

let MEM_FOLDR_INORDER_INSERT = prove
 (`!xs x. MEM x (ITLIST INORDER_INSERT xs []) <=> MEM x xs`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[ITLIST; INORDER_INSERT_def; MEM; MEM_APPEND; MEM_FILTER] THEN
  MESON_TAC[string_lt_cases]);;
let _ = cake_add_simps [MEM_FOLDR_INORDER_INSERT];;

let STRING_SORT_def = cake_def
  `STRING_SORT xs = ITLIST INORDER_INSERT xs []`;;

let PERM_STRING_SORT = prove
 (`!ls. ALL_DISTINCT ls ==> PERM ls (STRING_SORT ls)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[STRING_SORT_def; ITLIST; PERM_REFL] THEN
  REWRITE_TAC[INORDER_INSERT_def; PERM_CONS_EQ_APPEND; ALL_DISTINCT] THEN
  STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC
   [`FILTER (\y. string_lt y h) (ITLIST INORDER_INSERT t [])`;
    `FILTER (\y. string_lt h y) (ITLIST INORDER_INSERT t [])`] THEN
  REWRITE_TAC[APPEND] THEN MATCH_MP_TAC PERM_ALL_DISTINCT THEN
  ASM_SIMP_TAC[ALL_DISTINCT_APPEND; FILTER_ALL_DISTINCT;
               ALL_DISTINCT_FOLDR_INORDER_INSERT; MEM_APPEND; MEM_FILTER;
               MEM_FOLDR_INORDER_INSERT] THEN
  ASM_MESON_TAC[string_lt_antisym; string_lt_cases]);;

let LENGTH_STRING_SORT = prove
 (`!ls. ALL_DISTINCT ls ==> LENGTH (STRING_SORT ls) = LENGTH ls`,
  MESON_TAC[PERM_STRING_SORT; PERM_LENGTH]);;
let _ = cake_add_simps [LENGTH_STRING_SORT];;

let MEM_STRING_SORT = prove
 (`!ls. set_of_list (STRING_SORT ls) = set_of_list ls`,
  REWRITE_TAC[EXTENSION; IN_SET_OF_LIST; STRING_SORT_def;
              MEM_FOLDR_INORDER_INSERT]);;
let _ = cake_add_simps [MEM_STRING_SORT];;

let ALL_DISTINCT_STRING_SORT = prove
 (`!xs. ALL_DISTINCT (STRING_SORT xs)`,
  REWRITE_TAC[STRING_SORT_def; ALL_DISTINCT_FOLDR_INORDER_INSERT]);;
let _ = cake_add_simps [ALL_DISTINCT_STRING_SORT];;

let STRING_SORT_SORTED = prove
 (`!ls. SORTED string_lt (STRING_SORT ls)`,
  SUBGOAL_THEN `transitive string_lt` ASSUME_TAC THENL
   [REWRITE_TAC[transitive_def] THEN MESON_TAC[string_lt_trans]; ALL_TAC] THEN
  LIST_INDUCT_TAC THEN REWRITE_TAC[STRING_SORT_def; ITLIST; SORTED_DEF] THEN
  FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[STRING_SORT_def]) THEN
  ASM_SIMP_TAC[INORDER_INSERT_def; SORTED_APPEND; SORTED_FILTER; SORTED_DEF;
               MEM_FILTER; MEM_APPEND; MEM] THEN
  ASM_MESON_TAC[string_lt_trans]);;

let STRING_SORT_EQ = prove
 (`!l1 l2. ALL_DISTINCT l1 /\ ALL_DISTINCT l2
           ==> (STRING_SORT l1 = STRING_SORT l2 <=> PERM l1 l2)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `transitive string_lt /\ antisymmetric string_lt`
    (ASSUME_TAC o MATCH_MP SORTED_PERM_EQ) THENL
   [REWRITE_TAC[transitive_def; antisymmetric_def] THEN
    MESON_TAC[string_lt_trans; string_lt_antisym]; ALL_TAC] THEN
  MP_TAC(SPEC `l1:string list` PERM_STRING_SORT) THEN
  MP_TAC(SPEC `l2:string list` PERM_STRING_SORT) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN EQ_TAC THENL
   [ASM_MESON_TAC[PERM_SYM; PERM_TRANS];
    DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC[STRING_SORT_SORTED] THEN ASM_MESON_TAC[PERM_SYM; PERM_TRANS]]);;

let ALL_DISTINCT_LIST_UNION = prove
 (`!l1 (l2:A list). ALL_DISTINCT l2 ==> ALL_DISTINCT (LIST_UNION l1 l2)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[LIST_UNION_def; ITLIST] THEN
  REWRITE_TAC[GSYM LIST_UNION_def; LIST_INSERT_def] THEN
  REPEAT STRIP_TAC THEN COND_CASES_TAC THEN ASM_SIMP_TAC[ALL_DISTINCT]);;

let set_MAP_implode_STRING_SORT_MAP_explode = prove
 (`set_of_list (MAP implode (STRING_SORT (MAP explode ls))) =
   set_of_list (ls:mlstring list)`,
  REWRITE_TAC[EXTENSION; IN_SET_OF_LIST; MEM_MAP; STRING_SORT_def;
              MEM_FOLDR_INORDER_INSERT] THEN
  MESON_TAC[implode_explode]);;

let mlstring_sort_def = cake_def
  `mlstring_sort ls = MAP implode (STRING_SORT (MAP explode ls))`;;

let mlstring_sort_eq = prove
 (`!l1 l2. ALL_DISTINCT l1 /\ ALL_DISTINCT l2
           ==> (mlstring_sort l1 = mlstring_sort l2 <=> PERM l1 l2)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mlstring_sort_def] THEN
  REWRITE_TAC[MATCH_MP PERM_MAP_BIJ explode_BIJ] THEN
  MP_TAC(SPECL [`MAP explode l1`; `MAP explode l2`] STRING_SORT_EQ) THEN
  ASM_REWRITE_TAC[ALL_DISTINCT_MAP_explode] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC INJ_MAP_EQ_IFF THEN
  MP_TAC implode_BIJ THEN REWRITE_TAC[BIJ; INJ; IN_UNIV] THEN MESON_TAC[]);;

let mlstring_sort_nil = prove
 (`!l. mlstring_sort l = [] ==> l = []`,
  GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(REWRITE_RULE[GSYM mlstring_sort_def]
    (INST [`l:mlstring list`,`ls:mlstring list`]
       set_MAP_implode_STRING_SORT_MAP_explode)) THEN
  ASM_REWRITE_TAC[set_of_list] THEN
  DISCH_THEN(MP_TAC o SYM) THEN REWRITE_TAC[SET_OF_LIST_EQ_EMPTY]);;

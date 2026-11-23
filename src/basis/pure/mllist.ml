(* ========================================================================= *)
(* mllist: port of HOL4 basis/pure/mllistScript.sml (CakeML v3479).          *)
(* Pure functions for the List module.                                       *)
(*                                                                           *)
(* Names (doc/names.tsv): HOL4 mapi, mapPartial, foldl, foldli_aux,          *)
(* foldli, tabulate and collate are mllist_mapi, ... (mlvector and mlstring  *)
(* define the same names).  HOL4 merge (mergesort.ml) is mergesort_merge;    *)
(* HOL4 l1 ++ l2 is APPEND l1 l2 (left associative), set is set_of_list,     *)
(* GENLIST f n is list_of_seq f n, FUNPOW f n is ITER n f, $~ o f is (~) o f. *)
(* Helper lemmas that are not HOL4 theorems are PURE1AUX_.                   *)
(* HOL4 drop is mllist_drop (a short or common word; drop is also a constant *)
(* of HOL Light's Multivariate), and drop_def is mllist_drop_def.            *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "hol4/list.ml";;
needs "hol4/toto.ml";;
needs "hol4/sorting.ml";;
needs "hol4/mergesort.ml";;

type_invention_error := true;;

let intersperse_def = cake_def
  `(intersperse (_:A) [] = []) /\
   (intersperse _ [x] = [x]) /\
   (intersperse sep (CONS x xs) = CONS x (CONS sep (intersperse sep xs)))`;;

(* ===== TO BE PORTED TO HOL (better theorems for mergesort_tail) ===== *)

let PURE1AUX_TAKE_DIV2 = prove
 (`!n (l:A list).
     TAKE n l = APPEND (TAKE (DIV2 n) l) (TAKE (n - DIV2 n) (DROP (DIV2 n) l))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM TAKE_SUM] THEN AP_THM_TAC THEN
  AP_TERM_TAC THEN REWRITE_TAC[DIV2_DEF] THEN
  MP_TAC(SPECL [`n:num`; `2`] DIV_LE) THEN ARITH_TAC);;

let PURE1AUX_NUM_TAC =
  REPEAT (CHANGED_TAC (REWRITE_TAC[TAKE_DEF; DROP_DEF; TAKE_0; MEM; list_CASE] THEN
                       CONV_TAC NUM_REDUCE_CONV));;

let PURE1AUX_SORT_TAIL_TAC =
  REWRITE_TAC[sort2_tail_def; sort3_tail_def] THEN REPEAT COND_CASES_TAC THEN
  REWRITE_TAC[MEM];;

let merge_tail_MEM = prove
 (`!negate R (xs:A list) ys acc.
     MEM x (merge_tail negate R xs ys acc) <=> MEM x xs \/ MEM x ys \/ MEM x acc`,
  MATCH_MP_TAC merge_tail_ind THEN
  REWRITE_TAC[merge_tail_def; REV_REVERSE_LEM; MEM_APPEND; MEM_REVERSE; MEM] THEN
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[MEM] THEN CONV_TAC TAUT);;

let mergesortN_tail_MEM = prove
 (`!negate R length (lst:A list).
     MEM x (mergesortN_tail negate R length lst) <=> MEM x (TAKE length lst)`,
  MATCH_MP_TAC LSORTAUX_mergesortN_tail_ind THEN
  MAP_EVERY X_GEN_TAC [`negate:bool`; `R:A->A->bool`; `n:num`; `l:A list`] THEN
  STRIP_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [LSORTAUX_mergesortN_tail_eqn] THEN
  ASM_CASES_TAC `n = 0` THEN ASM_REWRITE_TAC[TAKE_0; MEM] THEN
  ASM_CASES_TAC `n = 1` THENL
   [ASM_REWRITE_TAC[] THEN
    REPEAT_TCL STRIP_THM_THEN SUBST1_TAC (ISPEC `l:A list` list_CASES) THEN
    PURE1AUX_NUM_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `n = 2` THENL
   [ASM_REWRITE_TAC[] THEN
    REPEAT_TCL STRIP_THM_THEN SUBST1_TAC (ISPEC `l:A list` LSORTAUX_LIST_CASES2) THEN
    PURE1AUX_NUM_TAC THEN PURE1AUX_SORT_TAIL_TAC THEN CONV_TAC TAUT; ALL_TAC] THEN
  ASM_CASES_TAC `n = 3` THENL
   [ASM_REWRITE_TAC[] THEN
    REPEAT_TCL STRIP_THM_THEN SUBST1_TAC (ISPEC `l:A list` LSORTAUX_LIST_CASES3) THEN
    PURE1AUX_NUM_TAC THEN PURE1AUX_SORT_TAIL_TAC THEN CONV_TAC TAUT; ALL_TAC] THEN
  ASM_REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `~(n = 0)`; ASSUME `~(n = 1)`;
                              ASSUME `~(n = 2)`; ASSUME `~(n = 3)`]) THEN
  ASM_REWRITE_TAC[merge_tail_MEM; MEM] THEN
  GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [PURE1AUX_TAKE_DIV2] THEN
  REWRITE_TAC[MEM_APPEND]);;

let sort3_tail_sort3 = prove
 (`!negate R (x:A) y z. sort3_tail negate R x y z =
     (if negate then REVERSE (sort3 R x y z) else sort3 R x y z)`,
  REWRITE_TAC[sort3_tail_correct]);;

let sort2_tail_sort2 = prove
 (`!negate R (x:A) y. sort2_tail negate R x y =
     (if negate then REVERSE (sort2 R x y) else sort2 R x y)`,
  REWRITE_TAC[sort2_tail_correct]);;

let mergetail_merge = prove
 (`!negate R (xs:A list) ys acc.
     merge_tail negate R xs ys acc =
     (if negate then APPEND (REVERSE (mergesort_merge (\x y. ~R x y) xs ys)) acc
      else APPEND (REVERSE (mergesort_merge R xs ys)) acc)`,
  MATCH_MP_TAC merge_tail_ind THEN
  REWRITE_TAC[merge_tail_def; mergesort_merge_def; REV_REVERSE_LEM; merge_empty;
              REVERSE; APPEND; COND_ID] THEN
  REPEAT GEN_TAC THEN BOOL_CASES_TAC `negate:bool` THEN
  REWRITE_TAC[] THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[REVERSE; GSYM APPEND_ASSOC; APPEND] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[]);;

let merge_tail_acc = prove
 (`!negate R (xs:A list) ys acc acc'.
     merge_tail negate R xs ys (APPEND acc acc') =
     APPEND (merge_tail negate R xs ys acc) acc'`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mergetail_merge] THEN COND_CASES_TAC THEN
  REWRITE_TAC[APPEND_ASSOC]);;

let mergesort_tail_MEM = prove
 (`!R (l:A list). MEM x (mergesort_tail R l) <=> MEM x l`,
  REWRITE_TAC[mergesort_tail_def; mergesortN_tail_MEM; TAKE_LENGTH_ID]);;

let merge_tail_PERM = prove
 (`!negate R (xs:A list) ys acc.
     PERM (APPEND (APPEND xs ys) acc) (merge_tail negate R xs ys acc)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mergetail_merge] THEN COND_CASES_TAC THEN
  REWRITE_TAC[PERM_APPEND_IFF; PERM_REVERSE_EQ; merge_perm]);;

let sort2_tail_PERM = prove
 (`!neg R (x:A) y. PERM [x; y] (sort2_tail neg R x y)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[sort2_tail_def] THEN COND_CASES_TAC THEN
  LSORTAUX_PERM_ARITH_TAC);;

let sort3_tail_PERM = prove
 (`!neg R (x:A) y z. PERM [x; y; z] (sort3_tail neg R x y z)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[sort3_tail_def] THEN REPEAT COND_CASES_TAC THEN
  LSORTAUX_PERM_ARITH_TAC);;

let mergesortN_tail_PERM = prove
 (`!neg R len (l:A list). PERM (TAKE len l) (mergesortN_tail neg R len l)`,
  MATCH_MP_TAC LSORTAUX_mergesortN_tail_ind THEN
  MAP_EVERY X_GEN_TAC [`neg:bool`; `R:A->A->bool`; `n:num`; `l:A list`] THEN
  DISCH_TAC THEN ONCE_REWRITE_TAC[LSORTAUX_mergesortN_tail_eqn] THEN
  LSORTAUX_MSN_CASES_TAC
   (LSORTAUX_TAKE_TAC THEN
    REWRITE_TAC[PERM_REFL; sort2_tail_PERM; sort3_tail_PERM]) THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [PURE1AUX_TAKE_DIV2] THEN
  MATCH_MP_TAC PERM_TRANS THEN
  EXISTS_TAC `APPEND (mergesortN_tail (~neg) R (DIV2 n) (l:A list))
                     (mergesortN_tail (~neg) R (n - DIV2 n) (DROP (DIV2 n) l))` THEN
  ASM_SIMP_TAC[PERM_CONG] THEN
  MP_TAC(ISPECL [`~neg`; `R:A->A->bool`;
                 `mergesortN_tail (~neg) R (DIV2 n) (l:A list)`;
                 `mergesortN_tail (~neg) R (n - DIV2 n) (DROP (DIV2 n) (l:A list))`;
                 `[]:A list`] merge_tail_PERM) THEN
  REWRITE_TAC[APPEND_NIL]);;

(* ^^^^^ TO BE PORTED TO HOL ^^^^^ *)

let sort_def = cake_def
  `(sort:(A->A->bool)->A list->A list) = mergesort_tail`;;

let sort_thm = prove
 (`!R (l:A list). sort R l = mergesort_tail R l`,
  REWRITE_TAC[sort_def]);;

let sort_SORTED = prove
 (`!R (L:A list). transitive R /\ total R ==> SORTED R (sort R L)`,
  SIMP_TAC[sort_def; mergesort_tail_def; mergesortN_correct; mergesortN_sorted]);;

let sort_MEM = prove
 (`!R (L:A list). MEM x (sort R L) <=> MEM x L`,
  REWRITE_TAC[sort_def; mergesort_tail_MEM]);;
let _ = cake_add_simps [sort_MEM];;

let sort_PERM = prove
 (`!R (L:A list). PERM L (sort R L)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[sort_def; mergesort_tail_def] THEN
  MP_TAC(ISPECL [`F`; `R:A->A->bool`; `LENGTH (L:A list)`; `L:A list`]
                mergesortN_tail_PERM) THEN
  REWRITE_TAC[TAKE_LENGTH_ID]);;

let sort_LENGTH = prove
 (`!R (l:A list). LENGTH (sort R l) = LENGTH l`,
  MESON_TAC[PERM_LENGTH; sort_PERM]);;
let _ = cake_add_simps [sort_LENGTH];;

let sort_SORTS = prove
 (`!R:A->A->bool. transitive R /\ total R ==> SORTS sort R`,
  SIMP_TAC[SORTS_DEF; sort_PERM; sort_SORTED]);;

let sort_set = prove
 (`set_of_list (sort R ls) = set_of_list (ls:A list)`,
  REWRITE_TAC[EXTENSION; IN_SET_OF_LIST; sort_MEM]);;
let _ = cake_add_simps [sort_set];;

let getItem_def = cake_def
  `(getItem ([]:A list) = NONE) /\
   (getItem (CONS h t) = SOME (h,t))`;;

let nth_def = cake_def
  `nth (l:A list) i = EL i l`;;

let take_def = cake_def
  `take (l:A list) i = TAKE i l`;;

let mllist_drop_def = cake_def
  `mllist_drop (l:A list) i = DROP i l`;;

let takeUntil_def = cake_def
  `(takeUntil (p:A->bool) [] = []) /\
   (takeUntil p (CONS x xs) = if p x then [] else CONS x (takeUntil p xs))`;;

let dropUntil_def = cake_def
  `(dropUntil (p:A->bool) [] = []) /\
   (dropUntil p (CONS x xs) = if p x then CONS x xs else dropUntil p xs)`;;

let mllist_mapi_def = cake_def
  `(mllist_mapi (f:num->A->B) (n:num) [] = []) /\
   (mllist_mapi f n (CONS h t) =
      (let y = f n h in CONS y (mllist_mapi f (n + 1) t)))`;;

let MAPI_thm_gen = prove
 (`!(f:num->A->B) l x. MAPi (\a. f (a + x)) l = mllist_mapi f x l`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[MAPi_DEF; mllist_mapi_def; LET_DEF; LET_END_DEF; ADD_CLAUSES] THEN
  GEN_TAC THEN REWRITE_TAC[CONS_11] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x + 1`) THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM; o_THM] THEN
  REPEAT GEN_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN ARITH_TAC);;

let MAPI_thm = prove
 (`!(f:num->A->B) l. MAPi f l = mllist_mapi f 0 l`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM MAPI_thm_gen; ADD_CLAUSES; ETA_AX]);;

let mllist_mapPartial_def = cake_def
  `(mllist_mapPartial (f:A->B option) [] = []) /\
   (mllist_mapPartial f (CONS h t) =
      match f h with
        NONE -> mllist_mapPartial f t
      | SOME x -> CONS x (mllist_mapPartial f t))`;;

let mapPartial_thm = prove
 (`!(f:A->B option) l. mllist_mapPartial f l = MAP THE (FILTER IS_SOME (MAP f l))`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[mllist_mapPartial_def; MAP; FILTER] THEN
  CASES_ON `(f:A->B option) h` THEN
  ASM_REWRITE_TAC[option_CASE; IS_SOME_DEF; MAP; THE_DEF]);;

let index_find_thm = prove
 (`!x y. OPTION_MAP SND (INDEX_FIND x f l) =
         OPTION_MAP SND (INDEX_FIND y (f:A->bool) l)`,
  SPEC_TAC(`l:A list`,`l:A list`) THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[INDEX_FIND_DEF] THEN REPEAT GEN_TAC THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[OPTION_MAP_DEF]);;

let FIND_thm = prove
 (`(FIND f [] = NONE) /\
   (!h t. FIND (f:A->bool) (CONS h t) = if f h then SOME h else FIND f t)`,
  REWRITE_TAC[FIND_DEF; INDEX_FIND_DEF; OPTION_MAP_DEF] THEN REPEAT GEN_TAC THEN
  COND_CASES_TAC THEN REWRITE_TAC[OPTION_MAP_DEF; index_find_thm] THEN
  MATCH_ACCEPT_TAC index_find_thm);;

let partition_aux_def = cake_def
  `(partition_aux (f:A->bool) [] pos neg = (REVERSE pos, REVERSE neg)) /\
   (partition_aux f (CONS h t) pos neg =
      if f h then partition_aux f t (CONS h pos) neg
      else partition_aux f t pos (CONS h neg))`;;

let partition_def = cake_def
  `partition (f:A->bool) l = partition_aux f l [] []`;;

let partition_aux_thm = prove
 (`!(f:A->bool) l l1 l2.
     partition_aux f l l1 l2 =
     (APPEND (REVERSE l1) (FILTER f l), APPEND (REVERSE l2) (FILTER ((~) o f) l))`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[partition_aux_def; FILTER; APPEND_NIL; o_THM] THEN
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[REVERSE; GSYM APPEND_ASSOC; APPEND]);;

let partition_pos_thm = prove
 (`!(f:A->bool) l. FST (partition f l) = FILTER f l`,
  REWRITE_TAC[partition_def; partition_aux_thm; REVERSE; APPEND]);;

let partition_neg_thm = prove
 (`!(f:A->bool) l. SND (partition f l) = FILTER ((~) o f) l`,
  REWRITE_TAC[partition_def; partition_aux_thm; REVERSE; APPEND]);;

let mllist_foldl_def = cake_def
  `(mllist_foldl (f:A->B->B) e [] = e) /\
   (mllist_foldl f e (CONS h t) = mllist_foldl f (f h e) t)`;;

let mllist_foldli_aux_def = cake_def
  `(mllist_foldli_aux (f:num->A->B->B) e n [] = e) /\
   (mllist_foldli_aux f e n (CONS h t) = mllist_foldli_aux f (f n h e) (SUC n) t)`;;

let mllist_foldli_def = cake_def
  `mllist_foldli (f:num->A->B->B) e l = mllist_foldli_aux f e 0 l`;;

let mllist_foldli_aux_thm = prove
 (`!l (f:num->A->B->B) e n.
     mllist_foldli_aux f e n l =
     FOLDRi (\n'. f ((LENGTH l + n) - SUC n')) e (REVERSE l)`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[mllist_foldli_aux_def; REVERSE; FOLDRi_def; FOLDRi_APPEND;
                  LENGTH; LENGTH_REVERSE; o_THM] THEN
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `(SUC (LENGTH (t:A list)) + n) - SUC (LENGTH t + 0) = n /\
                LENGTH t + SUC n = SUC (LENGTH t) + n`
   (fun th -> REWRITE_TAC[th]) THEN ARITH_TAC);;

let foldl_intro = prove
 (`!xs x (f:B->A->B). FOLDL f x xs = mllist_foldl (\(x:A) (acc:B). f acc x) x xs`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[FOLDL; mllist_foldl_def]);;

let mllist_foldli_thm = prove
 (`!(f:num->A->B->B) e l.
     mllist_foldli f e l = FOLDRi (\n. f (LENGTH l - SUC n)) e (REVERSE l)`,
  REWRITE_TAC[mllist_foldli_def; mllist_foldli_aux_thm; ADD_CLAUSES]);;

let tabulate_aux_def = cake_def_wf
  `MEASURE (\p:num#num#(num->A)#A list. FST (SND p) - FST p)`
  (REWRITE_TAC[measure_THM] THEN ARITH_TAC)
  `tabulate_aux n m (f:num->A) acc =
     let b = (n >= m) in
     if b then REVERSE acc
     else
       let v = f n in
       let n = n + 1 in
       let acc = CONS v acc in
       tabulate_aux n m f acc`;;

let tabulate_aux_ind = cake_ind "tabulate_aux";;

let mllist_tabulate_def = cake_def
  `mllist_tabulate n (f:num->A) = let l = [] in tabulate_aux 0 n f l`;;

let tabulate_aux_GENLIST = prove
 (`!n m (f:num->A) acc.
     tabulate_aux n m f acc =
     APPEND (REVERSE acc) (list_of_seq (f o ITER n SUC) (m - n))`,
  MATCH_MP_TAC tabulate_aux_ind THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  ONCE_REWRITE_TAC[tabulate_aux_def] THEN REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  COND_CASES_TAC THENL
   [SUBGOAL_THEN `m - n = 0` SUBST1_TAC THENL
     [POP_ASSUM MP_TAC THEN ARITH_TAC;
      REWRITE_TAC[LIST_OF_SEQ; APPEND_NIL]];
    FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    SUBGOAL_THEN `m - n = SUC (m - (n + 1))` SUBST1_TAC THENL
     [POP_ASSUM MP_TAC THEN ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[GENLIST_CONS; REVERSE; GSYM APPEND_ASSOC; APPEND] THEN
    REWRITE_TAC[FUNPOW_SUC_PLUS; o_THM; ADD_CLAUSES] THEN
    REPEAT AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[FUN_EQ_THM; o_THM] THEN GEN_TAC THEN AP_TERM_TAC THEN
    ARITH_TAC]);;

let tabulate_GENLIST = prove
 (`!n. mllist_tabulate n (f:num->A) = list_of_seq f n`,
  REWRITE_TAC[mllist_tabulate_def; tabulate_aux_GENLIST; LET_DEF; LET_END_DEF;
              REVERSE; APPEND; FUNPOW_SUC_PLUS; SUB_0] THEN
  GEN_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; o_THM; ADD_CLAUSES]);;

let mllist_collate_def = cake_def
  `(mllist_collate (f:A->B->ordering) [] [] = EQUAL) /\
   (mllist_collate f [] (CONS h2 t2) = LESS) /\
   (mllist_collate f (CONS h1 t1) [] = GREATER) /\
   (mllist_collate f (CONS h1 t1) (CONS h2 t2) =
      if f h1 h2 = EQUAL then mllist_collate f t1 t2 else f h1 h2)`;;

let mllist_collate_ind = cake_ind "mllist_collate";;

let collate_equal_thm = prove
 (`!l. (!x. MEM x l ==> (f x x = EQUAL)) ==>
       (mllist_collate (f:A->A->ordering) l l = EQUAL)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[mllist_collate_def; MEM] THEN
  STRIP_TAC THEN ASM_SIMP_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_MESON_TAC[]);;

let collate_short_thm = prove
 (`!(f:A->A->ordering) l1 l2.
     (!x. f x x = EQUAL) /\ ~(l1 = l2) /\ (l1 <<= l2)
     ==> (mllist_collate f l1 l2 = LESS)`,
  MATCH_MP_TAC mllist_collate_ind THEN
  REWRITE_TAC[mllist_collate_def; isPREFIX; list_CASE; NOT_CONS_NIL; CONS_11] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[]) THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN ASM_REWRITE_TAC[]);;

let collate_long_thm = prove
 (`!(f:A->A->ordering) l1 l2.
     (!x. f x x = EQUAL) /\ ~(l1 = l2) /\ (l2 <<= l1)
     ==> (mllist_collate f l1 l2 = GREATER)`,
  MATCH_MP_TAC mllist_collate_ind THEN
  REWRITE_TAC[mllist_collate_def; isPREFIX; list_CASE; NOT_CONS_NIL; CONS_11] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[]) THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN ASM_REWRITE_TAC[]);;

let cpn_to_reln_def = cake_def
  `cpn_to_reln (f:A->B->ordering) x1 x2 <=> (f x1 x2 = LESS)`;;

let collate_cpn_reln_thm = prove
 (`!(f:A->A->ordering) l1 l2.
     (!x1 x2. (f x1 x2 = EQUAL) <=> (x1 = x2))
     ==> (cpn_to_reln (mllist_collate f) l1 l2 <=> LLEX (cpn_to_reln f) l1 l2)`,
  MATCH_MP_TAC mllist_collate_ind THEN
  REWRITE_TAC[mllist_collate_def; cpn_to_reln_def; LLEX_def; list_CASE;
              NOT_CONS_NIL; distinctness "ordering"] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(f:A->A->ordering) h1 h2 = EQUAL <=> h1 = h2` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_CASES_TAC `h1:A = h2` THENL
   [SUBGOAL_THEN `(f:A->A->ordering) h1 h2 = EQUAL` ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
    ASM_REWRITE_TAC[distinctness "ordering"];
    SUBGOAL_THEN `~((f:A->A->ordering) h1 h2 = EQUAL)` ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[]]);;

let LENGTH_AUX_def = cake_def
  `(LENGTH_AUX ([]:A list) n = n:num) /\
   (LENGTH_AUX (CONS x xs) n = LENGTH_AUX xs (n + 1))`;;

let LENGTH_AUX_THM = prove
 (`LENGTH (xs:A list) = LENGTH_AUX xs 0`,
  SUBGOAL_THEN `!(xs:A list) n. LENGTH_AUX xs n = LENGTH xs + n`
   (fun th -> REWRITE_TAC[th; ADD_CLAUSES]) THEN
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[LENGTH_AUX_def; LENGTH] THEN ARITH_TAC);;

(* HOL4: Theorem list_compare_def = ternaryComparisonsTheory.list_compare_def *)
let list_compare_def = list_compare_def;;

let map_rev'_def = cake_def
  `(map_rev' (f:A->B) [] acc = acc) /\
   (map_rev' f (CONS x xs) acc = map_rev' f xs (CONS (f x) acc))`;;

let map_rev_def = cake_def
  `map_rev (f:A->B) xs = map_rev' f xs []`;;

let map_rev'_lemma = prove
 (`!acc. map_rev' (f:A->B) xs acc = APPEND (map_rev' f xs []) acc`,
  SPEC_TAC(`xs:A list`,`xs:A list`) THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[map_rev'_def; APPEND] THEN GEN_TAC THEN
  FIRST_ASSUM(fun th -> GEN_REWRITE_TAC (RAND_CONV o LAND_CONV) [th]) THEN
  FIRST_ASSUM(fun th -> GEN_REWRITE_TAC LAND_CONV [th]) THEN
  REWRITE_TAC[GSYM APPEND_ASSOC; APPEND]);;

let map_rev_thm = prove
 (`map_rev (f:A->B) xs = REVERSE (MAP f xs)`,
  REWRITE_TAC[map_rev_def] THEN SPEC_TAC(`xs:A list`,`xs:A list`) THEN
  LIST_INDUCT_TAC THEN REWRITE_TAC[map_rev'_def; MAP; REVERSE] THEN
  ONCE_REWRITE_TAC[map_rev'_lemma] THEN ASM_REWRITE_TAC[APPEND]);;

let filter_rev'_def = cake_def
  `(filter_rev' (P:A->bool) [] acc = acc) /\
   (filter_rev' P (CONS h t) acc =
      if P h then filter_rev' P t (CONS h acc) else filter_rev' P t acc)`;;

let filter_rev_def = cake_def
  `filter_rev (P:A->bool) xs = filter_rev' P xs []`;;

let filter_rev'_lemma = prove
 (`!acc. filter_rev' (P:A->bool) xs acc = APPEND (filter_rev' P xs []) acc`,
  SPEC_TAC(`xs:A list`,`xs:A list`) THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[filter_rev'_def; APPEND] THEN GEN_TAC THEN COND_CASES_TAC THEN
  REWRITE_TAC[] THEN
  FIRST_ASSUM(fun th -> GEN_REWRITE_TAC (RAND_CONV o LAND_CONV) [th]) THEN
  FIRST_ASSUM(fun th -> GEN_REWRITE_TAC LAND_CONV [th]) THEN
  REWRITE_TAC[GSYM APPEND_ASSOC; APPEND]);;

let filter_rev_thm = prove
 (`filter_rev (f:A->bool) xs = REVERSE (FILTER f xs)`,
  REWRITE_TAC[filter_rev_def] THEN SPEC_TAC(`xs:A list`,`xs:A list`) THEN
  LIST_INDUCT_TAC THEN REWRITE_TAC[filter_rev'_def; FILTER; REVERSE] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[REVERSE] THEN
  ONCE_REWRITE_TAC[filter_rev'_lemma] THEN ASM_REWRITE_TAC[APPEND; APPEND_NIL]);;

let flat_rev'_def = cake_def
  `(flat_rev' ([]:(A list) list) acc = acc) /\
   (flat_rev' (CONS x xs) acc = flat_rev' xs (REV x acc))`;;

let flat_rev_def = cake_def
  `flat_rev (xs:(A list) list) = flat_rev' xs []`;;

let flat_rev'_lemma = prove
 (`!acc. flat_rev' (l:(A list) list) acc = APPEND (flat_rev' l []) acc`,
  SPEC_TAC(`l:(A list) list`,`l:(A list) list`) THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[flat_rev'_def; APPEND] THEN GEN_TAC THEN
  FIRST_ASSUM(fun th -> GEN_REWRITE_TAC (RAND_CONV o LAND_CONV) [th]) THEN
  FIRST_ASSUM(fun th -> GEN_REWRITE_TAC LAND_CONV [th]) THEN
  REWRITE_TAC[REV_REVERSE_LEM; APPEND_NIL; GSYM APPEND_ASSOC]);;

let flat_rev_thm = prove
 (`flat_rev (xs:(A list) list) = REVERSE (FLAT xs)`,
  REWRITE_TAC[flat_rev_def] THEN SPEC_TAC(`xs:(A list) list`,`xs:(A list) list`) THEN
  LIST_INDUCT_TAC THEN REWRITE_TAC[flat_rev'_def; FLAT; REVERSE] THEN
  ONCE_REWRITE_TAC[flat_rev'_lemma] THEN
  ASM_REWRITE_TAC[REV_REVERSE_LEM; APPEND_NIL; REVERSE_APPEND]);;

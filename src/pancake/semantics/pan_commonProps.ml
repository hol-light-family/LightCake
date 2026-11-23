(* ========================================================================= *)
(* pan_commonProps: port of HOL4 pancake/semantics/pan_commonPropsScript.sml *)
(* (CakeML v3479).  Common Properties for Pancake ILS.                       *)
(*                                                                           *)
(* Notes on the rendering:                                                   *)
(* - Names as doc/names.tsv says: pan_commonProps_ctxt_max,                  *)
(*   pan_commonProps_no_overlap; the theorems keep their HOL4 names.         *)
(* - HOL4 set is set_of_list; GENLIST f n is list_of_seq f n; FOLDR f e l is *)
(*   ITLIST f l e; ZIP (a,b) is ZIP a b (every ZIP here is of lists of equal *)
(*   lengths); f ' x is FAPPLY f x; () is one, num_set is 1 spt; word5 is    *)
(*   5 word; EVERY is ALL, LIST_REL is ALL2.                                 *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "hol4/libext.ml";;
needs "pancake/pan_common.ml";;

prioritize_num();;
type_invention_error := true;;

let pan_commonProps_ctxt_max_def = cake_def
  `pan_commonProps_ctxt_max (n:num) (fm:(A,B#(num)list)fmap) <=>
     0 <= n /\
     (!v a xs. FLOOKUP fm v = SOME (a,xs) ==> !x. MEM x xs ==> x <= n)`;;

let pan_commonProps_no_overlap_def = cake_def
  `pan_commonProps_no_overlap (fm:(A,B#(C)list)fmap) <=>
     (!x a xs. FLOOKUP fm x = SOME (a,xs) ==> ALL_DISTINCT xs) /\
     (!x y a b xs ys.
        FLOOKUP fm x = SOME (a,xs) /\
        FLOOKUP fm y = SOME (b,ys) /\
        ~DISJOINT (set_of_list xs) (set_of_list ys) ==> x = y)`;;

let opt_mmap_eq_some = prove
 (`!xs (f:A->B option) ys. OPT_MMAP f xs = SOME ys <=> MAP f xs = MAP SOME ys`,
  LIST_INDUCT_TAC THEN RW[OPT_MMAP_def] THEN
  EQ_TAC THEN RW[] THEN FS[] THEN QCASES_ON "ys" THEN FS[]);;

let map_append_eq_drop = prove
 (`!xs ys zs (f:A->B).
     MAP f xs = APPEND ys zs ==> MAP f (DROP (LENGTH ys) xs) = zs`,
  LIST_INDUCT_TAC THEN RW[] THEN QCASES_ON "ys" THEN FS[DROP; SUC_SUB1]);;

let opt_mmap_mem_func = prove
 (`!l (f:A->B option) n g. OPT_MMAP f l = SOME n /\ MEM g l ==> ?m. f g = SOME m`,
  LIST_INDUCT_TAC THEN RW[OPT_MMAP_def] THEN RES_TAC THEN FS[]);;

let opt_mmap_mem_defined = prove
 (`!l (f:A->B option) m e n.
     OPT_MMAP f l = SOME m /\ MEM e l /\ f e = SOME n ==> MEM n m`,
  LIST_INDUCT_TAC THEN RW[] THEN FS[OPT_MMAP_def] THEN RVEQ_TAC THEN
  RES_TAC THEN FS[]);;

let opt_mmap_el = prove
 (`!l (f:A->B option) x n.
     OPT_MMAP f l = SOME x /\ n < LENGTH l ==> f (EL n l) = SOME (EL n x)`,
  LIST_INDUCT_TAC THEN RW[OPT_MMAP_def] THEN QCASES_ON "n" THEN
  FS[ARITH_ss; EL; HD; TL; LT_SUC] THEN ASM_MESON_TAC[]);;

let opt_mmap_length_eq = prove
 (`!l (f:A->B option) n. OPT_MMAP f l = SOME n ==> LENGTH l = LENGTH n`,
  LIST_INDUCT_TAC THEN RW[OPT_MMAP_def] THEN RES_TAC THEN FS[]);;

let opt_mmap_opt_map = prove
 (`!l (f:A->B option) n (g:B->C).
     OPT_MMAP f l = SOME n
     ==> OPT_MMAP (\a. OPTION_MAP g (f a)) l = SOME (MAP g n)`,
  LIST_INDUCT_TAC THEN RW[] THEN FS[OPT_MMAP_def] THEN RVEQ_TAC THEN
  RES_TAC THEN FS[]);;

let distinct_lists_eq_disjoint = prove
 (`distinct_lists (xs:A list) ys <=> DISJOINT (set_of_list xs) (set_of_list ys)`,
  FS[DISJOINT_ALT; distinct_lists_def; EVERY_MEM; IN_SET_OF_LIST]);;

let distinct_lists_append = prove
 (`ALL_DISTINCT (APPEND (xs:A list) ys) ==> distinct_lists xs ys`,
  RW[] THEN FS[ALL_DISTINCT_APPEND; distinct_lists_def; EVERY_MEM]);;

let distinct_lists_commutes = prove
 (`distinct_lists (xs:A list) ys = distinct_lists ys xs`,
  EQ_TAC THEN RW[] THEN FS[distinct_lists_def; EVERY_MEM] THEN ASM_MESON_TAC[]);;

let distinct_lists_cons = prove
 (`distinct_lists (APPEND (ns:A list) xs) (APPEND ys zs) ==> distinct_lists xs zs`,
  RW[] THEN FS[ALL_DISTINCT_APPEND; distinct_lists_def; EVERY_MEM; MEM_APPEND] THEN
  ASM_MESON_TAC[]);;

let distinct_lists_simp_cons = prove
 (`distinct_lists (xs:A list) (CONS y ys) ==> distinct_lists xs ys`,
  RW[] THEN FS[ALL_DISTINCT_APPEND; distinct_lists_def; EVERY_MEM; MEM] THEN
  ASM_MESON_TAC[]);;

let distinct_lists_append_intro = prove
 (`distinct_lists (xs:A list) ys /\ distinct_lists xs zs
   ==> distinct_lists xs (APPEND ys zs)`,
  RW[] THEN FS[ALL_DISTINCT_APPEND; distinct_lists_def; EVERY_MEM; MEM_APPEND] THEN
  ASM_MESON_TAC[]);;

let distinct_lists_append_right_elim = prove
 (`distinct_lists (xs:A list) (APPEND ys zs)
   ==> distinct_lists xs ys /\ distinct_lists xs zs`,
  FS[distinct_lists_def; EVERY_MEM; MEM_APPEND] THEN MESON_TAC[]);;

let opt_mmap_flookup_update = prove
 (`OPT_MMAP (FLOOKUP (fm:(A,B)fmap)) xs = SOME ys /\ ~MEM x xs
   ==> OPT_MMAP (FLOOKUP (fm |+ (x,y))) xs = SOME ys`,
  RW[] THEN FS[opt_mmap_eq_some; MAP_EQ_EVERY2; LIST_REL_EL_EQN] THEN
  RW[] THEN FS[FLOOKUP_UPDATE; list_MEM_EL] THEN ASM_MESON_TAC[]);;

let opt_mmap_some_eq_zip_flookup = prove
 (`!xs (f:(A,B)fmap) ys.
     ALL_DISTINCT xs /\ LENGTH xs = LENGTH ys
     ==> OPT_MMAP (FLOOKUP (f |++ ZIP xs ys)) xs = SOME ys`,
  LIST_INDUCT_TAC THEN RW[OPT_MMAP_def] THEN FS[] THEN
  NAMED_CASES_ON "ys" ["";"h' t'"] THEN FS[] THEN FS[ZIP; HD; TL; FUPDATE_LIST_THM] THEN
  QBY "~MEM (h:A) (MAP FST (ZIP t (t':B list)))" (ASM_SIMP_TAC[MAP_ZIP]) THEN
  DRULE FUPDATE_FUPDATE_LIST_COMMUTES THEN
  DISCH_THEN (QSPECL_THEN ["f"; "h'"] ASSUME_TAC) THEN
  FS[FLOOKUP_DEF; FDOM_FUPDATE; IN_INSERT; FAPPLY_FUPDATE_THM]);;

let opt_mmap_disj_zip_flookup = prove
 (`!xs (f:(A,B)fmap) ys zs.
     distinct_lists xs ys /\ LENGTH xs = LENGTH zs
     ==> OPT_MMAP (FLOOKUP (f |++ ZIP xs zs)) ys = OPT_MMAP (FLOOKUP f) ys`,
  LIST_INDUCT_TAC THEN RW[] THEN FS[distinct_lists_def] THENL
   [FS[FUPDATE_LIST_THM; ZIP]; ALL_TAC] THEN
  NAMED_CASES_ON "zs" ["";"h' t'"] THEN FS[] THEN FS[FUPDATE_LIST_THM; ZIP; HD; TL] THEN
  MATCH_MP_TAC IMP_OPT_MMAP_EQ THEN MATCH_MP_TAC MAP_CONG THEN FS[] THEN RW[] THEN
  FS[FLOOKUP_UPDATE] THEN ASM_MESON_TAC[]);;

let genlist_distinct_max = prove
 (`!n ys m. (!y. MEM y ys ==> y <= m)
            ==> distinct_lists (list_of_seq (\x. SUC x + m) n) ys`,
  RW[] THEN FS[distinct_lists_def; EVERY_GENLIST] THEN RW[] THEN
  CCONTR_TAC THEN FS[] THEN FIRST_X_ASSUM DRULE THEN DECIDE_TAC);;

let genlist_distinct_max' = prove
 (`!n ys m p. (!y. MEM y ys ==> y <= m)
              ==> distinct_lists (list_of_seq (\x. SUC x + (m + p)) n) ys`,
  RW[] THEN FS[distinct_lists_def; EVERY_GENLIST] THEN RW[] THEN
  CCONTR_TAC THEN FS[] THEN FIRST_X_ASSUM DRULE THEN DECIDE_TAC);;

(* HOL4: by induction on n with ADD_MONO_LESS_EQ, LESS_EQ_SUC_REFL and     *)
(* LESS_EQ_TRANS; here from MEM_GENLIST                                    *)

let mem_genlist_add_suc_val = prove
 (`!n x k. MEM x (list_of_seq (\x. SUC x + k) n) ==> k < x /\ x <= n + k`,
  REWRITE_TAC[MEM_GENLIST] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_ARITH_TAC);;

let update_eq_zip_flookup = prove
 (`!xs (f:(A,B)fmap) ys n.
     ALL_DISTINCT xs /\ LENGTH xs = LENGTH ys /\ n < LENGTH xs
     ==> FLOOKUP (f |++ ZIP xs ys) (EL n xs) = SOME (EL n ys)`,
  LIST_INDUCT_TAC THEN RW[FUPDATE_LIST_THM] THENL [FS[ARITH_ss]; ALL_TAC] THEN
  NAMED_CASES_ON "ys" ["";"h' t'"] THEN FS[FUPDATE_LIST_THM; ZIP; HD; TL] THEN
  QBY "~MEM (h:A) (MAP FST (ZIP t (t':B list)))" (ASM_SIMP_TAC[MAP_ZIP]) THEN
  NAMED_CASES_ON "n" ["";"n'"] THEN FS[EL; HD; TL; LT_SUC] THEN
  DRULE FUPDATE_FUPDATE_LIST_COMMUTES THEN
  DISCH_THEN (QSPECL_THEN ["f"; "h'"] ASSUME_TAC) THEN
  FS[FLOOKUP_DEF; FDOM_FUPDATE; IN_INSERT; FAPPLY_FUPDATE_THM]);;

(* HOL4 cases on ~MEM h (MAP FST (ZIP ..)) and, when h is in xs, takes it  *)
(* as EL n xs with MEM_MAP and MEM_ZIP; here MEM h xs with list_MEM_EL     *)

let update_eq_zip_map_flookup = prove
 (`!xs (f:(A,B)fmap) n m.
     n < LENGTH xs
     ==> FLOOKUP (f |++ ZIP xs (MAP (\x. m) xs)) (EL n xs) = SOME m`,
  LIST_INDUCT_TAC THEN RW[FUPDATE_LIST_THM] THENL [FS[ARITH_ss]; ALL_TAC] THEN
  NAMED_CASES_ON "n" ["";"n'"] THEN
  FS[ZIP; HD; TL; MAP; EL; LT_SUC; FUPDATE_LIST_THM] THEN
  ASM_CASES_TAC `MEM (h:A) t` THENL
   [FS[list_MEM_EL] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    QBY "~MEM (h:A) (MAP FST (ZIP t (MAP (\x:A. (m:B)) t)))"
      (ASM_SIMP_TAC[MAP_ZIP; LENGTH_MAP]) THEN
    DRULE FUPDATE_FUPDATE_LIST_COMMUTES THEN
    DISCH_THEN (QSPECL_THEN ["f"; "m"] ASSUME_TAC) THEN
    FS[FLOOKUP_DEF; FDOM_FUPDATE; IN_INSERT; FAPPLY_FUPDATE_THM]]);;

let flookup_fupdate_zip_not_mem = prove
 (`!xs ys (f:(A,B)fmap) n.
     LENGTH xs = LENGTH ys /\ ~MEM n xs
     ==> FLOOKUP (f |++ ZIP xs ys) n = FLOOKUP f n`,
  LIST_INDUCT_TAC THEN RW[FUPDATE_LIST_THM; ZIP] THEN
  NAMED_CASES_ON "ys" ["";"h' t'"] THEN FS[FUPDATE_LIST_THM; ZIP; HD; TL] THEN
  ASM_MESON_TAC[FLOOKUP_UPDATE]);;

(* HOL4 quantifies an unused n (of a free type) and leaves zs free *)

let map_flookup_fupdate_zip_not_mem = prove
 (`!xs ys (f:(A,B)fmap) (n:C).
     distinct_lists xs ys /\ LENGTH xs = LENGTH (zs:B list)
     ==> MAP (FLOOKUP (f |++ ZIP xs zs)) ys = MAP (FLOOKUP f) ys`,
  RW[] THEN FS[MAP_EQ_EVERY2] THEN MATCH_MP_TAC EVERY2_refl THEN RW[] THEN
  FS[distinct_lists_def; EVERY_MEM] THEN
  MATCH_MP_TAC flookup_fupdate_zip_not_mem THEN ASM_MESON_TAC[]);;

let domsub_commutes_fupdate = prove
 (`!xs ys (fm:(A,B)fmap) x.
     ~MEM x xs /\ LENGTH xs = LENGTH ys
     ==> (fm |++ ZIP xs ys) \\ x = (fm \\ x) |++ ZIP xs ys`,
  LIST_INDUCT_TAC THEN RW[] THENL [FS[FUPDATE_LIST_THM; ZIP]; ALL_TAC] THEN
  NAMED_CASES_ON "ys" ["";"h' t'"] THEN FS[] THEN FS[FUPDATE_LIST_THM; ZIP; HD; TL] THEN
  ASM_MESON_TAC[DOMSUB_FUPDATE_NEQ]);;

let map_the_some_cancel = prove
 (`!xs:A list. MAP (THE o SOME) xs = xs`,
  LIST_INDUCT_TAC THEN RW[MAP; o_THM; THE_DEF]);;

(* HOL4 [local] *)

let FUPDATE_LIST_APPLY_NOT_MEM_ZIP = prove
 (`!l1 l2 (f:(A,B)fmap) k.
     LENGTH l1 = LENGTH l2 /\ ~MEM k l1 ==> FAPPLY (f |++ ZIP l1 l2) k = FAPPLY f k`,
  MESON_TAC[FUPDATE_LIST_APPLY_NOT_MEM; MAP_ZIP]);;

let fm_multi_update = prove
 (`!xs ys a b c d (fm:(A,B)fmap).
     ~MEM a xs /\ ~MEM c xs /\ ~(a = c) /\ LENGTH xs = LENGTH ys
     ==> fm |++ (CONS (a,b) (CONS (c,d) (ZIP xs ys))) |++ (CONS (a,b) (ZIP xs ys)) =
         fm |++ (CONS (a,b) (CONS (c,d) (ZIP xs ys)))`,
  FS[FUPDATE_LIST_THM; GSYM fmap_EQ_THM; FDOM_FUPDATE; FDOM_FUPDATE_LIST] THEN
  REPEAT STRIP_TAC THENL
   [SET_TAC[]; ALL_TAC; ALL_TAC; ALL_TAC; ALL_TAC; ALL_TAC; ALL_TAC] THEN
  FS[FUPDATE_LIST_APPLY_NOT_MEM_ZIP; FAPPLY_FUPDATE_THM] THEN
  (ASM_CASES_TAC `MEM (x:A) xs` THENL
    [MATCH_MP_TAC FUPDATE_SAME_LIST_APPLY THEN ASM_SIMP_TAC[MAP_ZIP];
     RW[FUPDATE_LIST_APPLY_NOT_MEM_ZIP; FAPPLY_FUPDATE_THM] THEN
     FS[MAP_ZIP; IN_SET_OF_LIST]]));;

let el_reduc_tl = prove
 (`!l n. 0 < n /\ n < LENGTH (l:A list) ==> EL n l = EL (n - 1) (TL l)`,
  LIST_INDUCT_TAC THEN RW[] THEN NAMED_CASES_ON "n" ["";"n'"] THEN
  FS[ARITH_ss; EL; TL; SUC_SUB1]);;

(* HOL4: the simplifier decides 0w = n2w (i + 1) for word5 as             *)
(* (i + 1) MOD 32 = 0; here by val and DIMINDEX_CONV                      *)

let zero_not_mem_genlist_offset = prove
 (`!t:A list.
     LENGTH t <= 31
     ==> ~MEM (word 0) (MAP (word:num->5 word) (list_of_seq (\i. i + 1) (LENGTH t)))`,
  REWRITE_TAC[MEM_MAP; MEM_GENLIST] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o AP_TERM `val:5 word->num`) THEN
  ASM_REWRITE_TAC[VAL_WORD; DIMINDEX_CONV `dimindex(:5)`] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  SUBGOAL_THEN `(m + 1) MOD 32 = m + 1` SUBST1_TAC THENL
   [MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ARITH_TAC]);;

let all_distinct_take = prove
 (`!ns n. ALL_DISTINCT (ns:A list) /\ n <= LENGTH ns ==> ALL_DISTINCT (TAKE n ns)`,
  LIST_INDUCT_TAC THEN RW[] THEN FS[] THEN NAMED_CASES_ON "n" ["";"n'"] THEN
  FS[TAKE; LE_SUC] THEN ASM_MESON_TAC[MEM_TAKE]);;

let all_distinct_drop = prove
 (`!ns n. ALL_DISTINCT (ns:A list) /\ n <= LENGTH ns ==> ALL_DISTINCT (DROP n ns)`,
  LIST_INDUCT_TAC THEN RW[] THEN FS[] THEN NAMED_CASES_ON "n" ["";"n'"] THEN
  FS[DROP; LE_SUC] THEN ASM_MESON_TAC[MEM_DROP_IMP]);;

let disjoint_take_drop_sum = prove
 (`!n m p (ns:A list).
     ALL_DISTINCT ns
     ==> DISJOINT (set_of_list (TAKE n ns))
                  (set_of_list (TAKE p (DROP (n + m) ns)))`,
  INDUCT_TAC THEN RW[] THEN NAMED_CASES_ON "ns" ["";"h t"] THEN
  FS[TAKE; DROP; TAKE_def; DROP_def; ADD_CLAUSES; set_of_list; DISJOINT_EMPTY;
     DISJOINT_INSERT] THEN
  REWRITE_TAC[IN_SET_OF_LIST] THEN DISCH_THEN(MP_TAC o MATCH_MP MEM_TAKE) THEN
  DISCH_THEN(MP_TAC o MATCH_MP MEM_DROP_IMP) THEN ASM_REWRITE_TAC[]);;

(* HOL4 repeats the induction; here by DISJOINT_SYM *)

let disjoint_drop_take_sum = prove
 (`!n m p (ns:A list).
     ALL_DISTINCT ns
     ==> DISJOINT (set_of_list (TAKE p (DROP (n + m) ns)))
                  (set_of_list (TAKE n ns))`,
  ONCE_REWRITE_TAC[DISJOINT_SYM] THEN REWRITE_TAC[disjoint_take_drop_sum]);;

let fm_empty_zip_alist = prove
 (`!xs ys. LENGTH xs = LENGTH ys /\ ALL_DISTINCT xs
           ==> FEMPTY |++ ZIP xs ys = alist_to_fmap (ZIP xs ys):(A,B)fmap`,
  LIST_INDUCT_TAC THEN RW[] THENL [FS[FUPDATE_LIST_THM; ZIP; alist_to_fmap_thm]; ALL_TAC] THEN
  NAMED_CASES_ON "ys" ["";"h' t'"] THEN FS[] THEN
  FS[FUPDATE_LIST_THM; ZIP; HD; TL; alist_to_fmap_thm] THEN
  FIRST_X_ASSUM (QSPECL_THEN ["t'"] ASSUME_TAC) THEN RFS[] THEN
  POP_ASSUM (ASSUME_TAC o GSYM) THEN FS[] THEN
  MATCH_MP_TAC FUPDATE_FUPDATE_LIST_COMMUTES THEN ASM_SIMP_TAC[MAP_ZIP]);;

(* HOL4: by induction on xs; here (x,y) is in the list by ALOOKUP of the   *)
(* update list (flookup_update_list_some, alookup_distinct_reverse)        *)

let fm_empty_zip_flookup = prove
 (`!xs ys (x:A) (y:B).
     LENGTH xs = LENGTH ys /\ ALL_DISTINCT xs /\
     FLOOKUP (FEMPTY |++ ZIP xs ys) x = SOME y
     ==> ?n. n < LENGTH xs /\ EL n (ZIP xs ys) = (x,y)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `MEM (x:A,y:B) (ZIP xs ys)` MP_TAC THENL
   [MATCH_MP_TAC ALOOKUP_MEM THEN
    FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[flookup_update_list_some]) THEN
    ASM_SIMP_TAC[alookup_distinct_reverse; MAP_ZIP; FLOOKUP_EMPTY; option_DISTINCT];
    ASM_SIMP_TAC[list_MEM_EL; LENGTH_ZIP] THEN MESON_TAC[]]);;

(* HOL4: by induction on xs; here from update_eq_zip_flookup and EL_ZIP *)

let fm_empty_zip_flookup_el = prove
 (`!xs ys zs n (x:A).
     ALL_DISTINCT xs /\ LENGTH xs = LENGTH ys /\ LENGTH ys = LENGTH (zs:C list) /\
     n < LENGTH xs /\ EL n xs = x
     ==> FLOOKUP (FEMPTY |++ ZIP xs (ZIP ys zs)) x = SOME (EL n ys:B,EL n zs)`,
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  MP_TAC(ISPECL [`xs:A list`; `FEMPTY:(A,B#C)fmap`; `ZIP (ys:B list) (zs:C list)`;
                 `n:num`] update_eq_zip_flookup) THEN
  ASM_SIMP_TAC[LENGTH_ZIP] THEN DISCH_THEN SUBST1_TAC THEN
  AP_TERM_TAC THEN MATCH_MP_TAC EL_ZIP THEN ASM_MESON_TAC[]);;

let all_distinct_flookup_all_distinct = prove
 (`pan_commonProps_no_overlap (fm:(A,B#(C)list)fmap) /\ FLOOKUP fm x = SOME (y,zs)
   ==> ALL_DISTINCT zs`,
  RW[] THEN FS[pan_commonProps_no_overlap_def] THEN ASM_MESON_TAC[]);;

let no_overlap_flookup_distinct = prove
 (`pan_commonProps_no_overlap (fm:(A,B#(C)list)fmap) /\ ~(x = y) /\
   FLOOKUP fm x = SOME (a,xs) /\ FLOOKUP fm y = SOME (b,ys)
   ==> distinct_lists xs ys`,
  RW[] THEN MATCH_MP_TAC distinct_lists_append THEN
  FS[pan_commonProps_no_overlap_def; ALL_DISTINCT_APPEND; DISJOINT_ALT;
     IN_SET_OF_LIST] THEN
  ASM_MESON_TAC[]);;

let all_distinct_take_frop_disjoint = prove
 (`!ns n. ALL_DISTINCT (ns:A list) /\ n <= LENGTH ns
          ==> DISJOINT (set_of_list (TAKE n ns)) (set_of_list (DROP n ns))`,
  LIST_INDUCT_TAC THEN RW[] THEN NAMED_CASES_ON "n" ["";"n'"] THEN
  FS[TAKE; DROP; set_of_list; DISJOINT_EMPTY; DISJOINT_INSERT; LE_SUC] THEN
  REWRITE_TAC[IN_SET_OF_LIST] THEN DISCH_THEN(MP_TAC o MATCH_MP MEM_DROP_IMP) THEN
  ASM_REWRITE_TAC[]);;

(* HOL4: by induction on xs; here both sides by flookup_fupdate_list *)

let fupdate_flookup_zip_elim = prove
 (`!xs ys zs as (x:A).
     FLOOKUP (FEMPTY |++ ZIP xs ys) x = NONE /\
     LENGTH zs = LENGTH as /\ LENGTH xs = LENGTH (ys:B list) /\ ALL_DISTINCT xs
     ==> FLOOKUP (FEMPTY |++ ZIP xs ys |++ ZIP zs as) x =
         FLOOKUP (FEMPTY |++ ZIP zs as) x`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[flookup_fupdate_list] THEN
  ASM_REWRITE_TAC[FLOOKUP_EMPTY]);;

(* HOL4: by induction on xs; here from flookup_fupdate_zip_not_mem *)

let not_mem_fst_zip_flookup_empty = prove
 (`!xs ys (x:A).
     ~MEM x xs /\ ALL_DISTINCT xs /\ LENGTH xs = LENGTH (ys:B list)
     ==> FLOOKUP (FEMPTY |++ ZIP xs ys) x = NONE`,
  ASM_SIMP_TAC[flookup_fupdate_zip_not_mem; FLOOKUP_EMPTY]);;

let fm_zip_append_take_drop = prove
 (`!xs ys zs (f:(A,B)fmap).
     ALL_DISTINCT xs /\ LENGTH xs = LENGTH (APPEND ys zs)
     ==> f |++ ZIP xs (APPEND ys zs) =
         f |++ ZIP (TAKE (LENGTH ys) xs) ys |++ ZIP (DROP (LENGTH ys) xs) zs`,
  LIST_INDUCT_TAC THEN RW[] THENL [FS[FUPDATE_LIST_THM]; ALL_TAC] THEN
  NAMED_CASES_ON "ys" ["";"h' t'"] THEN
  FS[FUPDATE_LIST_THM; ZIP; HD; TL; TAKE; DROP; LENGTH; APPEND; SUC_SUB1]);;

let disjoint_not_mem_el = prove
 (`!xs ys n. DISJOINT (set_of_list (xs:A list)) (set_of_list ys) /\ n < LENGTH xs
             ==> ~MEM (EL n xs) ys`,
  LIST_INDUCT_TAC THEN RW[] THEN NAMED_CASES_ON "n" ["";"n'"] THEN
  FS[ARITH_ss; EL; HD; TL; LT_SUC; set_of_list; DISJOINT_INSERT; IN_SET_OF_LIST]);;

let map_some_the_map = prove
 (`!xs ys (f:A->B option). MAP f xs = MAP SOME ys ==> MAP (\n. THE (f n)) xs = ys`,
  LIST_INDUCT_TAC THEN RW[] THEN NAMED_CASES_ON "ys" ["";"h' t'"] THEN
  FS[MAP; THE_DEF; CONS_11] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

let set_eq_membership = prove
 (`a = b /\ (x:A) IN a ==> x IN b`,
  RW[] THEN FS[]);;

let max_set_MAX_LIST = prove
 (`!xs. MAX_SET (set_of_list xs) = MAX_LIST xs`,
  LIST_INDUCT_TAC THEN RW[set_of_list; MAX_LIST_def; MAX_SET_THM; FINITE_SET_OF_LIST]);;

(* HOL4: by induction on xs; here every member is at most MAX_LIST xs     *)
(* (MAX_LIST_PROPERTY)                                                     *)

let MAX_LIST_add_not_mem = prove
 (`!xs. ~MEM (MAX_LIST xs + 1) xs`,
  GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP MAX_LIST_PROPERTY) THEN ARITH_TAC);;

(* the values of a num_set are one (HOL4 ()): the theorem one *)

let subspt_same_insert_subspt = prove
 (`!p q n. subspt p q ==> subspt (insert n one p) (insert n one (q:num_set))`,
  RW[] THEN FS[subspt_lookup] THEN RW[] THEN FS[lookup_insert] THEN
  POP_ASSUM MP_TAC THEN COND_CASES_TAC THEN FS[]);;

let subspt_insert = prove
 (`!p n. subspt p (insert n one (p:num_set))`,
  RW[] THEN FS[subspt_lookup] THEN RW[] THEN FS[lookup_insert] THEN
  COND_CASES_TAC THEN REWRITE_TAC[option_INJ] THEN MESON_TAC[one]);;

let subspt_right_insert_subspt = prove
 (`!p q n. subspt p q ==> subspt p (insert n one (q:num_set))`,
  RW[] THEN FS[subspt_lookup] THEN RW[] THEN FS[lookup_insert] THEN
  COND_CASES_TAC THEN ASM_SIMP_TAC[option_INJ] THEN MESON_TAC[one]);;

let subspt_same_insert_cancel = prove
 (`!p q n m.
     subspt p q
     ==> subspt (insert n one (insert m one (insert n one p)))
                (insert m one (insert n one (q:num_set)))`,
  RW[] THEN FS[subspt_lookup] THEN RW[] THEN FS[lookup_insert] THEN
  POP_ASSUM MP_TAC THEN ONCE_REWRITE_TAC[one] THEN REPEAT COND_CASES_TAC THEN
  REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

let max_set_count_length = prove
 (`!n. MAX_SET (pred_set_count n) = n - 1`,
  INDUCT_TAC THEN RW[] THENL
   [REWRITE_TAC[pred_set_count_DEF; LT; EMPTY_GSPEC; MAX_SET_THM] THEN ARITH_TAC; ALL_TAC] THEN
  FS[COUNT_SUC] THEN
  QBY "MAX_SET (n INSERT pred_set_count n) = MAX n (MAX_SET (pred_set_count n))"
    (QBY "FINITE (pred_set_count n)" (REWRITE_TAC[FINITE_COUNT]) THEN
     ASM_MESON_TAC[MAX_SET_THM]) THEN
  FS[MAX_DEF] THEN ARITH_TAC);;

let MAX_LIST_i_genlist = prove
 (`!n. MAX_LIST (list_of_seq I n) = n - 1`,
  RW[] THEN FS[GSYM COUNT_LIST_GENLIST] THEN FS[GSYM max_set_MAX_LIST] THEN
  FS[COUNT_LIST_COUNT] THEN MESON_TAC[max_set_count_length]);;

(* HOL4: by induction on xs; here by EL_MAP *)

let el_pair_map_fst_el = prove
 (`!xs n (x:A) (y:B) (z:C).
     n < LENGTH xs /\ EL n xs = (x,y,z) ==> x = EL n (MAP FST xs)`,
  SIMP_TAC[EL_MAP; FST]);;

(* HOL4: by induction on xs; here by ALL_DISTINCT_EL_IMP on MAP FST xs *)

let all_distinct_el_fst_same_eq = prove
 (`!xs n n' (x:A) (y:B) y'.
     ALL_DISTINCT (MAP FST xs) /\ n < LENGTH xs /\ n' < LENGTH xs /\
     EL n xs = (x,y) /\ EL n' xs = (x,y')
     ==> n = n'`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`MAP FST (xs:(A#B)list)`; `n:num`; `n':num`] ALL_DISTINCT_EL_IMP) THEN
  ASM_SIMP_TAC[LENGTH_MAP; EL_MAP; FST]);;

let lookup_some_el = prove
 (`!xs n (x:A). lookup n (fromAList xs) = SOME x
                ==> ?m. m < LENGTH xs /\ EL m xs = (n,x)`,
  RW[lookup_fromAList] THEN IMP_RES_TAC ALOOKUP_MEM THEN GVS[list_MEM_EL] THEN
  ASM_MESON_TAC[]);;

let max_foldr_lt = prove
 (`!xs x n m. MEM x xs /\ n <= x /\ 0 < m ==> x < ITLIST MAX xs n + m`,
  LIST_INDUCT_TAC THEN RW[ITLIST; MEM] THEN FS[] THENL
   [FS[MAX_DEF] THEN COND_CASES_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM (DRULE_ALL) THEN STRIP_TAC THEN FS[MAX_DEF] THEN
  COND_CASES_TAC THEN ASM_ARITH_TAC);;

let fm_update_diff_vars = prove
 (`~(a = b)
   ==> (fm:(A,B)fmap) |+ (a,a') |+ (b,b') |+ (a,a') |+ (b,b'') =
       fm |+ (a,a') |+ (b,b'')`,
  RW[] THEN
  QBY "(fm:(A,B)fmap) |+ (a,a') |+ (b,b') |+ (a,a') |+ (b,b'') =
       fm |+ (a,a') |+ (b,b') |+ (b,b'') |+ (a,a')"
    (MATCH_MP_TAC FUPDATE_COMMUTES THEN FS[]) THEN
  FS[FUPDATE_EQ] THEN
  QBY "(fm:(A,B)fmap) |+ (a,a') |+ (b,b'') |+ (a,a') =
       fm |+ (a,a') |+ (a,a') |+ (b,b'')"
    (MATCH_MP_TAC FUPDATE_COMMUTES THEN FS[]) THEN
  FS[FUPDATE_EQ]);;

(* HOL4 \(x,y). (x,y) is \p. match p with (x,y) -> (x,y); HOL4 rewrites it *)
(* with MAP_values_fmap_to_alist, here it is the identity (MAP_ID)          *)

let fmap_to_alist_eq_fm = prove
 (CASE_TERM `!fm:(A,B)fmap.
     FEMPTY |++ MAP (\p. match p with (x,y) -> (x,y)) (fmap_to_alist fm) = fm`,
  GEN_TAC THEN
  QBY "MAP (\p:A#B. pair_CASE p (\x y. (x,y))) (fmap_to_alist fm) = fmap_to_alist fm"
    (GEN_REWRITE_TAC RAND_CONV [GSYM MAP_ID] THEN MATCH_MP_TAC MAP_CONG THEN
     REWRITE_TAC[FORALL_PAIR_THM; pair_CASE; I_THM]) THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[FUPDATE_LIST_EQ_APPEND_REVERSE; fmap_to_alist_FEMPTY; APPEND_NIL] THEN
  QBY "alist_to_fmap (REVERSE (fmap_to_alist fm)) =
       alist_to_fmap (fmap_to_alist (fm:(A,B)fmap))"
    (MATCH_MP_TAC ALL_DISTINCT_alist_to_fmap_REVERSE THEN
     REWRITE_TAC[ALL_DISTINCT_fmap_to_alist_keys]) THEN
  ASM_REWRITE_TAC[fmap_to_alist_to_fmap]);;

let MAP3_MAP2 = prove
 (`!l1 l2 l3 (f:A->B->C->D).
     LENGTH l1 = LENGTH l3 /\ LENGTH l2 = LENGTH l3
     ==> MAP3 f l1 l2 l3 = MAP2 (UNCURRY f) (ZIP l1 l2) l3`,
  LIST_INDUCT_TAC THEN FS[] THEN REPEAT STRIP_TAC THEN QCASES_ON "l3" THEN
  QCASES_ON "l2" THEN FS[ZIP; MAP2; HD; TL; UNCURRY_DEF; MAP3_def]);;

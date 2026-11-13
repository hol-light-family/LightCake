(* ========================================================================= *)
(* misc_p3: port of HOL4 misc/miscScript.sml (CakeML v3479), part 3 of 3:   *)
(* lines 3036-4478 of the script (SUM_COUNT_LIST .. TotOrd_pair_cmp).       *)
(* Miscellaneous definitions and minor lemmas used throughout the           *)
(* development (lists, options, finite maps, words, sptrees, bytes).        *)
(* ========================================================================= *)

needs "hol4/vocab.ml";;
needs "hol4/list.ml";;
needs "hol4/rich_list.ml";;
needs "hol4/basic.ml";;
needs "hol4/finite_map.ml";;
needs "hol4/alist.ml";;
needs "hol4/sptree.ml";;
needs "hol4/words4.ml";;
needs "hol4/ternaryComparisons.ml";;
needs "hol4/toto.ml";;
needs "hol4/comparison.ml";;
needs "hol4/string4.ml";;
needs "hol4/bitstring.ml";;
needs "hol4/llist.ml";;
needs "hol4/path.ml";;
needs "hol4/set_sep.ml";;
needs "hol4/sorting.ml";;
needs "hol4/bag.ml";;
needs "misc/misc_p2.ml";;

prioritize_num();;
type_invention_error := true;;

(* Helper lemmas that are not HOL4 theorems are named MISC3AUX_.             *)

(* used once; HOL4: SUM_MAP_COUNT_LIST at k = 0, simplified with srw_ss *)
let SUM_COUNT_LIST = prove
 (`SUM (MAP ((+) 0) (COUNT_LIST n)) = (n * (n - 1)) DIV 2`,
  REWRITE_TAC[SUM_MAP_COUNT_LIST; MULT_CLAUSES; ADD_CLAUSES]);;

let OPTION_MAP_I = prove
 (`OPTION_MAP I (x:A option) = x`,
  CASES_ON `x:A option` THEN RW[OPTION_MAP_DEF; I_THM]);;
let _ = cake_add_simps [OPTION_MAP_I];;

(* should be made an iff in conclusion *)
let OPTION_MAP_INJ = prove
 (`(!x y. (f:A->B) x = f y ==> x = y)
   ==> !o1 o2. OPTION_MAP f o1 = OPTION_MAP f o2 ==> o1 = o2`,
  STRIP_TAC THEN GEN_TAC THEN GEN_TAC THEN
  CASES_ON `o1:A option` THEN CASES_ON `o2:A option` THEN
  SIMP[OPTION_MAP_DEF] THEN ASM_MESON_TAC[]);;

let the_OPTION_MAP = prove
 (`!(f:A->A) d opt.
     f d = d ==>
     the d (OPTION_MAP f opt) = f (the d opt)`,
  REPEAT STRIP_TAC THEN CASES_ON `opt:A option` THEN
  ASM_REWRITE_TAC[OPTION_MAP_DEF; the_def]);;

let TAKE_FLAT_REPLICATE_LEQ = prove
 (`!j k (ls:A list) len.
     len = LENGTH ls /\ k <= j ==>
     TAKE (k * len) (FLAT (REPLICATE j ls)) = FLAT (REPLICATE k ls)`,
  INDUCT_TAC THEN SIMP[REPLICATE; LE] THEN
  INDUCT_TAC THEN SIMP[REPLICATE; FLAT; MULT_CLAUSES; TAKE_0] THEN
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[TAKE_APPEND2; ARITH_RULE `n <= m + n:num`; ADD_SUB] THEN
  AP_TERM_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC);;

let MOD_2EXP_0_EVEN = prove
 (`!x y. 0 < x /\ MOD_2EXP x y = 0 ==> EVEN y`,
  REWRITE_TAC[MOD_2EXP_def; MOD_EQ_0] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[EVEN_MULT; EVEN_EXP; ARITH] THEN ASM_ARITH_TAC);;

let ADD_MOD_EQ_LEMMA = prove
 (`k MOD d = 0 /\ n < d ==> (k + n) MOD d = n`,
  STRIP_TAC THEN MATCH_MP_TAC MOD_UNIQ THEN
  EXISTS_TAC `k DIV d` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`k:num`; `d:num`] DIVISION) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ASM_REWRITE_TAC[ADD_CLAUSES]] THEN
  ARITH_TAC);;

(* should be set l1 SUBSET set l2 *)
let list_subset_def = cake_def
 `list_subset (l1:A list) l2 = ALL (\x. MEM x l2) l1`;;

let list_set_eq_def = cake_def
 `list_set_eq (l1:A list) l2 <=> list_subset l1 l2 /\ list_subset l2 l1`;;

let list_subset_LENGTH = prove
 (`!l1 (l2:A list). ALL_DISTINCT l1 /\ list_subset l1 l2 ==>
                    LENGTH l1 <= LENGTH l2`,
  REWRITE_TAC[list_subset_def; GSYM ALL_MEM] THEN
  LIST_INDUCT_TAC THEN REWRITE_TAC[LENGTH; LE_0; ALL_DISTINCT; MEM] THEN
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `FILTER ((~) o ((=) (h:A))) l2`) THEN
  REWRITE_TAC[MEM_FILTER; o_THM] THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `LENGTH (FILTER ((~) o ((=) (h:A))) l2) < LENGTH l2`
    MP_TAC THENL
   [MATCH_MP_TAC LENGTH_FILTER_LESS THEN
    REWRITE_TAC[EXISTS_MEM; o_THM] THEN ASM_MESON_TAC[];
    ARITH_TAC]);;

let BIJ_UPDATE = prove
 (`!(f:A->B) s t x y. BIJ f s t /\ ~(x IN s) /\ ~(y IN t) ==>
     BIJ ((x =+ y) f) (x INSERT s) (y INSERT t)`,
  REWRITE_TAC[BIJ; SURJ; INJ; IN_INSERT; APPLY_UPDATE_THM] THEN
  MESON_TAC[]);;

let INJ_UPDATE = prove
 (`INJ (f:A->B) s t /\ ~(x IN s) /\ ~(y IN t) ==>
   INJ ((x =+ y) f) (x INSERT s) (y INSERT t)`,
  REWRITE_TAC[BIJ; SURJ; INJ; IN_INSERT; APPLY_UPDATE_THM] THEN
  MESON_TAC[]);;

(* TODO: candidate for move to HOL;
         subspt_domain exists already but is specialised to unit *)
let subspt_domain_SUBSET = prove
 (`subspt (t1:A spt) t2 ==> domain t1 SUBSET domain t2`,
  SIMP_TAC[subspt_def; SUBSET]);;

(* Some temporal logic definitions based on lazy lists *)
(* move into llistTheory? *)

let SPLITP_TAKE_DROP = prove
 (`!P i (l:A list). ALL ((~) o P) (TAKE i l) ==>
     P (EL i l) ==>
     SPLITP P l = (TAKE i l, DROP i l)`,
  GEN_TAC THEN ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN
  LIST_INDUCT_TAC THEN REWRITE_TAC[SPLITP_DEF; TAKE_def; DROP_def] THEN
  INDUCT_TAC THEN REWRITE_TAC[ALL; EL; HD; TL; NOT_SUC; SUC_SUB1; o_THM] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[PAIR_EQ] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[]);;

let SND_SPLITP_DROP = prove
 (`!P n (l:A list). ALL ((~) o P) (TAKE n l) ==>
     SND (SPLITP P (DROP n l)) = SND (SPLITP P l)`,
  GEN_TAC THEN INDUCT_TAC THEN REWRITE_TAC[DROP_0] THEN
  LIST_INDUCT_TAC THEN
  REWRITE_TAC[TAKE_def; DROP_def; SPLITP_DEF; NOT_SUC; SUC_SUB1; ALL; o_THM] THEN
  STRIP_TAC THEN ASM_SIMP_TAC[]);;

let FST_SPLITP_DROP = prove
 (`!P n (l:A list). ALL ((~) o P) (TAKE n l) ==>
     FST (SPLITP P l) = APPEND (TAKE n l) (FST (SPLITP P (DROP n l)))`,
  GEN_TAC THEN INDUCT_TAC THEN REWRITE_TAC[DROP_0; TAKE_0; APPEND] THEN
  LIST_INDUCT_TAC THEN
  REWRITE_TAC[TAKE_def; DROP_def; SPLITP_DEF; NOT_SUC; SUC_SUB1; ALL; o_THM;
              APPEND] THEN
  STRIP_TAC THEN ASM_SIMP_TAC[]);;

let TAKE_DROP_SUBLIST = prove
 (`(ll:A list) <<= DROP n ls /\ n < LENGTH ls /\ nlll = n + LENGTH ll ==>
   APPEND (APPEND (TAKE n ls) ll) (DROP nlll ls) = ls`,
  REWRITE_TAC[IS_PREFIX_APPEND] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `DROP (n + LENGTH (ll:A list)) (ls:A list) = l` SUBST1_TAC THENL
   [ONCE_REWRITE_TAC[ADD_SYM] THEN
    ASM_REWRITE_TAC[GSYM DROP_DROP_T; DROP_LENGTH_APPEND];
    MP_TAC(ISPECL [`n:num`; `ls:A list`] TAKE_DROP) THEN
    ASM_REWRITE_TAC[APPEND_ASSOC]]);;

(* helpers for the termination of Lnext *)
let MISC3AUX_eventually_ITER = prove
 (`!P (ll:A llist). eventually P ll ==> ?n. P (ITER n (\l. THE (LTL l)) ll)`,
  GEN_TAC THEN MATCH_MP_TAC eventually_ind THEN CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN EXISTS_TAC `0` THEN ASM_REWRITE_TAC[ITER_ALT];
    REPEAT STRIP_TAC THEN EXISTS_TAC `SUC n` THEN
    ASM_REWRITE_TAC[ITER_ALT; LTL_THM; THE_DEF]]);;

let MISC3AUX_Lnext_TC = prove
 (`!P (ll:A llist). eventually P ll /\ ~P ll ==>
     (minimal n. P (ITER n (\l. THE (LTL l)) (THE (LTL ll)))) <
     (minimal n. P (ITER n (\l. THE (LTL l)) ll))`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP MISC3AUX_eventually_ITER) THEN
  REWRITE_TAC[MINIMAL] THEN
  SPEC_TAC(`minimal n. P (ITER n (\l. THE (LTL l)) (ll:A llist))`,`k:num`) THEN
  GEN_TAC THEN STRUCT_CASES_TAC(SPEC `k:num` num_CASES) THEN
  REWRITE_TAC[ITER_ALT] THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC(ARITH_RULE `m <= n ==> m < SUC n`) THEN
  REWRITE_TAC[GSYM NOT_LT] THEN DISCH_TAC THEN
  MP_TAC(BETA_RULE(ISPEC `\m. (P:A llist->bool)
           (ITER m (\l. THE (LTL l)) (THE (LTL (ll:A llist))))` MINIMAL)) THEN
  REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o fst o EQ_IMP_RULE) THEN ANTS_TAC THENL
   [EXISTS_TAC `n:num` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `n:num` o CONJUNCT2) THEN ASM_REWRITE_TAC[]);;

(* computes the next position for which P holds *)
(* HOL4 Termination: a relation shown well founded by eventually_ind; here
   the measure of the distance to the next position where P holds *)
let misc_Lnext_def = cake_def_wf
 `measure (\p:(A llist->bool)#(A llist).
             minimal n. FST p (ITER n (\l. THE (LTL l)) (SND p)))`
 (REWRITE_TAC(FST::SND::WF_REL_THMS) THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC MISC3AUX_Lnext_TC THEN ASM_REWRITE_TAC[])
 `Lnext P (ll:A llist) = if eventually P ll then
                           if P ll then 0
                           else SUC (Lnext P (THE (LTL ll)))
                         else ARB`;;

let misc_Lnext_ind = CONV_RULE (GEN_ALPHA_CONV
  `P':(A llist->bool)->A llist->bool`) (cake_ind "Lnext");;

let misc_Lnext_pos_def = cake_def
 `Lnext_pos (ll:num llist) = Lnext (\ll. ?k. LHD ll = SOME k /\ ~(k = 0)) ll`;;

let OPTION_CHOICE_EQUALS_OPTION = prove
 (`!(x:A option) y z. (OPTION_CHOICE x y = SOME z) <=>
                      ((x = SOME z) \/ ((x = NONE) /\ (y = SOME z)))`,
  REPEAT GEN_TAC THEN CASES_ON `x:A option` THEN CASES_ON `y:A option` THEN
  SIMP[OPTION_CHOICE_DEF]);;

let option_eq_some = end_itlist CONJ
  [OPTION_IGNORE_BIND_EQUALS_OPTION; OPTION_BIND_EQUALS_OPTION;
   OPTION_CHOICE_EQUALS_OPTION];;

let ALL_DISTINCT_alist_to_fmap_REVERSE = prove
 (`ALL_DISTINCT (MAP FST (ls:(A#B)list)) ==>
   alist_to_fmap (REVERSE ls) = alist_to_fmap ls`,
  SPEC_TAC(`ls:(A#B)list`,`ls:(A#B)list`) THEN
  LIST_INDUCT_TAC THEN REWRITE_TAC[REVERSE; MAP; ALL_DISTINCT] THEN
  SPEC_TAC(`h:A#B`,`h:A#B`) THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN FS[] THEN
  ASM_SIMP_TAC[alist_to_fmap_APPEND; alist_to_fmap_thm; FUNION_FUPDATE_2;
               FUNION_FEMPTY_2; FDOM_alist_to_fmap; IN_SET_OF_LIST]);;

let FUPDATE_LIST_alist_to_fmap = prove
 (`!ls (fm:(A,B)fmap). fm |++ ls = FUNION (alist_to_fmap (REVERSE ls)) fm`,
  REWRITE_TAC[FUNION_alist_to_fmap; REVERSE_REVERSE]);;

let DISTINCT_FUPDATE_LIST_UNION = prove
 (`ALL_DISTINCT (MAP FST (ls:(A#B)list)) /\
   DISJOINT (FDOM f) (set_of_list (MAP FST ls)) ==>
   f |++ ls = FUNION f (alist_to_fmap ls)`,
  STRIP_TAC THEN
  ASM_SIMP_TAC[FUPDATE_LIST_alist_to_fmap; ALL_DISTINCT_alist_to_fmap_REVERSE] THEN
  MATCH_MP_TAC FUNION_COMM THEN
  ASM_REWRITE_TAC[FDOM_alist_to_fmap] THEN ASM_MESON_TAC[DISJOINT_SYM]);;

let fevery_to_drestrict = prove
 (`!P (m:(A,B)fmap) s. FEVERY P m ==> FEVERY P (DRESTRICT m s)`,
  REWRITE_TAC[FEVERY_ALL_FLOOKUP; FLOOKUP_DRESTRICT] THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[option_DISTINCT]);;

let SUM_MAP_K = prove
 (`!(f:A->num) ls c. (!x. f x = c) ==> SUM (MAP f ls) = LENGTH ls * c`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  ASM_SIMP_TAC[MAP; SUM; LENGTH; MULT_CLAUSES] THEN ARITH_TAC);;

let LAST_FLAT = prove
 (`!ls:(A list)list. ~NULL (FLAT ls) ==>
     (LAST (FLAT ls) = LAST (LAST (FILTER ((~) o NULL) ls)))`,
  MATCH_MP_TAC SNOC_INDUCT THEN REWRITE_TAC[FLAT; NULL] THEN
  REPEAT STRIP_TAC THEN FS[FLAT_SNOC; FILTER_SNOC; o_THM] THEN
  CASES_ON `x:A list` THEN FS[NULL; APPEND_NIL; LAST_APPEND_CONS; LAST_SNOC]);;

(* string4.ml defines TOKENS on char lists only: these two are about char lists *)
let TOKENS_unchanged = prove
 (`ALL ((~) o P) (ls:char list) ==> TOKENS P ls = if NULL ls then [] else [ls]`,
  STRUCT_CASES_TAC(ISPEC `ls:char list` list_CASES) THEN
  REWRITE_TAC[TOKENS_def; NULL] THEN DISCH_TAC THEN
  SUBGOAL_THEN `SPLITP (P:char->bool) (CONS h t) = (CONS h t,[])` SUBST1_TAC THENL
   [ASM_REWRITE_TAC[SPLITP_NIL_SND_EVERY];
    REWRITE_TAC[pair_CASE; NULL; TOKENS_def]]);;

let TOKENS_FLAT_MAP_SNOC = prove
 (`ALL (ALL (\y. ~(x = y))) (ls:(char list)list) /\ ALL ((~) o NULL) ls ==>
   TOKENS ((=) x) (FLAT (MAP (SNOC x) ls)) = ls`,
  SPEC_TAC(`ls:(char list)list`,`ls:(char list)list`) THEN
  LIST_INDUCT_TAC THEN REWRITE_TAC[MAP; FLAT; TOKENS_def; ALL; o_THM] THEN
  STRIP_TAC THEN
  REWRITE_TAC[SNOC_APPEND; GSYM APPEND_ASSOC; APPEND] THEN
  SIMP_TAC[TOKENS_APPEND] THEN ASM_SIMP_TAC[] THEN
  SUBGOAL_THEN `ALL ((~) o ((=) (x:char))) h` ASSUME_TAC THENL
   [UNDISCH_TAC `ALL (\y. ~((x:char) = y)) h` THEN
    MATCH_MP_TAC MONO_ALL THEN REWRITE_TAC[o_THM];
    ASM_SIMP_TAC[TOKENS_unchanged; APPEND]]);;

(* insert a string (l1) at specified index (n) in a list (l2) *)
let insert_atI_def = cake_def
 `insert_atI (l1:A list) n l2 =
    APPEND (APPEND (TAKE n l2) l1) (DROP (n + LENGTH l1) l2)`;;

let insert_atI_NIL = prove
 (`!n (l:A list). insert_atI [] n l = l`,
  REWRITE_TAC[insert_atI_def; APPEND_NIL; LENGTH; ADD_CLAUSES; TAKE_DROP]);;

let MISC3AUX_insert_atI_SUC = prove
 (`!l1 n x (l2:A list).
     insert_atI l1 (SUC n) (CONS x l2) = CONS x (insert_atI l1 n l2)`,
  REWRITE_TAC[insert_atI_def; TAKE_def; DROP_def; NOT_SUC; SUC_SUB1; APPEND;
              ADD_CLAUSES]);;

let MISC3AUX_insert_atI_0_CONS = prove
 (`!h t x (l:A list).
     insert_atI (CONS h t) 0 (CONS x l) = CONS h (insert_atI t 0 l)`,
  REWRITE_TAC[insert_atI_def; TAKE_0; DROP_def; NOT_SUC; SUC_SUB1; APPEND;
              ADD_CLAUSES; LENGTH]);;

let insert_atI_CONS = prove
 (`!n (l:A list) h t.
     n + LENGTH t < LENGTH l ==>
     insert_atI (CONS h t) n l = LUPDATE h n (insert_atI t (n + 1) l)`,
  INDUCT_TAC THEN GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `l:A list` list_CASES) THEN
  REWRITE_TAC[LENGTH; CONJUNCT1 LT] THENL
   [REWRITE_TAC[MISC3AUX_insert_atI_0_CONS; ADD_CLAUSES; ONE;
                MISC3AUX_insert_atI_SUC; LUPDATE_def];
    REWRITE_TAC[MISC3AUX_insert_atI_SUC; ADD_CLAUSES; LUPDATE_def; LT_SUC;
                CONS_11] THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

let LENGTH_insert_atI = prove
 (`p + LENGTH l1 <= LENGTH l2 ==> LENGTH (insert_atI (l1:A list) p l2) = LENGTH l2`,
  REWRITE_TAC[insert_atI_def; LENGTH_APPEND; LENGTH_DROP; LENGTH_TAKE_EQ] THEN
  ARITH_TAC);;

let insert_atI_app = prove
 (`!n (l:A list) c1 c2. (n + LENGTH c1) + LENGTH c2 <= LENGTH l ==>
     insert_atI (APPEND c1 c2) n l =
     insert_atI c1 n (insert_atI c2 (n + LENGTH c1) l)`,
  REPEAT GEN_TAC THEN SPEC_TAC(`n:num`,`n:num`) THEN
  SPEC_TAC(`l:A list`,`l:A list`) THEN SPEC_TAC(`c2:A list`,`c2:A list`) THEN
  SPEC_TAC(`c1:A list`,`c1:A list`) THEN
  LIST_INDUCT_TAC THEN REWRITE_TAC[APPEND; insert_atI_NIL; LENGTH; ADD_CLAUSES] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `insert_atI (CONS (h:A) (APPEND t c2)) n l =
                LUPDATE h n (insert_atI (APPEND t c2) (n + 1) l)` SUBST1_TAC THENL
   [MATCH_MP_TAC insert_atI_CONS THEN REWRITE_TAC[LENGTH_APPEND] THEN
    ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
    `insert_atI (CONS (h:A) t) n (insert_atI c2 (SUC (n + LENGTH t)) l) =
     LUPDATE h n (insert_atI t (n + 1) (insert_atI c2 (SUC (n + LENGTH t)) l))`
    SUBST1_TAC THENL
   [MATCH_MP_TAC insert_atI_CONS THEN
    SUBGOAL_THEN `LENGTH (insert_atI (c2:A list) (SUC (n + LENGTH (t:A list))) l) =
                  LENGTH l` SUBST1_TAC THENL
     [MATCH_MP_TAC LENGTH_insert_atI THEN ASM_ARITH_TAC; ASM_ARITH_TAC];
    ALL_TAC] THEN
  AP_TERM_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`c2:A list`; `l:A list`; `n + 1`]) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[ARITH_RULE `(n + 1) + t = SUC (n + t)`]);;

let insert_atI_end = prove
 (`insert_atI (l1:A list) (LENGTH l2) l2 = APPEND l2 l1`,
  SIMP_TAC[insert_atI_def; TAKE_LENGTH_ID; DROP_LENGTH_TOO_LONG; APPEND_NIL;
           ARITH_RULE `l <= l + m:num`]);;

let MISC3AUX_insert_atI_APPEND = prove
 (`!l1 l2 (c:A list) p. LENGTH l1 = p ==>
     insert_atI c p (APPEND l1 l2) = APPEND (APPEND l1 c) (DROP (LENGTH c) l2)`,
  REPEAT GEN_TAC THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[insert_atI_def; TAKE_LENGTH_APPEND] THEN
  ONCE_REWRITE_TAC[ADD_SYM] THEN
  REWRITE_TAC[GSYM DROP_DROP_T; DROP_LENGTH_APPEND]);;

let MISC3AUX_insert_atI_LONG = prove
 (`!(c:A list) p l. LENGTH l <= p ==> insert_atI c p l = APPEND l c`,
  SIMP_TAC[insert_atI_def; TAKE_LENGTH_TOO_LONG; DROP_LENGTH_TOO_LONG;
           APPEND_NIL; ARITH_RULE `l <= p ==> l <= p + c:num`]);;

let insert_atI_insert_atI = prove
 (`pos2 = pos1 + LENGTH c1 ==>
   insert_atI (c2:A list) pos2 (insert_atI c1 pos1 l) =
   insert_atI (APPEND c1 c2) pos1 l`,
  DISCH_THEN SUBST1_TAC THEN ASM_CASES_TAC `pos1 <= LENGTH (l:A list)` THENL
   [SUBGOAL_THEN `?xs ys. l = APPEND xs ys /\ LENGTH (xs:A list) = pos1`
      STRIP_ASSUME_TAC THENL
     [MAP_EVERY EXISTS_TAC [`TAKE pos1 (l:A list)`; `DROP pos1 (l:A list)`] THEN
      ASM_SIMP_TAC[TAKE_DROP; LENGTH_TAKE];
      ALL_TAC] THEN
    ASM_SIMP_TAC[MISC3AUX_insert_atI_APPEND] THEN
    SUBGOAL_THEN `LENGTH (APPEND xs (c1:A list)) = pos1 + LENGTH c1` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[LENGTH_APPEND]; ALL_TAC] THEN
    ASM_SIMP_TAC[GSYM APPEND_ASSOC; MISC3AUX_insert_atI_APPEND] THEN
    REWRITE_TAC[APPEND_ASSOC; DROP_DROP_T; LENGTH_APPEND] THEN
    REWRITE_TAC[ADD_SYM];
    SUBGOAL_THEN `LENGTH (l:A list) <= pos1` ASSUME_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[MISC3AUX_insert_atI_LONG] THEN
    SUBGOAL_THEN `LENGTH (APPEND (l:A list) c1) <= pos1 + LENGTH c1` ASSUME_TAC THENL
     [REWRITE_TAC[LENGTH_APPEND] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[MISC3AUX_insert_atI_LONG; APPEND_ASSOC]]);;

let LUPDATE_insert_commute = prove
 (`!ws pos1 pos2 (a:A list) w.
     pos2 < pos1 /\ pos1 + LENGTH ws <= LENGTH a ==>
     insert_atI ws pos1 (LUPDATE w pos2 a) =
     LUPDATE w pos2 (insert_atI ws pos1 a)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[insert_atI_NIL; LENGTH] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `pos1 + LENGTH (t:A list) < LENGTH (a:A list)` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[insert_atI_CONS; LENGTH_LUPDATE] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`pos1 + 1`; `pos2:num`; `a:A list`; `w:A`]) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  MATCH_MP_TAC LUPDATE_commutes THEN ASM_ARITH_TAC);;

let LESS_EQ_LENGTH = prove
 (`!(xs:A list) k. k <= LENGTH xs ==>
     ?ys1 ys2. (xs = APPEND ys1 ys2) /\ (LENGTH ys1 = k)`,
  REPEAT STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`TAKE k (xs:A list)`; `DROP k (xs:A list)`] THEN
  ASM_SIMP_TAC[TAKE_DROP; LENGTH_TAKE]);;

let LESS_LENGTH = prove
 (`!(xs:A list) k. k < LENGTH xs ==>
     ?ys1 y ys2. (xs = APPEND ys1 (CONS y ys2)) /\ (LENGTH ys1 = k)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[LENGTH; CONJUNCT1 LT] THEN
  INDUCT_TAC THEN REWRITE_TAC[LT_SUC; LT_0] THENL
   [MAP_EVERY EXISTS_TAC [`[]:A list`; `h:A`; `t:A list`] THEN
    REWRITE_TAC[APPEND; LENGTH];
    DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `k:num`) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC [`CONS (h:A) ys1`; `y:A`; `ys2:A list`] THEN
    ASM_REWRITE_TAC[APPEND; LENGTH]]);;

let IN_EVEN = prove
 (`x IN EVEN <=> EVEN x`,
  REWRITE_TAC[IN]);;

let FOLDL_OPTION_CHOICE_EQ_SOME_IMP_MEM = prove
 (`FOLDL OPTION_CHOICE (x:A option) ls = SOME y ==> MEM (SOME y) (CONS x ls)`,
  SPEC_TAC(`x:A option`,`x:A option`) THEN SPEC_TAC(`ls:(A option)list`,`ls:(A option)list`) THEN
  LIST_INDUCT_TAC THEN REWRITE_TAC[FOLDL; MEM] THENL
   [MESON_TAC[]; ALL_TAC] THEN
  GEN_TAC THEN DISCH_THEN(fun th -> FIRST_X_ASSUM(MP_TAC o C MATCH_MP th)) THEN
  REWRITE_TAC[MEM] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  POP_ASSUM MP_TAC THEN CASES_ON `x:A option` THEN
  REWRITE_TAC[OPTION_CHOICE_DEF] THEN MESON_TAC[]);;

let MISC3AUX_FORALL_LT_SUC = prove
 (`!P n. (!m. m < SUC n ==> P m) <=> P 0 /\ (!m. m < n ==> P (SUC m))`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [MESON_TAC[LT_0; LT_SUC];
    STRIP_TAC THEN INDUCT_TAC THEN ASM_SIMP_TAC[LT_SUC]]);;

let BAG_ALL_DISTINCT_FOLDR_BAG_UNION = prove
 (`!ls (b0:A->num).
     BAG_ALL_DISTINCT (ITLIST BAG_UNION ls b0) <=>
     BAG_ALL_DISTINCT b0 /\
     (!n. n < LENGTH ls ==>
          BAG_DISJOINT (EL n ls) b0 /\ BAG_ALL_DISTINCT (EL n ls) /\
          (!m. m < n ==> BAG_DISJOINT (EL n ls) (EL m ls)))`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[ITLIST; LENGTH; CONJUNCT1 LT] THEN
  REWRITE_TAC[BAG_ALL_DISTINCT_BAG_UNION; BAG_DISJOINT_FOLDR_BAG_UNION; ALL] THEN
  GEN_TAC THEN REWRITE_TAC[MISC3AUX_FORALL_LT_SUC] THEN
  REWRITE_TAC[EL; HD; TL; CONJUNCT1 LT] THEN REWRITE_TAC[GSYM ALL_EL] THEN
  ASM_REWRITE_TAC[] THEN MESON_TAC[BAG_DISJOINT_SYM]);;

(* TODO - candidate for move to HOL *)
(* N.B.: there is a different is_subsequence defined in lcsTheory; these
   should be merged *)
let is_subseq_def = cake_def_wf
 `measure (\p:(A list)#(A list). LENGTH (FST p))`
 (REPEAT STRIP_TAC THEN REWRITE_TAC[measure_THM; FST; SND; LENGTH] THEN
  ARITH_TAC)
 `(is_subseq (ls:A list) [] <=> T) /\
  (is_subseq [] (CONS (x:A) xs) <=> F) /\
  (is_subseq (CONS y ys) (CONS x xs) <=>
     (x = y /\ is_subseq ys xs) \/ (is_subseq ys (CONS x xs)))`;;

(* TODO - candidate for move to HOL *)
let is_subseq_ind = cake_ind "is_subseq";;

(* TODO - candidate for move to HOL *)
let is_subseq_refl = prove
 (`!ls:A list. is_subseq ls ls`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[is_subseq_def]);;
let _ = cake_add_simps [is_subseq_refl];;

(* TODO - candidate for move to HOL *)
let is_subseq_nil = prove
 (`is_subseq [] (ls:A list) <=> ls = []`,
  CASES_ON `ls:A list` THEN REWRITE_TAC[is_subseq_def; NOT_CONS_NIL]);;
let _ = cake_add_simps [is_subseq_nil];;

(* TODO - candidate for move to HOL *)
let is_subseq_cons = prove
 (`!l1 l2 (x:A). is_subseq l1 l2 ==> is_subseq (CONS x l1) l2`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN SIMP_TAC[is_subseq_def]);;

(* TODO - candidate for move to HOL *)
let is_subseq_snoc = prove
 (`!l1 l2 (x:A). is_subseq l1 l2 ==> is_subseq (SNOC x l1) l2`,
  MATCH_MP_TAC is_subseq_ind THEN REWRITE_TAC[is_subseq_def; SNOC] THEN
  MESON_TAC[]);;

(* TODO - candidate for move to HOL *)
let is_subseq_append1 = prove
 (`!l3 l1 (l2:A list). is_subseq l1 l2 ==> is_subseq (APPEND l3 l1) l2`,
  LIST_INDUCT_TAC THEN ASM_SIMP_TAC[APPEND; is_subseq_cons]);;

(* TODO - candidate for move to HOL *)
let is_subseq_append2 = prove
 (`!l4 l1 (l2:A list). is_subseq l1 l2 ==> is_subseq (APPEND l1 l4) l2`,
  MATCH_MP_TAC SNOC_INDUCT THEN REWRITE_TAC[APPEND_NIL] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[SNOC_APPEND; APPEND_ASSOC] THEN
  REWRITE_TAC[GSYM SNOC_APPEND] THEN MATCH_MP_TAC is_subseq_snoc THEN
  ASM_SIMP_TAC[]);;

(* TODO - candidate for move to HOL *)
let is_subseq_IS_SUBLIST = prove
 (`is_subseq l1 (l2:A list) /\ IS_SUBLIST l3 l1 ==> is_subseq l3 l2`,
  REWRITE_TAC[IS_SUBLIST_APPEND] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[is_subseq_append1; is_subseq_append2]);;

(* TODO - candidate for move to HOL *)
let is_subseq_MEM = prove
 (`!l1 l2 (x:A). is_subseq l1 l2 /\ MEM x l2 ==> MEM x l1`,
  MATCH_MP_TAC is_subseq_ind THEN REWRITE_TAC[is_subseq_def; MEM] THEN
  MESON_TAC[]);;

(* TODO - candidate for move to HOL *)
let IS_PREFIX_is_subseq = prove
 (`!l1 l2:A list. IS_PREFIX l1 l2 ==> is_subseq l1 l2`,
  MATCH_MP_TAC is_subseq_ind THEN
  REWRITE_TAC[is_subseq_def; IS_PREFIX_DEF; IS_PREFIX_NIL; NOT_CONS_NIL] THEN
  REWRITE_TAC[isPREFIX; list_CASE] THEN MESON_TAC[]);;

(* TODO - candidate for move to HOL *)
let IS_SUBLIST_is_subseq = prove
 (`!l1 l2:A list. IS_SUBLIST l1 l2 ==> is_subseq l1 l2`,
  MATCH_MP_TAC is_subseq_ind THEN REWRITE_TAC[is_subseq_def; IS_SUBLIST] THEN
  MESON_TAC[IS_PREFIX_is_subseq; IS_PREFIX_DEF]);;

(* TODO - candidate for move to HOL *)
let is_subseq_ALL_DISTINCT = prove
 (`!l1 l2:A list. ALL_DISTINCT l1 /\ is_subseq l1 l2 ==> ALL_DISTINCT l2`,
  MATCH_MP_TAC is_subseq_ind THEN REWRITE_TAC[is_subseq_def; ALL_DISTINCT] THEN
  MESON_TAC[is_subseq_MEM]);;

(* TODO - candidate for move to HOL *)
let is_subseq_append_suff = prove
 (`!l1 l3 l2 (l4:A list).
     is_subseq l1 l3 /\ is_subseq l2 l4 ==>
     is_subseq (APPEND l1 l2) (APPEND l3 l4)`,
  MATCH_MP_TAC is_subseq_ind THEN
  REWRITE_TAC[is_subseq_def; APPEND] THEN
  MESON_TAC[is_subseq_append1; APPEND]);;

(* TODO - candidate for move to HOL *)
let is_subseq_FLAT_suff = prove
 (`!ls1 ls2:(A list)list. ALL2 is_subseq ls1 ls2 ==>
     is_subseq (FLAT ls1) (FLAT ls2)`,
  MATCH_MP_TAC LIST_REL_ind THEN
  SIMP_TAC[FLAT; is_subseq_refl; is_subseq_append_suff]);;

let LIST_REL_IMP_LAST = prove
 (`!P (xs:A list) (ys:B list).
     ALL2 P xs ys /\ (~(xs = []) \/ ~(ys = [])) ==> P (LAST xs) (LAST ys)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[ALL2; NOT_CONS_NIL; LAST_DEF] THEN STRIP_TAC THEN
  REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[LIST_REL_LENGTH; LENGTH_EQ_NIL]);;

let make_even_def = cake_def
 `make_even n = if EVEN n then n else n + 1`;;

let EVEN_make_even = prove
 (`EVEN (make_even x)`,
  REWRITE_TAC[make_even_def] THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[EVEN_ADD; ARITH]);;
let _ = cake_add_simps [EVEN_make_even];;

let ALOOKUP_MAP_FST_INJ_SOME = prove
 (`!ls (x:A) (y:B).
     ALOOKUP ls x = SOME y /\
     (!x'. IS_SOME (ALOOKUP ls x') /\ (f:A->C) x' = f x ==> x = x') ==>
     ALOOKUP (MAP (f ## (g:B->D)) ls) (f x) = SOME (g y)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[ALOOKUP_DEF; option_DISTINCT] THEN
  SPEC_TAC(`h:A#B`,`h:A#B`) THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`a:A`; `b:B`] THEN
  REWRITE_TAC[MAP; PAIR_MAP_THM; ALOOKUP_THM] THEN
  REPEAT GEN_TAC THEN COND_CASES_TAC THENL
   [ASM_REWRITE_TAC[option_INJ] THEN MESON_TAC[]; ALL_TAC] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `~((f:A->C) a = f x)` ASSUME_TAC THENL
   [DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `a:A`) THEN
    ASM_REWRITE_TAC[IS_SOME_DEF] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `z:A` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `z:A`) THEN ASM_REWRITE_TAC[] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[IS_SOME_DEF] THEN ASM_MESON_TAC[]);;

let v2w_32_F = prove
 (`(v2w [F] : int32) = word 0`,
  REWRITE_TAC[WORD_EQ_BITS_ALT; bit_v2w; testbit; LENGTH; BIT_WORD_0] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[ARITH_RULE `i < 1 <=> i = 0`] THEN
  X_GEN_TAC `i:num` THEN ASM_CASES_TAC `i = 0` THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[EL; HD]);;
let _ = cake_add_simps [v2w_32_F];;

let v2w_32_T = prove
 (`(v2w [T] : int32) = word 1`,
  REWRITE_TAC[WORD_EQ_BITS_ALT; bit_v2w; testbit; LENGTH; BIT_WORD_1] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[ARITH_RULE `i < 1 <=> i = 0`] THEN
  X_GEN_TAC `i:num` THEN ASM_CASES_TAC `i = 0` THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[EL; HD]);;
let _ = cake_add_simps [v2w_32_T];;

let v2w_sing = prove
 (`v2w [b] = if b then word 1 else word 0:N word`,
  REWRITE_TAC[WORD_EQ_BITS_ALT; bit_v2w; testbit; LENGTH] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  BOOL_CASES_TAC `b:bool` THEN REWRITE_TAC[BIT_WORD_1; BIT_WORD_0] THEN
  ASM_CASES_TAC `i = 0` THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[EL; HD] THEN ASM_ARITH_TAC);;

let FOLDR_FUNPOW = prove
 (`ITLIST (\x:A. f) ls (x:B) = ITER (LENGTH ls) f x`,
  SPEC_TAC(`ls:A list`,`ls:A list`) THEN
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[ITLIST; LENGTH; ITER]);;

let FUNPOW_refl_trans_chain = prove
 (`transitive (P:A->A->bool) /\ reflexive P ==>
   !n x. (!j. j < n ==> P (ITER j f x) (f (ITER j f x))) ==>
         P x (ITER n f x)`,
  REWRITE_TAC[transitive_DEF; reflexive_DEF] THEN STRIP_TAC THEN
  INDUCT_TAC THEN ASM_REWRITE_TAC[ITER] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `ITER n (f:A->A) x` THEN
  ASM_SIMP_TAC[LT] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_SIMP_TAC[ARITH_RULE `j < n ==> j < SUC n`]);;

let MISC3AUX_LOG2_4 = CONV_RULE(LAND_CONV(RAND_CONV NUM_REDUCE_CONV))
  (SPEC `2` LOG2_TWOEXP);;
let MISC3AUX_LOG2_8 = CONV_RULE(LAND_CONV(RAND_CONV NUM_REDUCE_CONV))
  (SPEC `3` LOG2_TWOEXP);;

let byte_align_extract = prove
 (`byte_align (x:int32) =
   word_join (word_extract 31 2 x:(30)word) (word 0:(2)word)`,
  REWRITE_TAC[byte_align_def; WORD_EQ_BITS_ALT; BIT_ALIGN; BIT_WORD_JOIN;
              word_extract_def; o_THM; word_bits_def; BIT_WORD_ZX;
              BIT_WORD_OF_BITS; BIT_WORD_0; IN] THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[MISC3AUX_LOG2_4] THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL
   [ASM_ARITH_TAC;
    ASM_SIMP_TAC[ARITH_RULE `~(i < 2) ==> (i - 2) + 2 = i`] THEN
    ASM_SIMP_TAC[ARITH_RULE `~(i < 2) /\ i < 32 ==> i - 2 < 30 /\ i - 2 < 32 /\
                              i <= 31 /\ 2 <= i`]]);;

let byte_align_IN_IMP_IN_range = prove
 (`byte_align (a:N word) IN dm /\
   (dm = {w | word_ule low w /\ word_ult w hi}) /\
   byte_aligned low /\ byte_aligned hi ==>
   a IN dm`,
  STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[IN_ELIM_THM; byte_align_def; byte_aligned_def]) THEN
  REWRITE_TAC[IN_ELIM_THM] THEN CONJ_TAC THENL
   [MATCH_MP_TAC WORD_LOWER_EQ_TRANS THEN
    EXISTS_TAC `align (LOG2 (dimindex(:N) DIV 8)) (a:N word)` THEN
    ASM_REWRITE_TAC[align_ls];
    ASM_CASES_TAC `alignment_aligned (LOG2 (dimindex(:N) DIV 8)) (a:N word)` THENL
     [RULE_ASSUM_TAC(REWRITE_RULE[aligned_def]) THEN ASM_MESON_TAC[];
      MATCH_MP_TAC aligned_between THEN
      EXISTS_TAC `LOG2 (dimindex(:N) DIV 8)` THEN ASM_REWRITE_TAC[]]]);;

let MULT_DIV_MULT_LEMMA = prove
 (`!m l k. 0 < m /\ 0 < l ==> (m * k) DIV (l * m) = k DIV l`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `l * m = m * l` SUBST1_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC DIV_MULT2 THEN ASM_ARITH_TAC);;

let IMP_MULT_DIV_LESS = prove
 (`~(m = 0) /\ d < k ==> m * (d DIV m) < k`,
  STRIP_TAC THEN MP_TAC(SPECL [`d:num`; `m:num`] DIV_MUL_LE) THEN
  ASM_ARITH_TAC);;

let DIV_LESS_DIV = prove
 (`n MOD k = 0 /\ m MOD k = 0 /\ n < m /\ 0 < k ==> n DIV k < m DIV k`,
  STRIP_TAC THEN
  MP_TAC(SPECL [`n:num`; `k:num`] DIVISION) THEN
  MP_TAC(SPECL [`m:num`; `k:num`] DIVISION) THEN
  ASM_SIMP_TAC[ARITH_RULE `0 < k ==> ~(k = 0)`; ADD_CLAUSES] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `n DIV k * k < m DIV k * k` MP_TAC THENL
   [ASM_MESON_TAC[]; REWRITE_TAC[LT_MULT_RCANCEL] THEN SIMP_TAC[]]);;

(* HOL4 fromList of llistTheory is llist_fromList *)
let toPath_fromList = prove
 (`(toPath ((x:A), llist_fromList ([]:(B#A)list)) = stopped_at x) /\
   (toPath (x, llist_fromList (CONS ((y:B),(z:A)) t)) =
    pcons x y (toPath (z, llist_fromList t)))`,
  REWRITE_TAC[llist_fromList_def; stopped_at_def; pcons_def; first_def;
              path_rep_bijections_thm]);;

let steps_def = cake_def
 `(steps (f:A->B->A) x [] = []) /\
  (steps f x (CONS j js) =
     let y = f x j in
     let tr = steps f y js in
       CONS (j,y) tr)`;;

let steps_rel_def = cake_def_wf
 `measure (\p:(A->B->A->bool)#A#((B#A)list). LENGTH (SND (SND p)))`
 (REPEAT STRIP_TAC THEN REWRITE_TAC[measure_THM; FST; SND; LENGTH] THEN
  ARITH_TAC)
 `(steps_rel (R:A->B->A->bool) x [] <=> T) /\
  (steps_rel R x (CONS (j,y) tr) <=>
     R x j y /\
     steps_rel R y tr)`;;

let steps_rel_ind = cake_ind "steps_rel";;

let steps_rel_okpath = prove
 (`!R (x:A) (tr:(B#A)list).
     steps_rel R x tr <=> okpath R (toPath (x,llist_fromList tr))`,
  MATCH_MP_TAC steps_rel_ind THEN REWRITE_TAC[toPath_fromList] THEN
  REWRITE_TAC[steps_rel_def; okpath_thm; first_def; path_rep_bijections_thm] THEN
  SIMP_TAC[]);;

let steps_rel_LRC = prove
 (`!R (x:A) (tr:(B#A)list).
     steps_rel R x tr ==>
     LRC (\x y. ?i. R x i y)
       (BUTLAST (CONS x (MAP SND tr))) x (LAST (CONS x (MAP SND tr)))`,
  MATCH_MP_TAC steps_rel_ind THEN
  REWRITE_TAC[steps_rel_def; MAP; BUTLAST; LAST_DEF; LRC_def; NOT_CONS_NIL] THEN
  REPEAT STRIP_TAC THEN EXISTS_TAC `y:A` THEN
  CONJ_TAC THENL [ASM_MESON_TAC[]; ASM_SIMP_TAC[]]);;

let LAST_MAP_SND_steps_FOLDL = prove
 (`!f (x:A) (ls:B list). LAST (CONS x (MAP SND (steps f x ls))) = FOLDL f x ls`,
  GEN_TAC THEN ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[steps_def; MAP; LAST_DEF; FOLDL; LET_DEF; LET_END_DEF;
                  NOT_CONS_NIL]);;

let all_words_def = cake_def
 `(all_words (base:N word) 0 = {}) /\
  (all_words base (SUC n) = base INSERT (all_words (word_add base (word 1)) n))`;;

let IN_all_words = prove
 (`x IN all_words (base:N word) n <=> (?i. i < n /\ x = word_add base (word i))`,
  SPEC_TAC(`base:N word`,`base:N word`) THEN SPEC_TAC(`n:num`,`n:num`) THEN
  INDUCT_TAC THEN REWRITE_TAC[all_words_def; NOT_IN_EMPTY; CONJUNCT1 LT] THEN
  ASM_REWRITE_TAC[IN_INSERT] THEN GEN_TAC THEN EQ_TAC THENL
   [STRIP_TAC THENL
     [EXISTS_TAC `0` THEN ASM_REWRITE_TAC[LT_0; WORD_ADD_0];
      EXISTS_TAC `i + 1` THEN
      ASM_REWRITE_TAC[GSYM WORD_ADD_ASSOC; word_add_n2w] THEN
      CONJ_TAC THENL [ASM_ARITH_TAC; REWRITE_TAC[ADD_SYM]]];
    DISCH_THEN(X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) THEN
    ASM_CASES_TAC `i = 0` THENL
     [DISJ1_TAC THEN ASM_REWRITE_TAC[WORD_ADD_0];
      DISJ2_TAC THEN EXISTS_TAC `i - 1` THEN
      ASM_REWRITE_TAC[GSYM WORD_ADD_ASSOC; word_add_n2w] THEN
      CONJ_TAC THENL [ASM_ARITH_TAC;
                      AP_TERM_TAC THEN AP_TERM_TAC THEN ASM_ARITH_TAC]]]);;

(* val (a + k) without wrap-around *)
let MISC3AUX_VAL_WORD_ADD_LT = prove
 (`!(a:N word) k. val a + k < dimword(:N) ==>
     val (word_add a (word k)) = val a + k`,
  REWRITE_TAC[dimword_def] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[VAL_WORD_ADD; VAL_WORD] THEN
  SUBGOAL_THEN `k MOD 2 EXP dimindex(:N) = k` SUBST1_TAC THENL
   [MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC;
    MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC]);;

let read_bytearray_IMP_mem_SOME = prove
 (`!(p:N word) n (m:N word->B option) ba.
     (read_bytearray p n m = SOME ba) ==>
     !k. k IN all_words p n ==> IS_SOME (m k)`,
  REPEAT GEN_TAC THEN SPEC_TAC(`ba:B list`,`ba:B list`) THEN
  SPEC_TAC(`p:N word`,`p:N word`) THEN SPEC_TAC(`n:num`,`n:num`) THEN
  INDUCT_TAC THEN REWRITE_TAC[read_bytearray_def; all_words_def; NOT_IN_EMPTY] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[option_case_eq] THEN
  REWRITE_TAC[option_DISTINCT; option_INJ] THEN STRIP_TAC THEN
  REWRITE_TAC[IN_INSERT] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[IS_SOME_DEF] THEN ASM_MESON_TAC[]);;

let read_bytearray_no_wrap = prove
 (`!ptr len.
     IS_SOME (read_bytearray ptr len (m:N word -> B option)) /\
     (!x. IS_SOME (m x) ==> val x < dimword(:N) - 1) /\
     val ptr < dimword (:N)
     ==>
     val ptr + len < dimword(:N)`,
  ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN INDUCT_TAC THEN
  REWRITE_TAC[read_bytearray_def; ADD_CLAUSES] THEN GEN_TAC THEN
  REWRITE_TAC[IS_SOME_EXISTS; option_case_eq; option_DISTINCT; option_INJ] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `val (ptr:N word) < dimword(:N) - 1` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `val (word_add (ptr:N word) (word 1)) = val ptr + 1` ASSUME_TAC THENL
   [MATCH_MP_TAC MISC3AUX_VAL_WORD_ADD_LT THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `val (word_add (ptr:N word) (word 1)) + len < dimword(:N)` MP_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[IS_SOME_EXISTS]; ASM_MESON_TAC[IS_SOME_EXISTS]; ASM_ARITH_TAC];
    ASM_ARITH_TAC]);;

let asm_write_bytearray_def = cake_def
 `(asm_write_bytearray (a:N word) [] (m:N word->byte) = m) /\
  (asm_write_bytearray a (CONS x xs) m =
     (a =+ x) (asm_write_bytearray (word_add a (word 1)) xs m))`;;

let mem_eq_imp_asm_write_bytearray_eq = prove
 (`!(a:N word) bs.
     (m1:N word->byte) k = m2 k ==>
     (asm_write_bytearray a bs m1 k = asm_write_bytearray a bs m2 k)`,
  ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN LIST_INDUCT_TAC THEN
  ASM_SIMP_TAC[asm_write_bytearray_def; APPLY_UPDATE_THM]);;

let asm_write_bytearray_unchanged = prove
 (`!a bs m z. (word_ult x a \/ word_ule (word_add a (word (LENGTH bs))) x) /\
     (val a + LENGTH bs < dimword(:N)) /\ (z = m x)
     ==> (asm_write_bytearray (a:N word) bs m x = z)`,
  ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN LIST_INDUCT_TAC THENL
   [SIMP_TAC[asm_write_bytearray_def]; ALL_TAC] THEN
  REWRITE_TAC[asm_write_bytearray_def; APPLY_UPDATE_THM; LENGTH] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  (SUBGOAL_THEN `val (word_add (a:N word) (word 1)) = val a + 1` ASSUME_TAC THENL
    [MATCH_MP_TAC MISC3AUX_VAL_WORD_ADD_LT THEN ASM_ARITH_TAC; ALL_TAC]) THEN
  (SUBGOAL_THEN `val (word_add (a:N word) (word (SUC (LENGTH (t:byte list))))) =
                 val a + SUC (LENGTH t)` ASSUME_TAC THENL
    [MATCH_MP_TAC MISC3AUX_VAL_WORD_ADD_LT THEN ASM_ARITH_TAC; ALL_TAC]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_ULT; WORD_ULE]) THEN
  (SUBGOAL_THEN `~((a:N word) = x)` (fun th -> REWRITE_TAC[th]) THENL
    [DISCH_THEN SUBST_ALL_TAC THEN ASM_ARITH_TAC; ALL_TAC]) THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[WORD_ULT; WORD_ULE] THEN
  REWRITE_TAC[GSYM WORD_ADD_ASSOC; word_add_n2w] THEN
  ASM_REWRITE_TAC[ARITH_RULE `1 + n = SUC n`] THEN ASM_ARITH_TAC);;

let asm_write_bytearray_id = prove
 (`!a bs m.
     (!j. j < LENGTH bs ==> (m (word_add a (word j)) = EL j bs))
     ==> (asm_write_bytearray (a:N word) bs m x = m x)`,
  ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[asm_write_bytearray_def; APPLY_UPDATE_THM; LENGTH] THEN
  REPEAT STRIP_TAC THEN COND_CASES_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `0`) THEN
    ASM_REWRITE_TAC[LT_0; WORD_ADD_0; EL; HD] THEN MESON_TAC[];
    FIRST_X_ASSUM MATCH_MP_TAC THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `SUC j`) THEN
    ASM_REWRITE_TAC[LT_SUC; EL; TL; GSYM WORD_ADD_ASSOC; word_add_n2w] THEN
    REWRITE_TAC[ADD1; ADD_SYM]]);;

let asm_write_bytearray_unchanged_alt = prove
 (`!a bs m z.
     (z = m x) /\ ~(x IN { word_add a (word k) | k < LENGTH bs }) ==>
     (asm_write_bytearray (a:N word) bs m x = z)`,
  ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[asm_write_bytearray_def; APPLY_UPDATE_THM; LENGTH;
              IN_ELIM_THM; NOT_EXISTS_THM] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN COND_CASES_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `0`) THEN
    ASM_REWRITE_TAC[LT_0; WORD_ADD_0];
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC[IN_ELIM_THM; NOT_EXISTS_THM] THEN X_GEN_TAC `k:num` THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `k + 1`) THEN
    REWRITE_TAC[GSYM WORD_ADD_ASSOC; word_add_n2w] THEN
    REWRITE_TAC[ADD_SYM] THEN
    REWRITE_TAC[ARITH_RULE `k + 1 < SUC n <=> k < n`]]);;

let asm_write_bytearray_unchanged_all_words = prove
 (`!a bs m z x.
     ~(x IN all_words a (LENGTH bs)) /\ (z = m x) ==>
     (asm_write_bytearray (a:N word) bs m x = z)`,
  ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[asm_write_bytearray_def; APPLY_UPDATE_THM; LENGTH;
              all_words_def; IN_INSERT; DE_MORGAN_THM] THEN
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[]);;

let asm_write_bytearray_append = prove
 (`!a l1 l2 m.
     (val a + LENGTH l1) + LENGTH l2 < dimword (:N) ==>
     (asm_write_bytearray (a:N word) (APPEND l1 l2) m =
      asm_write_bytearray (word_add a (word (LENGTH l1))) l2
        (asm_write_bytearray a l1 m))`,
  ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN LIST_INDUCT_TAC THENL
   [REWRITE_TAC[APPEND; LENGTH; WORD_ADD_0; asm_write_bytearray_def];
    ALL_TAC] THEN
  REWRITE_TAC[APPEND; LENGTH; asm_write_bytearray_def] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `val (word_add (a:N word) (word 1)) = val a + 1` ASSUME_TAC THENL
   [MATCH_MP_TAC MISC3AUX_VAL_WORD_ADD_LT THEN ASM_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`word_add (a:N word) (word 1)`; `l2:byte list`;
                                `m:N word->byte`]) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[GSYM WORD_ADD_ASSOC; word_add_n2w; ARITH_RULE `1 + n = SUC n`] THEN
  ABBREV_TAC `b = word_add (a:N word) (word (SUC (LENGTH (t:byte list))))` THEN
  SUBGOAL_THEN `val (b:N word) = val (a:N word) + SUC (LENGTH (t:byte list))`
    ASSUME_TAC THENL
   [EXPAND_TAC "b" THEN MATCH_MP_TAC MISC3AUX_VAL_WORD_ADD_LT THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[FUN_EQ_THM; APPLY_UPDATE_THM] THEN X_GEN_TAC `y:N word` THEN
  COND_CASES_TAC THENL
   [FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC asm_write_bytearray_unchanged THEN
    REWRITE_TAC[APPLY_UPDATE_THM; WORD_ULT] THEN ASM_ARITH_TAC;
    MATCH_MP_TAC mem_eq_imp_asm_write_bytearray_eq THEN
    ASM_REWRITE_TAC[APPLY_UPDATE_THM]]);;

let asm_write_bytearray_EL = prove
 (`!a bs m x. x < LENGTH bs /\ LENGTH bs < dimword(:N) ==>
     (asm_write_bytearray (a:N word) bs m (word_add a (word x)) = EL x bs)`,
  ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[asm_write_bytearray_def; APPLY_UPDATE_THM; LENGTH; CONJUNCT1 LT] THEN
  REPEAT GEN_TAC THEN STRUCT_CASES_TAC(SPEC `x:num` num_CASES) THEN
  REWRITE_TAC[WORD_ADD_0; EL; HD; TL] THEN STRIP_TAC THEN
  SUBGOAL_THEN `~((a:N word) = word_add a (word (SUC n)))` (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[WORD_EQ_ADD_CANCEL] THEN
    SUBGOAL_THEN `SUC n < 2 EXP dimindex(:N)`
      (fun th -> SIMP_TAC[th; WORD_EQ_0; NOT_SUC]) THEN
    REWRITE_TAC[GSYM dimword_def] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `word_add (a:N word) (word (SUC n)) =
                word_add (word_add a (word 1)) (word n)` SUBST1_TAC THENL
   [REWRITE_TAC[GSYM WORD_ADD_ASSOC; word_add_n2w; ARITH_RULE `1 + n = SUC n`];
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC]);;

(* TODO: move to sptTheory *)

(* HOL4 completes the last clause eq_shape _ _ = F into the 12 clauses
   below it *)
let eq_shape_def = cake_def_wf
 `measure (\p:(A spt)#(B spt). spt_size (\x:A. 0) (FST p))`
 TERM_TAC
 `(eq_shape (LN:A spt) (LN:B spt) <=> T) /\
  (eq_shape (LS (a:A)) (LS (b:B)) <=> T) /\
  (eq_shape (BN t1 t2) (BN u1 u2) <=> eq_shape t1 u1 /\ eq_shape t2 u2) /\
  (eq_shape (BS t1 a t2) (BS u1 b u2) <=> eq_shape t1 u1 /\ eq_shape t2 u2) /\
  (eq_shape LN (LS b) <=> F) /\
  (eq_shape LN (BN u1 u2) <=> F) /\
  (eq_shape LN (BS u1 b u2) <=> F) /\
  (eq_shape (LS a) LN <=> F) /\
  (eq_shape (LS a) (BN u1 u2) <=> F) /\
  (eq_shape (LS a) (BS u1 b u2) <=> F) /\
  (eq_shape (BN t1 t2) LN <=> F) /\
  (eq_shape (BN t1 t2) (LS b) <=> F) /\
  (eq_shape (BN t1 t2) (BS u1 b u2) <=> F) /\
  (eq_shape (BS t1 a t2) LN <=> F) /\
  (eq_shape (BS t1 a t2) (LS b) <=> F) /\
  (eq_shape (BS t1 a t2) (BN u1 u2) <=> F)`;;

let eq_shape_ind = cake_ind "eq_shape";;

(* helpers: a key is 0, an odd number or a positive even number *)
let MISC3AUX_bit_cases = prove
 (`!n. n = 0 \/ (?m. n = 2 * m + 1) \/ (?m. n = 2 * m + 2)`,
  GEN_TAC THEN DISJ_CASES_TAC(SPEC `n:num` EVEN_OR_ODD) THENL
   [FIRST_X_ASSUM(X_CHOOSE_TAC `m:num` o REWRITE_RULE[EVEN_EXISTS]) THEN
    ASM_CASES_TAC `m = 0` THENL
     [ASM_REWRITE_TAC[] THEN ARITH_TAC;
      DISJ2_TAC THEN DISJ2_TAC THEN EXISTS_TAC `m - 1` THEN ASM_ARITH_TAC];
    FIRST_X_ASSUM(X_CHOOSE_TAC `m:num` o REWRITE_RULE[ODD_EXISTS]) THEN
    DISJ2_TAC THEN DISJ1_TAC THEN EXISTS_TAC `m:num` THEN ASM_ARITH_TAC]);;

let MISC3AUX_FORALL_BITS = prove
 (`!P. (!n. P n) <=> P 0 /\ (!m. P (2 * m + 1)) /\ (!m. P (2 * m + 2))`,
  GEN_TAC THEN EQ_TAC THEN SIMP_TAC[] THEN STRIP_TAC THEN GEN_TAC THEN
  REPEAT_TCL STRIP_THM_THEN SUBST1_TAC (SPEC `n:num` MISC3AUX_bit_cases) THEN
  ASM_REWRITE_TAC[]);;

let MISC3AUX_BIT_RW = prove
 (`(!m. ~(2 * m + 1 = 0)) /\ (!m. ~(2 * m + 2 = 0)) /\
   (!m. EVEN (2 * m + 1) <=> F) /\ (!m. EVEN (2 * m + 2) <=> T) /\
   (!m. ((2 * m + 1) - 1) DIV 2 = m) /\ (!m. ((2 * m + 2) - 1) DIV 2 = m)`,
  REWRITE_TAC[EVEN_ADD; EVEN_MULT; ARITH] THEN REPEAT CONJ_TAC THEN
  GEN_TAC THEN TRY ARITH_TAC THEN
  MATCH_MP_TAC DIV_UNIQ THEN EXISTS_TAC `1` THEN ARITH_TAC);;

let MISC3AUX_lookup_bits = prove
 (`(!m t1 (t2:A spt). lookup (2 * m + 1) (BN t1 t2) = lookup m t2) /\
   (!m t1 (a:A) t2. lookup (2 * m + 1) (BS t1 a t2) = lookup m t2) /\
   (!m t1 (t2:A spt). lookup (2 * m + 2) (BN t1 t2) = lookup m t1) /\
   (!m t1 (a:A) t2. lookup (2 * m + 2) (BS t1 a t2) = lookup m t1) /\
   (!m (a:A). lookup (2 * m + 1) (LS a) = NONE) /\
   (!m (a:A). lookup (2 * m + 2) (LS a) = NONE)`,
  REWRITE_TAC[lookup_def; MISC3AUX_BIT_RW]);;

let spt_eq = prove
 (`!t1 t2:A spt.
     t1 = t2 <=>
     (eq_shape t1 t2 /\ (!k v. lookup k t1 = SOME v ==> lookup k t2 = SOME v))`,
  MATCH_MP_TAC spt_INDUCT THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  TRY DISCH_TAC THEN REPEAT GEN_TAC THEN CASES_ON `t2:A spt` THEN
  REWRITE_TAC[eq_shape_def; spt_distinct; spt_inject] THEN
  ONCE_REWRITE_TAC[MISC3AUX_FORALL_BITS] THEN
  REWRITE_TAC[lookup_def; MISC3AUX_lookup_bits; option_DISTINCT; option_INJ] THEN
  REWRITE_TAC[MISC3AUX_BIT_RW] THEN
  TRY(FIRST_X_ASSUM(fun th -> ONCE_REWRITE_TAC[CONJUNCT1 th; CONJUNCT2 th])) THEN
  MESON_TAC[]);;

let eq_shape_map = prove
 (`!(t1:A spt) (t2:C spt) (f:A->B). eq_shape (map f t1) t2 <=> eq_shape t1 t2`,
  MATCH_MP_TAC spt_INDUCT THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  TRY DISCH_TAC THEN REPEAT GEN_TAC THEN CASES_ON `t2:C spt` THEN
  ASM_REWRITE_TAC[eq_shape_def; map_def]);;

let eq_shape_IMP_domain = prove
 (`!(t1:A spt) (t2:B spt). eq_shape t1 t2 ==> domain t1 = domain t2`,
  MATCH_MP_TAC eq_shape_ind THEN REWRITE_TAC[eq_shape_def; domain_def] THEN
  REPEAT STRIP_TAC THEN RES_TAC THEN ASM_REWRITE_TAC[]);;

let copy_shape_def = cake_def_wf
 `measure (\p:(A spt)#(B spt).
     spt_size (\x:A. 0) (FST p) + spt_size (\x:B. 0) (SND p))`
 TERM_TAC
 `(copy_shape (LN:A spt) (LN:B spt) = LN) /\
  (copy_shape LN (LS y) = LN) /\
  (copy_shape LN (BN t1 t2) = BN (copy_shape LN t1) (copy_shape LN t2)) /\
  (copy_shape LN (BS t1 y t2) = LN) /\
  (copy_shape (LS x) LN = LS x) /\
  (copy_shape (LS x) (LS y) = LS x) /\
  (copy_shape (LS x) (BN t1 t2) = LS x) /\
  (copy_shape (LS x) (BS t1 y t2) = BS (copy_shape LN t1) x (copy_shape LN t2)) /\
  (copy_shape (BN u1 u2) LN = (if domain (BN u1 u2) = {} then LN else BN u1 u2)) /\
  (copy_shape (BN u1 u2) (LS y) = BN u1 u2) /\
  (copy_shape (BN u1 u2) (BN t1 t2) = BN (copy_shape u1 t1) (copy_shape u2 t2)) /\
  (copy_shape (BN u1 u2) (BS t1 y t2) = BN u1 u2) /\
  (copy_shape (BS u1 x u2) LN = BS u1 x u2) /\
  (copy_shape (BS u1 x u2) (LS y) =
     (if domain (BN u1 u2) = {} then LS x else BS u1 x u2)) /\
  (copy_shape (BS u1 x u2) (BN t1 t2) = BS u1 x u2) /\
  (copy_shape (BS u1 x u2) (BS t1 y t2) =
     BS (copy_shape u1 t1) x (copy_shape u2 t2))`;;

let MISC3AUX_domain_empty_lookup = prove
 (`!t:A spt. domain t = {} <=> !k. lookup k t = NONE`,
  REWRITE_TAC[EXTENSION; domain_lookup; NOT_IN_EMPTY] THEN
  MESON_TAC[option_nchotomy; option_DISTINCT]);;

let eq_shape_copy_shape = prove
 (`!s:B spt. domain s = {} ==> eq_shape (copy_shape (LN:A spt) s) s`,
  MATCH_MP_TAC spt_INDUCT THEN
  REWRITE_TAC[copy_shape_def; eq_shape_def; MISC3AUX_domain_empty_lookup] THEN
  REPEAT STRIP_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `0`) THEN REWRITE_TAC[lookup_def; option_DISTINCT];
    FIRST_X_ASSUM MATCH_MP_TAC THEN X_GEN_TAC `m:num` THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `2 * m + 2`) THEN REWRITE_TAC[MISC3AUX_lookup_bits];
    FIRST_X_ASSUM MATCH_MP_TAC THEN X_GEN_TAC `m:num` THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `2 * m + 1`) THEN REWRITE_TAC[MISC3AUX_lookup_bits];
    FIRST_X_ASSUM(MP_TAC o SPEC `0`) THEN REWRITE_TAC[lookup_def; option_DISTINCT]]);;

let num_lemma = prove
 (`(!n. ~(0 = 2 * n + 2) /\ ~(0 = 2 * n + 1:num)) /\
   (!n m. 2 * n + 2 = 2 * m + 2 <=> (m = n)) /\
   (!n m. 2 * n + 1 = 2 * m + 1 <=> (m = n)) /\
   (!n m. ~(2 * n + 2 = 2 * m + 1))`,
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN TRY ARITH_TAC THEN
  DISCH_THEN(MP_TAC o AP_TERM `EVEN`) THEN REWRITE_TAC[EVEN_ADD; EVEN_MULT; ARITH]);;

let MISC3AUX_domain_eq_lookup = prove
 (`!(t1:A spt) (t2:B spt). domain t1 = domain t2 <=>
     !k. lookup k t1 = NONE <=> lookup k t2 = NONE`,
  REWRITE_TAC[EXTENSION; domain_lookup] THEN
  MESON_TAC[option_nchotomy; option_DISTINCT]);;

let shape_eq_copy_shape = prove
 (`!(t1:A spt) (t2:B spt).
     domain t1 = domain t2 ==> eq_shape (copy_shape t1 t2) t2`,
  MATCH_MP_TAC spt_INDUCT THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  TRY(DISCH_THEN(fun th -> if is_conj(concl th) then ASSUME_TAC th THEN GEN_TAC
                           else MP_TAC th)) THEN
  CASES_ON `t2:B spt` THEN
  REWRITE_TAC[copy_shape_def; eq_shape_def] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MISC3AUX_domain_eq_lookup]) THEN
  MP_TAC eq_shape_copy_shape THEN
  REWRITE_TAC[MISC3AUX_domain_eq_lookup; MISC3AUX_domain_empty_lookup] THEN
  DISCH_TAC THEN
  ONCE_REWRITE_TAC[MISC3AUX_FORALL_BITS] THEN
  REWRITE_TAC[lookup_def; MISC3AUX_lookup_bits; option_DISTINCT] THEN
  REPEAT COND_CASES_TAC THEN REWRITE_TAC[eq_shape_def] THEN
  ASM_MESON_TAC[]);;

let lookup_copy_shape_LN = prove
 (`!(s:B spt) n. lookup n (copy_shape (LN:A spt) s) = NONE`,
  MATCH_MP_TAC spt_INDUCT THEN REWRITE_TAC[copy_shape_def; lookup_def] THEN
  REPEAT STRIP_TAC THEN REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[]);;

let domain_EMPTY_lookup = prove
 (`domain (t:A spt) = EMPTY ==> !x. lookup x t = NONE`,
  REWRITE_TAC[MISC3AUX_domain_empty_lookup]);;

let lookup_copy_shape = prove
 (`!(t1:A spt) (t2:B spt) n. lookup n (copy_shape t1 t2) = lookup n t1`,
  MATCH_MP_TAC spt_INDUCT THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  TRY DISCH_TAC THEN REPEAT GEN_TAC THEN CASES_ON `t2:B spt` THEN
  REWRITE_TAC[copy_shape_def; lookup_copy_shape_LN] THEN
  REPEAT COND_CASES_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MISC3AUX_domain_empty_lookup]) THEN
  ASM_REWRITE_TAC[] THEN
  TRY(FIRST_X_ASSUM(MP_TAC o SPEC `n:num` o check (is_forall o concl))) THEN
  REWRITE_TAC[lookup_def] THEN REPEAT COND_CASES_TAC THEN
  ASM_REWRITE_TAC[lookup_copy_shape_LN] THEN ASM_MESON_TAC[]);;

(* / TODO *)

(* BEGIN TODO: move to sptreeTheory *)

let lookup_zero = prove
 (`!n (t:A spt) x. (lookup n t = SOME x) ==> ~(size t = 0)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[size_domain] THEN
  SIMP_TAC[CARD_EQ_0; FINITE_domain; GSYM MEMBER_NOT_EMPTY; domain_lookup] THEN
  MESON_TAC[]);;

(* HOL4 isEmpty t is t = LN *)
let empty_sub = prove
 (`difference (a:A spt) b = LN /\ subspt b a ==> domain a = domain b`,
  STRIP_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN
  ASM_MESON_TAC[difference_sub; subspt_domain_SUBSET]);;

let subspt_delete = prove
 (`!(a:A spt) b x. subspt a b ==> subspt (delete x a) b`,
  REWRITE_TAC[subspt_def; domain_delete; IN_DELETE; lookup_delete] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

let inter_union_empty = prove
 (`!(a:A spt) b (c:B spt).
     inter (union a b) c = LN <=> inter a c = LN /\ inter b c = LN`,
  SIMP_TAC[wf_inter; domain_empty; domain_inter; domain_union] THEN SET_TAC[]);;

let inter_insert_empty = prove
 (`!n (t1:1 spt) (t2:B spt). inter (insert n one t1) t2 = LN ==>
     ~(n IN domain t2) /\ inter t1 t2 = LN`,
  SIMP_TAC[wf_inter; domain_empty; domain_inter; domain_insert] THEN SET_TAC[]);;

let fromList2_value = prove
 (`!(e:A) l (t:B) (n:num). MEM e l <=> ?n. lookup n (fromList2 l) = SOME e`,
  REWRITE_TAC[lookup_fromList2; lookup_fromList; list_MEM_EL] THEN
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `k:num` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `2 * k` THEN
    ASM_SIMP_TAC[EVEN_DOUBLE; DIV_MULT; ARITH_EQ];
    DISCH_THEN(X_CHOOSE_THEN `k:num` MP_TAC) THEN
    REPEAT COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT; option_INJ] THEN
    DISCH_TAC THEN EXISTS_TAC `k DIV 2` THEN ASM_REWRITE_TAC[]]);;

(* The range is the set of values taken on by an sptree.
   Not sure if these are worth moving. *)
let range_def = cake_def
 `range (s:A spt) = {v | ?n. lookup n s = SOME v}`;;

let range_delete = prove
 (`range (delete h (v:A spt)) SUBSET range v`,
  REWRITE_TAC[range_def; lookup_delete; SUBSET; IN_ELIM_THM] THEN
  REPEAT STRIP_TAC THEN EXISTS_TAC `n:num` THEN POP_ASSUM MP_TAC THEN
  COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT]);;

let range_insert = prove
 (`~(n IN domain (fml:A spt)) ==>
   range (insert n l fml) = l INSERT range fml`,
  REWRITE_TAC[range_def; EXTENSION; lookup_insert; domain_lookup; IN_ELIM_THM;
              IN_INSERT] THEN
  STRIP_TAC THEN X_GEN_TAC `x:A` THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `m:num` MP_TAC) THEN COND_CASES_TAC THEN
    REWRITE_TAC[option_INJ] THEN MESON_TAC[];
    STRIP_TAC THENL
     [EXISTS_TAC `n:num` THEN ASM_REWRITE_TAC[];
      EXISTS_TAC `n':num` THEN COND_CASES_TAC THEN ASM_MESON_TAC[]]]);;

(* HOL4 names the element C, a constant of HOL Light *)
let range_insert_2 = prove
 (`(c:A) IN range (insert n l fml) ==> c IN range fml \/ c = l`,
  REWRITE_TAC[range_def; lookup_insert; IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `m:num` MP_TAC) THEN COND_CASES_TAC THEN
  REWRITE_TAC[option_INJ] THEN MESON_TAC[]);;

let range_insert_SUBSET = prove
 (`range (insert n l (fml:A spt)) SUBSET l INSERT range fml`,
  REWRITE_TAC[SUBSET; IN_INSERT] THEN MESON_TAC[range_insert_2]);;

(* END TODO *)

(* HOL4: TWOxDIV2 *)
let misc_TWOxDIV2 = prove
 (`(2 * x) DIV 2 = x`,
  SIMP_TAC[DIV_MULT; ARITH_EQ]);;

(* alist_insert_REVERSE: the same statement is sptree.ml's alist_insert_REVERSE
   (HOL4 sptreeTheory has it too); not rebound here *)

let alist_insert_ALL_DISTINCT = prove
 (`!xs ys (t:A spt) ls.
     ALL_DISTINCT xs /\
     LENGTH xs = LENGTH ys /\
     PERM (ZIP xs ys) ls ==>
     alist_insert xs ys t = alist_insert (MAP FST ls) (MAP SND ls) t`,
  MATCH_MP_TAC alist_insert_ind THEN REPEAT CONJ_TAC THENL
   [REPEAT GEN_TAC THEN REWRITE_TAC[LENGTH] THEN STRIP_TAC THEN
    SUBGOAL_THEN `xs:A list = []` SUBST_ALL_TAC THENL
     [ASM_MESON_TAC[LENGTH_EQ_NIL]; ALL_TAC] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[ZIP; PERM_NIL]) THEN
    ASM_REWRITE_TAC[MAP; alist_insert_def];
    REWRITE_TAC[LENGTH; NOT_SUC];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`v:num`; `vs:num list`; `x:A`; `xs:A list`; `t:A spt`] THEN
  DISCH_TAC THEN X_GEN_TAC `ls:(num#A)list` THEN
  REWRITE_TAC[ALL_DISTINCT; LENGTH; SUC_INJ; ZIP; PERM_CONS_EQ_APPEND] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[alist_insert_def; MAP_APPEND; MAP] THEN
  SUBGOAL_THEN `~MEM (v:num) (MAP FST (M:(num#A)list))` ASSUME_TAC THENL
   [REWRITE_TAC[MEM_MAP; EXISTS_PAIR_THM; FST] THEN
    DISCH_THEN(X_CHOOSE_THEN `p1:num` (X_CHOOSE_THEN `y:A` STRIP_ASSUME_TAC)) THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> is_var(rhs(concl th)))) THEN
    UNDISCH_TAC `~MEM (v:num) vs` THEN REWRITE_TAC[] THEN
    FIRST_ASSUM(MP_TAC o SPEC `(v:num,y:A)` o MATCH_MP PERM_MEM_EQ) THEN
    ASM_SIMP_TAC[MEM_APPEND; MEM_ZIP] THEN
    DISCH_THEN(X_CHOOSE_THEN `n:num` STRIP_ASSUME_TAC) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[PAIR_EQ]) THEN ASM_MESON_TAC[EL_MEM];
    ALL_TAC] THEN
  SUBGOAL_THEN `LENGTH (MAP FST (M:(num#A)list)) = LENGTH (MAP SND M)`
    ASSUME_TAC THENL [REWRITE_TAC[LENGTH_MAP]; ALL_TAC] THEN
  ASM_SIMP_TAC[alist_insert_append; alist_insert_def; alist_insert_pull_insert] THEN
  AP_TERM_TAC THEN ASM_SIMP_TAC[GSYM alist_insert_append] THEN
  REWRITE_TAC[GSYM MAP_APPEND] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[]);;

(* signed comparisons of words with small values *)
let MISC3AUX_IVAL_SMALL = prove
 (`!w:N word. val w < 2 EXP (dimindex(:N) - 1) ==> ival w = &(val w)`,
  SIMP_TAC[ival]);;

let MISC3AUX_ILT_0 = prove
 (`!w:N word. word_ilt (word 0) w <=>
              0 < val w /\ val w < 2 EXP (dimindex(:N) - 1)`,
  GEN_TAC THEN REWRITE_TAC[word_ilt; irelational2; IVAL_WORD_0; ival] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[INT_OF_NUM_LT] THEN
  MP_TAC(ISPEC `w:N word` VAL_BOUND) THEN
  REWRITE_TAC[GSYM INT_OF_NUM_LT; GSYM INT_OF_NUM_POW] THEN INT_ARITH_TAC);;

let MISC3AUX_ILT_ILE_SMALL = prove
 (`!v w:N word.
     val v < 2 EXP (dimindex(:N) - 1) /\ val w < 2 EXP (dimindex(:N) - 1) ==>
     (word_ilt v w <=> val v < val w) /\ (word_ile v w <=> val v <= val w)`,
  SIMP_TAC[word_ilt; word_ile; irelational2; MISC3AUX_IVAL_SMALL;
           INT_OF_NUM_LT; INT_OF_NUM_LE]);;

let n2w_lt = prove
 (`word_ilt (word 0:N word) (word a) /\ word_ilt (word 0:N word) (word b) /\
   a < dimword (:N) /\ b < dimword (:N)
   ==>
   (word_ilt (word a:N word) (word b) <=> a < b)`,
  REWRITE_TAC[MISC3AUX_ILT_0; dimword_def] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[MISC3AUX_ILT_ILE_SMALL] THEN ASM_SIMP_TAC[VAL_WORD_EQ]);;

let n2w_le = prove
 (`word_ilt (word 0:N word) (word a) /\ word_ilt (word 0:N word) (word b) /\
   a < dimword (:N) /\ b < dimword (:N)
   ==>
   (word_ile (word a:N word) (word b) <=> a <= b)`,
  REWRITE_TAC[MISC3AUX_ILT_0; dimword_def] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[MISC3AUX_ILT_ILE_SMALL] THEN ASM_SIMP_TAC[VAL_WORD_EQ]);;

let word_lt_0w = prove
 (`2 * n < dimword (:N) ==> (word_ilt (word 0:N word) (word n) <=> 0 < n)`,
  REWRITE_TAC[MISC3AUX_ILT_0; dimword_def] THEN DISCH_TAC THEN
  SUBGOAL_THEN `2 EXP dimindex(:N) = 2 * 2 EXP (dimindex(:N) - 1)` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM(CONJUNCT2 EXP)] THEN AP_TERM_TAC THEN
    MP_TAC(ISPEC `(:N)` DIMINDEX_GE_1) THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `val (word n:N word) = n` SUBST1_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN ASM_ARITH_TAC; ASM_ARITH_TAC]);;

let word_sub_lt = prove
 (`word_ilt (word 0) (n:N word) /\ word_ilt (word 0) m /\ word_ile n m ==>
   word_ilt (word_sub m n) m`,
  REWRITE_TAC[MISC3AUX_ILT_0] THEN STRIP_TAC THEN
  SUBGOAL_THEN `val (n:N word) <= val (m:N word)` ASSUME_TAC THENL
   [ASM_MESON_TAC[MISC3AUX_ILT_ILE_SMALL]; ALL_TAC] THEN
  SUBGOAL_THEN `val (word_sub m n:N word) = val m - val n` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[VAL_WORD_SUB_CASES]; ALL_TAC] THEN
  SUBGOAL_THEN `val (word_sub m n:N word) < 2 EXP (dimindex(:N) - 1)` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[MISC3AUX_ILT_ILE_SMALL] THEN ASM_ARITH_TAC);;

(* see #521 *)

let bytes_in_memory_def = cake_def
 `(bytes_in_memory (a:N word) [] (m:N word->byte) dm <=> T) /\
  (bytes_in_memory a (CONS (x:byte) xs) m dm <=>
     (m a = x) /\ a IN dm /\ bytes_in_memory (word_add a (word 1)) xs m dm)`;;

let bytes_in_memory_APPEND = prove
 (`!l1 l2 (pc:N word) mem mem_domain.
     bytes_in_memory pc (APPEND l1 l2) mem mem_domain <=>
     bytes_in_memory pc l1 mem mem_domain /\
     bytes_in_memory (word_add pc (word (LENGTH l1))) l2 mem mem_domain`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[APPEND; LENGTH; bytes_in_memory_def; WORD_ADD_0] THEN
  REWRITE_TAC[GSYM WORD_ADD_ASSOC; word_add_n2w; ARITH_RULE `1 + n = SUC n`] THEN
  REWRITE_TAC[CONJ_ACI]);;

let bytes_in_memory_change_domain = prove
 (`!(a:N word) bs m md1 md2.
     bytes_in_memory a bs m md1 /\
     (!n. n < LENGTH bs /\ word_add a (word n) IN md1 ==>
          word_add a (word n) IN md2)
     ==> bytes_in_memory a bs m md2`,
  ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[bytes_in_memory_def; LENGTH] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[] THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `0`) THEN ASM_REWRITE_TAC[LT_0; WORD_ADD_0];
    FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `md1:N word->bool` THEN
    ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[GSYM WORD_ADD_ASSOC; word_add_n2w;
                                ARITH_RULE `1 + n = SUC n`]) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `SUC n`) THEN
    REWRITE_TAC[GSYM WORD_ADD_ASSOC; word_add_n2w; ARITH_RULE `1 + n = SUC n`] THEN
    ASM_REWRITE_TAC[LT_SUC]]);;

let bytes_in_memory_change_mem = prove
 (`!(a:N word) bs m1 m2 md.
     bytes_in_memory a bs m1 md /\
     (!n. n < LENGTH bs ==> (m1 (word_add a (word n)) = m2 (word_add a (word n))))
     ==> bytes_in_memory a bs m2 md`,
  ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[bytes_in_memory_def; LENGTH] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[] THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `0`) THEN ASM_REWRITE_TAC[LT_0; WORD_ADD_0] THEN
    ASM_MESON_TAC[];
    FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `m1:N word->byte` THEN
    ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[GSYM WORD_ADD_ASSOC; word_add_n2w;
                                ARITH_RULE `1 + n = SUC n`]) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `SUC n`) THEN
    REWRITE_TAC[GSYM WORD_ADD_ASSOC; word_add_n2w; ARITH_RULE `1 + n = SUC n`] THEN
    ASM_REWRITE_TAC[LT_SUC]]);;

let bytes_in_memory_EL = prove
 (`!(a:N word) bs m md k. bytes_in_memory a bs m md /\ k < LENGTH bs ==>
     (m (word_add a (word k)) = EL k bs)`,
  ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[bytes_in_memory_def; LENGTH; CONJUNCT1 LT] THEN
  REPEAT GEN_TAC THEN STRUCT_CASES_TAC(SPEC `k:num` num_CASES) THEN
  REWRITE_TAC[EL; HD; TL; WORD_ADD_0; LT_SUC] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[ARITH_RULE `SUC n = 1 + n`; GSYM word_add_n2w; WORD_ADD_ASSOC] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `md:N word->bool` THEN
  ASM_REWRITE_TAC[]);;

let bytes_in_memory_in_domain = prove
 (`!(a:N word) bs m md k. bytes_in_memory a bs m md /\ k < LENGTH bs ==>
     ((word_add a (word k)) IN md)`,
  ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[bytes_in_memory_def; LENGTH; CONJUNCT1 LT] THEN
  REPEAT GEN_TAC THEN STRUCT_CASES_TAC(SPEC `k:num` num_CASES) THEN
  REWRITE_TAC[EL; HD; TL; WORD_ADD_0; LT_SUC] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[ARITH_RULE `SUC n = 1 + n`; GSYM word_add_n2w; WORD_ADD_ASSOC] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `m:N word->byte` THEN
  ASM_REWRITE_TAC[]);;

let bytes_in_mem_def = cake_def
 `(bytes_in_mem (a:N word) [] (m:N word->B) md k <=> T) /\
  (bytes_in_mem a (CONS b bs) m md k <=>
     a IN md /\ ~(a IN k) /\ (m a = b) /\
     bytes_in_mem (word_add a (word 1)) bs m md k)`;;

let bytes_in_mem_IMP = prove
 (`!xs (p:N word). bytes_in_mem p xs m dm dm1 ==> bytes_in_memory p xs m dm`,
  LIST_INDUCT_TAC THEN ASM_SIMP_TAC[bytes_in_mem_def; bytes_in_memory_def]);;

let fun2set_disjoint_union = prove
 (`DISJOINT d1 d2 /\
   p (fun2set ((m:A->B),d1)) /\
   q (fun2set (m,d2))
   ==> (p STAR q) (fun2set (m,d1 UNION d2))`,
  REWRITE_TAC[STAR_def; SPLIT_def] THEN STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`fun2set ((m:A->B),d1)`; `fun2set ((m:A->B),d2)`] THEN
  ASM_REWRITE_TAC[fun2set_def] THEN
  UNDISCH_TAC `DISJOINT (d1:A->bool) d2` THEN
  REWRITE_TAC[EXTENSION; IN_UNION; IN_ELIM_THM; DISJOINT; IN_INTER;
              NOT_IN_EMPTY] THEN
  DISCH_TAC THEN CONJ_TAC THENL [MESON_TAC[]; ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(a:A) = a'` SUBST_ALL_TAC THENL
   [ASM_MESON_TAC[PAIR_EQ]; ASM_MESON_TAC[]]);;

let MISC3AUX_WORD_ADD_SUB_VAL = prove
 (`!(a:N word) b. val a <= val b ==> word_add a (word (val b - val a)) = b`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [GSYM WORD_VAL] THEN
  ASM_SIMP_TAC[word_add_n2w; ARITH_RULE `a <= b ==> a + (b - a) = b:num`;
               WORD_VAL]);;

let WORD_LS_IMP = prove
 (`word_ule (a:N word) b ==>
   ?k. Abbrev (b = word_add a (word k)) /\
       val (word_sub b a) = k /\
       (!w. word_ule a w /\ word_ult w b <=> ?i. w = word_add a (word i) /\ i < k)`,
  REWRITE_TAC[WORD_ULE; WORD_ULT; marker_Abbrev_def] THEN DISCH_TAC THEN
  EXISTS_TAC `val (b:N word) - val (a:N word)` THEN
  ASM_SIMP_TAC[MISC3AUX_WORD_ADD_SUB_VAL; VAL_WORD_SUB_CASES] THEN
  X_GEN_TAC `w:N word` THEN EQ_TAC THENL
   [STRIP_TAC THEN EXISTS_TAC `val (w:N word) - val (a:N word)` THEN
    ASM_SIMP_TAC[MISC3AUX_WORD_ADD_SUB_VAL] THEN ASM_ARITH_TAC;
    DISCH_THEN(X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `val (w:N word) = val (a:N word) + i` (fun th -> REWRITE_TAC[th]) THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MISC3AUX_VAL_WORD_ADD_LT THEN
      MP_TAC(ISPEC `b:N word` VAL_BOUND) THEN REWRITE_TAC[dimword_def] THEN
      ASM_ARITH_TAC;
      ASM_ARITH_TAC]]);;

(* TODO: move to HOL *)
let size_fromAList = prove
 (`!xs:(num#A)list. ALL_DISTINCT (MAP FST xs) ==> size (fromAList xs) = LENGTH xs`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[fromAList_def; sptree_size_def; LENGTH] THEN
  SPEC_TAC(`h:num#A`,`h:num#A`) THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
  REWRITE_TAC[fromAList_def; MAP; ALL_DISTINCT; size_insert; domain_fromAList;
              IN_SET_OF_LIST] THEN
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[ADD1]);;

(* helpers for ALL_DISTINCT_MAP_FST_toSortedAList (HOL4 proves it with
   sptreeTheory SORTED_toSortedAList, which sptree.ml does not have) *)
let MISC3AUX_add_pause_pos = prove
 (`!j (q:(num#A spt)list). 0 < j /\ ALL (\p. 0 < FST p) q ==>
     ALL (\p. 0 < FST p) (spts_to_alist_add_pause j q)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[spts_to_alist_add_pause_def; list_CASE; ALL; FST] THEN
  SPEC_TAC(`h:num#A spt`,`h:num#A spt`) THEN
  REWRITE_TAC[FORALL_PAIR_THM; pair_CASE; ALL; FST] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

let MISC3AUX_spts_to_alist_aux_DISTINCT = prove
 (`!(xs:(num#A spt)list) i acc_cent acc_right acc_left repeat j ys acc2 repeat2.
     spts_to_alist_aux i xs acc_cent acc_right acc_left repeat =
       (j,ys,acc2,repeat2) /\
     ALL (\p. 0 < FST p) xs /\ ALL (\p. 0 < FST p) acc_right /\
     ALL (\p. 0 < FST p) acc_left /\
     ALL_DISTINCT (MAP FST acc_cent) /\ ALL (\k. k < i) (MAP FST acc_cent)
     ==> ALL (\p. 0 < FST p) ys /\ ALL_DISTINCT (MAP FST acc2) /\
         ALL (\k. k < j) (MAP FST acc2)`,
  LIST_INDUCT_TAC THENL
   [REWRITE_TAC[SPTAUX_spts_to_alist_aux_thm; PAIR_EQ] THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (is_var o rhs o concl))) THEN
    ASM_REWRITE_TAC[ALL_APPEND; EVERY_REVERSE];
    ALL_TAC] THEN
  SPEC_TAC(`h:num#A spt`,`h:num#A spt`) THEN
  REWRITE_TAC[FORALL_PAIR_THM; SPTAUX_spts_to_alist_aux_thm; ALL; FST] THEN
  MAP_EVERY X_GEN_TAC [`k:num`; `spt:A spt`] THEN REPEAT GEN_TAC THEN
  COND_CASES_TAC THEN STRIP_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPECL
      [`i + k:num`; `acc_cent:(num#A)list`;
       `spts_to_alist_add_pause k (acc_right:(num#A spt)list)`;
       `spts_to_alist_add_pause k (acc_left:(num#A spt)list)`;
       `repeat:bool`; `j:num`; `ys:(num#A spt)list`; `acc2:(num#A)list`;
       `repeat2:bool`]) THEN
    ASM_SIMP_TAC[MISC3AUX_add_pause_pos] THEN DISCH_THEN MATCH_MP_TAC THEN
    UNDISCH_TAC `ALL (\k. k < i) (MAP FST (acc_cent:(num#A)list))` THEN
    MATCH_MP_TAC MONO_ALL THEN ARITH_TAC;
    FIRST_X_ASSUM(MP_TAC o SPECL
      [`i + k:num`;
       `APPEND (option_CASE (spt_center (spt:A spt)) [] (\c. [(i,c)]))
               (acc_cent:(num#A)list)`;
       `CONS (k,spt_right spt) (acc_right:(num#A spt)list)`;
       `CONS (k,spt_left spt) (acc_left:(num#A spt)list)`;
       `T`; `j:num`; `ys:(num#A spt)list`; `acc2:(num#A)list`;
       `repeat2:bool`]) THEN
    ASM_REWRITE_TAC[ALL; FST] THEN DISCH_THEN MATCH_MP_TAC THEN
    SUBGOAL_THEN `ALL (\k'. k' < i + k) (MAP FST (acc_cent:(num#A)list))`
      ASSUME_TAC THENL
     [UNDISCH_TAC `ALL (\k. k < i) (MAP FST (acc_cent:(num#A)list))` THEN
      MATCH_MP_TAC MONO_ALL THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    SPEC_TAC(`spt_center (spt:A spt)`,`c:A option`) THEN
    MATCH_MP_TAC option_INDUCT THEN
    ASM_REWRITE_TAC[option_CASE; APPEND; MAP; ALL_DISTINCT; ALL; FST] THEN
    CONJ_TAC THENL [ALL_TAC; ASM_ARITH_TAC] THEN
    REWRITE_TAC[GSYM ALL_MEM] THEN DISCH_TAC THEN
    UNDISCH_TAC `ALL (\k. k < i) (MAP FST (acc_cent:(num#A)list))` THEN
    REWRITE_TAC[GSYM ALL_MEM] THEN DISCH_THEN(MP_TAC o SPEC `i:num`) THEN
    ASM_REWRITE_TAC[LT_REFL]]);;

let MISC3AUX_spts_to_alist_DISTINCT = prove
 (`!i (xs:(num#A spt)list) acc_cent.
     ALL (\p. 0 < FST p) xs /\ ALL_DISTINCT (MAP FST acc_cent) /\
     ALL (\k. k < i) (MAP FST acc_cent)
     ==> ALL_DISTINCT (MAP FST (spts_to_alist i xs acc_cent))`,
  MATCH_MP_TAC (cake_ind "spts_to_alist") THEN
  MAP_EVERY X_GEN_TAC [`i:num`; `xs:(num#A spt)list`; `acc_cent:(num#A)list`] THEN
  DISCH_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL
   [`xs:(num#A spt)list`; `i:num`; `acc_cent:(num#A)list`;
    `[]:(num#A spt)list`; `[]:(num#A spt)list`; `F`;
    `FST (spts_to_alist_aux i (xs:(num#A spt)list) acc_cent [] [] F)`;
    `FST (SND (spts_to_alist_aux i (xs:(num#A spt)list) acc_cent [] [] F))`;
    `FST (SND (SND (spts_to_alist_aux i (xs:(num#A spt)list) acc_cent [] [] F)))`;
    `SND (SND (SND (spts_to_alist_aux i (xs:(num#A spt)list) acc_cent [] [] F)))`]
   MISC3AUX_spts_to_alist_aux_DISTINCT) THEN
  ASM_REWRITE_TAC[PAIR; ALL] THEN STRIP_TAC THEN
  ONCE_REWRITE_TAC[SPTAUX_spts_to_alist_eqn] THEN COND_CASES_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o C MATCH_MP (ASSUME
      `SND (SND (SND (spts_to_alist_aux i (xs:(num#A spt)list) acc_cent [] [] F)))`)) THEN
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[GSYM MAP_REVERSE; ALL_DISTINCT_REVERSE]]);;

let ALL_DISTINCT_MAP_FST_toSortedAList = prove
 (`ALL_DISTINCT (MAP FST (toSortedAList (t:A spt)))`,
  REWRITE_TAC[toSortedAList_def] THEN
  MATCH_MP_TAC MISC3AUX_spts_to_alist_DISTINCT THEN
  REWRITE_TAC[ALL; MAP; ALL_DISTINCT; FST] THEN ARITH_TAC);;

let good_dimindex_DEF = new_definition
 `good_dimindex (s:A->bool) <=> dimindex(:A) = 32 \/ dimindex(:A) = 64`;;

let good_dimindex_def = prove
 (`good_dimindex (:A) <=> dimindex (:A) = 32 \/ dimindex (:A) = 64`,
  REWRITE_TAC[good_dimindex_DEF]);;

let good_dimindex_get_byte_set_byte = prove
 (`good_dimindex (:N) ==>
   (get_byte a (set_byte (a:N word) b w be) be = b)`,
  STRIP_TAC THEN MATCH_MP_TAC get_byte_set_byte THEN
  RULE_ASSUM_TAC(REWRITE_RULE[good_dimindex_def]) THEN ASM_ARITH_TAC);;

let byte_index_LESS_IMP = prove
 (`(dimindex (:N) = 32 \/ dimindex (:N) = 64) /\
   byte_index (a:N word) be < byte_index (a':N word) be /\ i < 8 ==>
   byte_index a be + i < byte_index a' be /\
   byte_index a be <= i + byte_index a' be /\
   byte_index a be + 8 <= i + byte_index a' be /\
   i + byte_index a' be < byte_index a be + dimindex (:N)`,
  REWRITE_TAC[byte_index_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  BOOL_CASES_TAC `be:bool` THEN REWRITE_TAC[] THEN
  STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
  CONV_TAC NUM_REDUCE_CONV THEN RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[LT_MULT_LCANCEL; ARITH_EQ]) THEN
  MP_TAC(SPECL [`val(a:N word)`; `4`] MOD_LT_EQ) THEN
  MP_TAC(SPECL [`val(a':N word)`; `4`] MOD_LT_EQ) THEN
  MP_TAC(SPECL [`val(a:N word)`; `8`] MOD_LT_EQ) THEN
  MP_TAC(SPECL [`val(a':N word)`; `8`] MOD_LT_EQ) THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN ARITH_TAC);;

let NOT_w2w_bit = prove
 (`8 <= i /\ i < dimindex (:B) ==> ~(bit i ((word_zx:byte->B word) w))`,
  STRIP_TAC THEN ASM_SIMP_TAC[BIT_WORD_ZX; BIT_TRIVIAL; DIMINDEX_8]);;

let DIV_EQ_DIV_IMP = prove
 (`0 < d /\ ~(n = n') /\ (n DIV d * d = n' DIV d * d) ==>
   ~(n MOD d = n' MOD d)`,
  REPEAT STRIP_TAC THEN UNDISCH_TAC `~(n = n':num)` THEN REWRITE_TAC[] THEN
  MP_TAC(SPECL [`n:num`; `d:num`] DIVISION) THEN
  MP_TAC(SPECL [`n':num`; `d:num`] DIVISION) THEN
  ASM_SIMP_TAC[ARITH_RULE `0 < d ==> ~(d = 0)`] THEN ARITH_TAC);;



let MISC3AUX_byte_align_MOD = prove
 (`!(a:N word) a'.
     (dimindex(:N) = 32 \/ dimindex(:N) = 64) /\ ~(a = a') /\
     byte_align a = byte_align a'
     ==> ~(val a MOD (dimindex(:N) DIV 8) = val a' MOD (dimindex(:N) DIV 8))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC DIV_EQ_DIV_IMP THEN
  ASM_REWRITE_TAC[VAL_EQ] THEN CONV_TAC NUM_REDUCE_CONV THEN
  FIRST_X_ASSUM(MP_TAC o AP_TERM `val:N word->num`) THEN
  REWRITE_TAC[byte_align_def; align_w2n] THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[MISC3AUX_LOG2_4; MISC3AUX_LOG2_8] THEN CONV_TAC NUM_REDUCE_CONV THEN
  SUBGOAL_THEN `!(x:N word) k. val x DIV k * k < 2 EXP dimindex(:N)`
    (fun th -> SIMP_TAC[th; VAL_WORD_EQ]) THEN
  REPEAT GEN_TAC THEN MATCH_MP_TAC LET_TRANS THEN EXISTS_TAC `val (x:N word)` THEN
  REWRITE_TAC[VAL_BOUND] THEN ONCE_REWRITE_TAC[MULT_SYM] THEN
  REWRITE_TAC[DIV_MUL_LE]);;

let MISC3AUX_byte_index_neq = prove
 (`!(a:N word) (a':N word) be.
     (dimindex(:N) = 32 \/ dimindex(:N) = 64) /\
     ~(val a MOD (dimindex(:N) DIV 8) = val a' MOD (dimindex(:N) DIV 8))
     ==> ?u v. byte_index a be = 8 * u /\ byte_index a' be = 8 * v /\
               ~(u = v) /\ 8 * u + 8 <= dimindex(:N) /\
               8 * v + 8 <= dimindex(:N)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  EXISTS_TAC `if be then dimindex(:N) DIV 8 - 1 - val (a:N word) MOD (dimindex(:N) DIV 8)
              else val a MOD (dimindex(:N) DIV 8)` THEN
  EXISTS_TAC `if be then dimindex(:N) DIV 8 - 1 - val (a':N word) MOD (dimindex(:N) DIV 8)
              else val a' MOD (dimindex(:N) DIV 8)` THEN
  REWRITE_TAC[byte_index_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  BOOL_CASES_TAC `be:bool` THEN REWRITE_TAC[] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (is_eq o concl)) THEN
  CONV_TAC NUM_REDUCE_CONV THEN RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV) THEN
  MP_TAC(SPECL [`val(a:N word)`; `4`] MOD_LT_EQ) THEN
  MP_TAC(SPECL [`val(a':N word)`; `4`] MOD_LT_EQ) THEN
  MP_TAC(SPECL [`val(a:N word)`; `8`] MOD_LT_EQ) THEN
  MP_TAC(SPECL [`val(a':N word)`; `8`] MOD_LT_EQ) THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN ARITH_TAC);;

let get_byte_set_byte_diff = prove
 (`good_dimindex (:N) /\ ~(a = a') /\ (byte_align a = byte_align a') ==>
   (get_byte a (set_byte (a':N word) b w be) be = get_byte a w be)`,
  REWRITE_TAC[good_dimindex_def] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC STRIP_ASSUME_TAC) THEN
  MP_TAC(SPECL [`a:N word`; `a':N word`; `be:bool`] MISC3AUX_byte_index_neq) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[MISC3AUX_byte_align_MOD]; ALL_TAC] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`u:num`; `v:num`] THEN STRIP_TAC THEN
  REWRITE_TAC[get_byte_def; set_byte_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  ASM_REWRITE_TAC[WORD_EQ_BITS_ALT; DIMINDEX_8] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[BIT_WORD_ZX; BIT_WORD_USHR; BIT_WORD_OR_ALT; BIT_WORD_SLICE_ALT;
                  BIT_WORD_SHL; DIMINDEX_8] THEN
  ASM_CASES_TAC `u < v:num` THENL
   [SUBGOAL_THEN `~(8 * v + 8 <= i + 8 * u) /\ ~(8 * v <= i + 8 * u) /\
                  i + 8 * u < 8 * v /\ 0 <= i + 8 * u`
      (fun th -> REWRITE_TAC[th]) THEN ASM_ARITH_TAC;
    SUBGOAL_THEN `8 * v + 8 <= i + 8 * u /\ i + 8 * u < dimindex(:N) /\
                  ~(i + 8 * u < 8 * v) /\ ~(bit ((i + 8 * u) - 8 * v) (b:byte))`
      (fun th -> REWRITE_TAC[th]) THEN
    CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC(TAUT `(p <=> F) ==> ~p`) THEN MATCH_MP_TAC BIT_TRIVIAL THEN
    REWRITE_TAC[DIMINDEX_8] THEN ASM_ARITH_TAC]);;

(* helpful theorems for _size *)
let list_size_pair_size_MAP_FST_SND = prove
 (`list_size (pair_size (f:A->num) (g:B->num)) ls =
   list_size f (MAP FST ls) + list_size g (MAP SND ls)`,
  SPEC_TAC(`ls:(A#B)list`,`ls:(A#B)list`) THEN
  LIST_INDUCT_TAC THEN REWRITE_TAC[list_size; MAP; ADD_CLAUSES] THEN
  POP_ASSUM MP_TAC THEN SPEC_TAC(`h:A#B`,`h:A#B`) THEN
  REWRITE_TAC[FORALL_PAIR_THM; pair_size_THM] THEN ARITH_TAC);;

let MEM_list_size = prove
 (`MEM x ls ==> (f:A->num) x <= list_size f ls`,
  MESON_TAC[MEM_LIST_SIZE; LT_IMP_LE]);;

(* must be used instead of FUPDATE in defitions that go through translation *)
let fmap_update_def = cake_def
 `fmap_update (f:(A,B)fmap) k v = f |+ (k,v)`;;
let _ = cake_add_simps [fmap_update_def];;

(* TODO: move to HOL? *)
(* HOL4 num_cmp and pair_cmp are num_compare and pair_compare *)
let sum_cmp_def = cake_def
 `sum_cmp (c1:A->B->ordering) (c2:C->D->ordering) (x1:A+C) (x2:B+D) =
    match x1 with
      INL n1 -> (match x2 with INL n2 -> c1 n1 n2 | INR _ -> LESS)
    | INR n1 -> (match x2 with INL _ -> GREATER | INR n2 -> c2 n1 n2)`;;

let TotOrd_sum = prove
 (`TotOrd (c1:A->A->ordering) /\ TotOrd (c2:B->B->ordering) ==>
   TotOrd (sum_cmp c1 c2)`,
  REWRITE_TAC[TotOrd; sum_cmp_def; FORALL_SUM; sum_CASE] THEN
  REWRITE_TAC[distinctness "ordering"; injectivity "sum"; distinctness "sum"] THEN
  MESON_TAC[]);;

let TotOrd_num_cmp = prove
 (`TotOrd num_compare`,
  REWRITE_TAC[num_cmp_numOrd; TO_numOrd]);;

(* the shape num_cmp shares with mlint$int_cmp *)
let num_cmp_thm = prove
 (`num_compare n1 n2 =
     if n1 < n2 then LESS else
     if n2 < n1 then GREATER else EQUAL`,
  REWRITE_TAC[num_compare_def] THEN
  ASM_CASES_TAC `n1:num = n2` THEN ASM_REWRITE_TAC[LT_REFL] THEN
  ASM_CASES_TAC `n1 < n2` THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

let TotOrd_pair_cmp = prove
 (`TotOrd (c1:A->A->ordering) /\ TotOrd (c2:B->B->ordering) ==>
   TotOrd (pair_compare c1 c2)`,
  SIMP_TAC[pair_cmp_lexTO; TO_lexTO]);;

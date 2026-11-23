(* ========================================================================= *)
(* misc_p1: port of HOL4 misc/miscScript.sml (CakeML v3479), part 1 of 3:    *)
(* the script up to (not including) FOLDL_invariant.                         *)
(* Miscellaneous definitions and minor lemmas used throughout the            *)
(* development.                                                              *)
(* HOL4 the is misc_the (a short name), and the_def is misc_the_def.         *)
(* ========================================================================= *)

needs "hol4/vocab.ml";;
needs "hol4/list.ml";;
needs "hol4/rich_list.ml";;
needs "hol4/basic.ml";;
needs "hol4/finite_map.ml";;
needs "hol4/alist.ml";;
needs "hol4/sorting.ml";;
needs "hol4/sptree.ml";;
needs "hol4/words4.ml";;
needs "hol4/numposrep.ml";;

prioritize_num();;
type_invention_error := true;;

(* Total version of THE *)
let misc_the_def = cake_def
  `(misc_the (d:A) (SOME x) = x) /\
   (misc_the x NONE = x)`;;

let opt_bind_def = cake_def
  `opt_bind (n:A option) (v:B) e =
     match n with
       NONE -> e
     | SOME n' -> CONS (n',v) e`;;

(* theorem behind impl_tac *)
let misc_IMP_IMP = prove
 (`(P /\ (Q ==> R)) ==> ((P ==> Q) ==> R)`,
  MESON_TAC[]);;

(* used elsewhere in cakeml *)
let SUBSET_IMP = prove
 (`s SUBSET t ==> ((x:A) IN s ==> x IN t)`,
  REWRITE_TAC[SUBSET] THEN MESON_TAC[]);;

let DROP_NIL = prove
 (`!n (xs:A list). DROP n xs = [] <=> LENGTH xs <= n`,
  INDUCT_TAC THEN GEN_TAC THEN CASES_ON `xs:A list` THEN
  FS[DROP_def; LENGTH] THEN ARITH_TAC);;

let revdroprev = prove
 (`!(l:A list) n.
     n <= LENGTH l ==> REVERSE (DROP n (REVERSE l)) = TAKE (LENGTH l - n) l`,
  SIMP[GSYM BUTLASTN_def; BUTLASTN_TAKE]);;

let revtakerev = prove
 (`!n (l:A list).
     n <= LENGTH l ==> REVERSE (TAKE n (REVERSE l)) = DROP (LENGTH l - n) l`,
  INDUCT_TAC THEN SIMP[DROP_LENGTH_NIL] THEN
  X_GEN_TAC `l:A list` THEN
  STRIP_ASSUME_TAC(ISPEC `l:A list` SNOC_CASES) THEN ASM_REWRITE_TAC[] THENL
   [REWRITE_TAC[LENGTH; LT]; ALL_TAC] THEN
  REWRITE_TAC[REVERSE_SNOC; LENGTH_SNOC; TAKE_def; NOT_SUC; SUC_SUB1;
              LT_SUC_LE; SUB_SUC; REVERSE] THEN
  DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `l':A list`) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[SNOC_APPEND] THEN
  SIMP[DROP_APPEND1; ARITH_RULE `!m n. m - n <= m:num`]);;

let times_add_o = prove
 (`(\n:num. k * n + x) = ((+) x) o ((*) k)`,
  REWRITE_TAC[FUN_EQ_THM; o_THM] THEN ARITH_TAC);;

let SORTED_inv_image_LESS_PLUS = prove
 (`SORTED (inv_image (<) ((+) k)) = SORTED (<)`,
  AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM; inv_image_THM; LT_ADD_LCANCEL]);;

let SORTED_GENLIST_TIMES = prove
 (`0 < k ==> !n. SORTED (<) (list_of_seq (( * ) k) n)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[SORTED_EL_SUC; LENGTH_GENLIST] THEN
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[EL_GENLIST; ARITH_RULE `SUC m < n ==> m < n`] THEN
  ASM_REWRITE_TAC[LT_MULT_LCANCEL; ARITH_RULE `m < SUC m`] THEN
  ASM_ARITH_TAC);;

(* this is
     read_bytearray a c gb = OPT_MMAP gb (GENLIST (\i. a + n2w i) c)
*)
let read_bytearray_def = cake_def
  `(read_bytearray (a:A word) 0 (gb:A word->B option) = SOME []) /\
   (read_bytearray a (SUC n) gb =
      match gb a with
        NONE -> NONE
      | SOME b -> (match read_bytearray (word_add a (word 1)) n gb with
                     NONE -> NONE
                   | SOME bs -> SOME (CONS b bs)))`;;

(* HOL to have OPT_MMAP f l1 = SOME l2 ==> (LENGTH l2 = LENGTH l1) *)
let read_bytearray_LENGTH = prove
 (`!n (a:A word) (f:A word->B option) x.
     read_bytearray a n f = SOME x ==> LENGTH x = n`,
  INDUCT_TAC THEN FS[read_bytearray_def] THEN REPEAT STRIP_TAC THEN
  EVERY_CASE_TAC THEN FS[] THEN RW[] THEN RES_TAC THEN ASM_REWRITE_TAC[]);;

let shift_seq_def = cake_def
  `shift_seq (k:num) (s:num->A) = \i. s (i + k)`;;

(* TODO: Used once in all of CakeML: could probably be pushed back to use-site*)
let SUM_SET_IN_LT = prove
 (`!s x y. FINITE s /\ x IN s /\ y < x ==> y < SUM_SET s`,
  MESON_TAC[SUM_SET_IN_LE; LTE_TRANS]);;

(* only used in proof of tlookup_bij_iff *)
let CARD_IMAGE_ID_BIJ = prove
 (`!s. FINITE s ==>
       (!x. x IN s ==> (f:A->A) x IN s) /\ CARD (IMAGE f s) = CARD s ==>
       BIJ f s s`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `SURJ (f:A->A) s s`
    (fun th -> ASM_MESON_TAC[th; FINITE_SURJ_BIJ]) THEN
  REWRITE_TAC[IMAGE_SURJ] THEN
  SUBGOAL_THEN `IMAGE (f:A->A) s SUBSET s` ASSUME_TAC THENL
   [ASM SET_TAC[]; ASM_MESON_TAC[SUBSET_EQ_CARD; FINITE_IMAGE]]);;

(* never used *)
let CARD_IMAGE_EQ_BIJ = prove
 (`!s. FINITE s ==> CARD (IMAGE (f:A->B) s) = CARD s ==> BIJ f s (IMAGE f s)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `SURJ (f:A->B) s (IMAGE f s)`
    (fun th -> ASM_MESON_TAC[th; FINITE_SURJ_BIJ]) THEN
  REWRITE_TAC[IMAGE_SURJ]);;

(* used only in clos_callProof -
   HOL has DISJOINT_IMAGE:
     |- (!x y. f x = f y <=> x = y) ==>
        (DISJOINT (IMAGE f x) (IMAGE f y) <=> DISJOINT x y
*)
let DISJOINT_IMAGE_SUC = prove
 (`DISJOINT (IMAGE SUC x) (IMAGE SUC y) <=> DISJOINT x y`,
  REWRITE_TAC[IN_DISJOINT; IN_IMAGE] THEN MESON_TAC[SUC_INJ]);;

(* disgusting and used only in clos_callProof *)
let IMAGE_SUC_SUBSET_UNION = prove
 (`IMAGE SUC x SUBSET IMAGE SUC y UNION IMAGE SUC z <=> x SUBSET y UNION z`,
  REWRITE_TAC[SUBSET; IN_UNION; IN_IMAGE] THEN MESON_TAC[SUC_INJ]);;

(* HOL4: Overload LLOOKUP = \l n. oEL n l.  The port writes oEL n l for     *)
(* LLOOKUP l n, so these theorems are the oEL theorems of list.ml.         *)

let LLOOKUP_def = oEL_def;;
let LLOOKUP_EQ_EL = oEL_EQ_EL;;
let LLOOKUP_THM = oEL_THM;;
let LLOOKUP_DROP = oEL_DROP;;
let LLOOKUP_TAKE_IMP = oEL_TAKE_E;;
let LLOOKUP_LUPDATE = oEL_LUPDATE;;

(* app_list stuff should be in an app_list theory *)
(* HOL4 constructors List and Append are misc_List and misc_Append *)
let app_list_INDUCT,app_list_RECURSION =
  cake_type "app_list = misc_List (A list) | misc_Append app_list app_list | Nil";;

let append_aux_def = cake_def
  `(append_aux (Nil:A app_list) aux = aux) /\
   (append_aux (misc_List xs) aux = APPEND xs aux) /\
   (append_aux (misc_Append l1 l2) aux = append_aux l1 (append_aux l2 aux))`;;

let append_def = cake_def
  `append (l:A app_list) = append_aux l []`;;

let append_aux_thm = prove
 (`!(l:A app_list) xs. append_aux l xs = APPEND (append_aux l []) xs`,
  MATCH_MP_TAC app_list_INDUCT THEN
  METIS_TAC[APPEND; APPEND_ASSOC; APPEND_NIL; append_aux_def]);;

let append_thm = prove
 (`append (misc_Append (l1:A app_list) l2) = APPEND (append l1) (append l2) /\
   append (misc_List (xs:A list)) = xs /\
   append (Nil:A app_list) = []`,
  FS[append_def; append_aux_def] THEN
  ONCE_REWRITE_TAC[append_aux_thm] THEN FS[]);;
let _ = cake_add_simps [append_thm];;

(* HOL4 states the definition with overlapping patterns (first match wins); *)
(* these are the disjoint clauses that HOL4 derives from them.             *)
let SmartAppend_def = cake_def
  `(SmartAppend (Nil:A app_list) l2 = l2) /\
   (SmartAppend (misc_List xs) Nil = misc_List xs) /\
   (SmartAppend (misc_Append a b) Nil = misc_Append a b) /\
   (SmartAppend (misc_List xs) (misc_List ys) =
      misc_Append (misc_List xs) (misc_List ys)) /\
   (SmartAppend (misc_List xs) (misc_Append c d) =
      misc_Append (misc_List xs) (misc_Append c d)) /\
   (SmartAppend (misc_Append a b) (misc_List ys) =
      misc_Append (misc_Append a b) (misc_List ys)) /\
   (SmartAppend (misc_Append a b) (misc_Append c d) =
      misc_Append (misc_Append a b) (misc_Append c d))`;;
let _ = cake_add_simps [SmartAppend_def];;

let SmartAppend_thm = prove
 (`!(l1:A app_list) l2.
     SmartAppend l1 l2 =
       if l1 = Nil then l2 else
       if l2 = Nil then l1 else misc_Append l1 l2`,
  GEN_TAC THEN CASES_ON `l1:A app_list` THEN GEN_TAC THEN
  CASES_ON `l2:A app_list` THEN RW[]);;

let SmartAppend_Nil = prove
 (`SmartAppend (l:A app_list) Nil = l /\
   SmartAppend Nil l = l`,
  CASES_ON `l:A app_list` THEN GVS[SmartAppend_def]);;

let append_SmartAppend = prove
 (`append (SmartAppend (l1:A app_list) l2) = APPEND (append l1) (append l2)`,
  RW[append_def; SmartAppend_thm; append_aux_def] THEN
  ONCE_REWRITE_TAC[append_aux_thm] THEN REWRITE_TAC[APPEND_NIL]);;
let _ = cake_add_simps [append_SmartAppend];;

(* instant derivation from LIST_EQ_REWRITE *)
let GENLIST_eq_MAP = prove
 (`list_of_seq (f:num->B) n = MAP (g:A->B) ls <=>
   LENGTH ls = n /\ !m. m < n ==> f m = g (EL m ls)`,
  REWRITE_TAC[LIST_EQ_REWRITE; LENGTH_GENLIST; LENGTH_MAP] THEN
  EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `m:num`) THEN
    ASM_SIMP_TAC[EL_GENLIST; EL_MAP];
    FIRST_X_ASSUM(MP_TAC o SPEC `x:num`) THEN
    ASM_SIMP_TAC[EL_GENLIST; EL_MAP] THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN ASM_SIMP_TAC[EL_MAP]]);;

(* TODO - already in HOL as ZIP_GENLIST *)
let ZIP_GENLIST1 = prove
 (`!(l:B list) (f:num->A) n. LENGTH l = n ==>
     ZIP (list_of_seq f n) l = list_of_seq (\x. (f x, EL x l)) n`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[LIST_EQ_REWRITE; LENGTH_ZIP; LENGTH_GENLIST; EL_ZIP;
               EL_GENLIST]);;

(* used once *)
let MAP_REVERSE_STEP = prove
 (`!(x:A list) (f:A->B). ~(x = []) ==>
     MAP f (REVERSE x) = CONS (f (LAST x)) (MAP f (REVERSE (BUTLAST x)))`,
  GEN_TAC THEN STRIP_ASSUME_TAC(ISPEC `x:A list` SNOC_CASES) THEN
  ASM_REWRITE_TAC[] THEN
  SIMP[REVERSE_SNOC; LAST_SNOC; FRONT_SNOC; NOT_SNOC_NIL]);;

(* used three times, once with MIN_DEF alongside, which turns it into
   LENGTH_TAKE_EQ
*)
let LENGTH_TAKE_EQ_MIN = prove
 (`!n (xs:A list). LENGTH (TAKE n xs) = MIN n (LENGTH xs)`,
  REWRITE_TAC[LENGTH_TAKE_EQ; MIN] THEN ARITH_TAC);;

(* should be switched in orientation; looks like an attempt to get congruence
   rule *)
let LIST_REL_MEM = prove
 (`!(xs:A list) (ys:B list) P. ALL2 P xs ys <=>
     ALL2 (\x y. MEM x xs /\ MEM y ys ==> P x y) xs ys`,
  REWRITE_TAC[LIST_REL_EL_EQN] THEN MESON_TAC[MEM_EL]);;

(* only used in theorem immediately below *)
let LIST_REL_GENLIST_I = prove
 (`!(xs:A list). ALL2 P (list_of_seq I (LENGTH xs)) xs <=>
     !n. n < LENGTH xs ==> P n (EL n xs)`,
  SIMP[LIST_REL_EL_EQN; LENGTH_GENLIST] THEN
  MESON_TAC[EL_GENLIST; I_THM]);;

(* only used in bvi_to_dataProof *)
let LIST_REL_lookup_fromList = prove
 (`ALL2 (\v x. lookup v (fromList args) = SOME (x:A))
     (list_of_seq I (LENGTH args)) args`,
  REWRITE_TAC[LIST_REL_GENLIST_I; lookup_fromList] THEN SIMP_TAC[]);;

let LIST_REL_lookup_fromList_MAP = prove
 (`ALL2 (\v x. ?z. lookup v (fromList args) = SOME (z:A) /\ x = (f:A->B) z)
     (list_of_seq I (LENGTH args)) (MAP f args)`,
  REWRITE_TAC[LIST_REL_MAP2; LIST_REL_GENLIST_I; lookup_fromList] THEN
  SIMP_TAC[option_INJ] THEN MESON_TAC[]);;

(* only used in examples/stackProg; oriented badly *)
let LIST_REL_FRONT_LAST = prove
 (`~((l1:A list) = []) /\ ~((l2:B list) = []) ==>
   (ALL2 R l1 l2 <=>
    ALL2 R (BUTLAST l1) (BUTLAST l2) /\ R (LAST l1) (LAST l2))`,
  STRIP_ASSUME_TAC(ISPEC `l1:A list` SNOC_CASES) THEN
  STRIP_ASSUME_TAC(ISPEC `l2:B list` SNOC_CASES) THEN
  ASM_REWRITE_TAC[NOT_SNOC_NIL] THEN
  SIMP[LIST_REL_SNOC; FRONT_SNOC; LAST_SNOC; SNOC_11] THEN MESON_TAC[]);;

(* HOL4 [local]; in HOL4 the first subtraction is applied to the sum *)
let lemmas = prove
 (`((2 + 2 * n) - 1 = 2 * n + 1) /\
   (2 + 2 * n' = 2 * n'' + 2 <=> n' = n'') /\
   (2 * m = 2 * n <=> m = n) /\
   ((2 * n'' + 1) DIV 2 = n'') /\
   ((2 * n) DIV 2 = n) /\
   ~(2 + 2 * n' = 2 * n'' + 1) /\
   ~(2 * m + 1 = 2 * n' + 2)`,
  REPEAT CONJ_TAC THEN TRY ARITH_TAC THEN
  DISCH_THEN(MP_TAC o AP_TERM `EVEN`) THEN
  REWRITE_TAC[EVEN_ADD; EVEN_MULT; ARITH]);;

let lookup_any_def = cake_def
  `lookup_any x (sp:A spt) d =
     match lookup x sp with
       NONE -> d
     | SOME m -> m`;;

let fromList2_def = cake_def
  `fromList2 (l:A list) =
     SND (FOLDL (\(i,t) a. (i + 2,insert i a t)) (0,LN) l)`;;

(* HOL4 [local] *)
let EVEN_fromList2_lemma = prove
 (`!(l:A list) n t.
     EVEN n /\ (!x. x IN domain t ==> EVEN x) ==>
     !x. x IN domain (SND (FOLDL (\(i,t) a. (i + 2,insert i a t)) (n,t) l))
         ==> EVEN x`,
  LIST_INDUCT_TAC THENL [REWRITE_TAC[FOLDL; SND] THEN MESON_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[FOLDL] THEN
  MAP_EVERY X_GEN_TAC [`n:num`; `tr:A spt`] THEN STRIP_TAC THEN
  X_GEN_TAC `x:num` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`n + 2`; `insert n (h:A) tr`]) THEN
  ASM_REWRITE_TAC[domain_insert; IN_INSERT; EVEN_ADD; ARITH] THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

let EVEN_fromList2 = prove
 (`!(l:A list) n. n IN domain (fromList2 l) ==> EVEN n`,
  REWRITE_TAC[fromList2_def] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`l:A list`; `0`; `LN:A spt`] EVEN_fromList2_lemma) THEN
  REWRITE_TAC[domain_def; NOT_IN_EMPTY; EVEN] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

let SUBMAP_mono_FUPDATE_LIST = prove
 (`!ls (f:(A,B)fmap) g.
     DRESTRICT f (COMPL (set_of_list (MAP FST ls))) SUBMAP
     DRESTRICT g (COMPL (set_of_list (MAP FST ls)))
     ==> f |++ ls SUBMAP g |++ ls`,
  LIST_INDUCT_TAC THENL
   [REWRITE_TAC[FUPDATE_LIST_THM; MAP; set_of_list; COMPL_DEF; DIFF_EMPTY;
                DRESTRICT_UNIV];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[FUPDATE_LIST_THM] THEN DISCH_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  POP_ASSUM MP_TAC THEN SUBST1_TAC(ISPEC `h:A#B` (GSYM PAIR)) THEN
  REWRITE_TAC[SUBMAP_FLOOKUP_EQN; FLOOKUP_DRESTRICT; FLOOKUP_UPDATE; MAP;
              set_of_list; IN_COMPL; IN_INSERT] THEN
  DISCH_TAC THEN REPEAT GEN_TAC THEN
  REPEAT COND_CASES_TAC THEN ASM_MESON_TAC[]);;

let INJ_FAPPLY_FUPDATE = prove
 (`INJ (FAPPLY (f:(A,B)fmap)) (FDOM f) (FRANGE f) /\
   s = k INSERT FDOM f /\ ~(v IN FRANGE f) /\
   t = v INSERT FRANGE f
   ==> INJ (FAPPLY (f |+ (k,v))) s t`,
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[INJ; FAPPLY_FUPDATE_THM; IN_INSERT] THEN
  REPEAT STRIP_TAC THEN REPEAT(POP_ASSUM MP_TAC) THEN
  REWRITE_TAC[INJ; IN_FRANGE] THEN
  REPEAT COND_CASES_TAC THEN ASM_MESON_TAC[]);;

(* used in only one place: stack_to_labProof *)
let BIJ_FLOOKUP_MAP_KEYS = prove
 (`BIJ (bij:A->B) UNIV UNIV ==>
   FLOOKUP (MAP_KEYS (LINV bij UNIV) (f:(B,C)fmap)) n = FLOOKUP f (bij n)`,
  STRIP_TAC THEN
  SUBGOAL_THEN `!x:A. LINV (bij:A->B) UNIV (bij x) = x` ASSUME_TAC THENL
   [ASM_MESON_TAC[LINV_DEF; BIJ; IN_UNIV]; ALL_TAC] THEN
  SUBGOAL_THEN `!y:B. bij (LINV (bij:A->B) UNIV y) = y` ASSUME_TAC THENL
   [ASM_MESON_TAC[BIJ_LINV_INV; IN_UNIV]; ALL_TAC] THEN
  SUBGOAL_THEN `INJ (LINV (bij:A->B) UNIV) (FDOM (f:(B,C)fmap)) UNIV`
    ASSUME_TAC THENL
   [REWRITE_TAC[INJ; IN_UNIV] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[FLOOKUP_DEF; MAP_KEYS_def] THEN
  SUBGOAL_THEN `(n:A) IN IMAGE (LINV (bij:A->B) UNIV) (FDOM (f:(B,C)fmap)) <=>
                bij n IN FDOM f` SUBST1_TAC THENL
   [REWRITE_TAC[IN_IMAGE] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  COND_CASES_TAC THEN REWRITE_TAC[option_INJ] THEN
  MP_TAC(ISPECL [`LINV (bij:A->B) UNIV`; `f:(B,C)fmap`] MAP_KEYS_def) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `(bij:A->B) n` o CONJUNCT2) THEN
  ASM_REWRITE_TAC[]);;

let SPLIT_LIST = prove
 (`!xs:A list.
     ?ys zs. (xs = APPEND ys zs) /\
             (LENGTH xs DIV 2 = LENGTH ys)`,
  GEN_TAC THEN
  MAP_EVERY EXISTS_TAC [`TAKE (LENGTH (xs:A list) DIV 2) xs`;
                        `DROP (LENGTH (xs:A list) DIV 2) xs`] THEN
  REWRITE_TAC[TAKE_DROP] THEN CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC LENGTH_TAKE THEN REWRITE_TAC[DIV_LE]);;

let EXISTS_ZIP = prove
 (`!(l:(A#B) list) f. EX (\(x,y). f x) l <=> EX f (MAP FST l)`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[EX; MAP] THEN GEN_TAC THEN
  SUBST1_TAC(ISPEC `h:A#B` (GSYM PAIR)) THEN REWRITE_TAC[FST]);;

let EVERY_ZIP = prove
 (`!(l:(A#B) list) f. ALL (\(x,y). f x) l <=> ALL f (MAP FST l)`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[ALL; MAP] THEN GEN_TAC THEN
  SUBST1_TAC(ISPEC `h:A#B` (GSYM PAIR)) THEN REWRITE_TAC[FST]);;

let every_zip_split = prove
 (`!(l1:A list) (l2:B list) P Q.
     LENGTH l1 = LENGTH l2 ==>
     (ALL (\(x,y). P x /\ Q y) (ZIP l1 l2) <=> ALL P l1 /\ ALL Q l2)`,
  LIST_INDUCT_TAC THEN SIMP[] THEN LIST_INDUCT_TAC THEN
  SIMP[ZIP_def; LENGTH; NOT_SUC] THEN RW[] THEN METIS_TAC[]);;

let every_shim = prove
 (`!(l:(A#B) list) P. ALL (\(x,y). P y) l <=> ALL P (MAP SND l)`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[ALL; MAP] THEN GEN_TAC THEN
  SUBST1_TAC(ISPEC `h:A#B` (GSYM PAIR)) THEN REWRITE_TAC[SND]);;

let every_shim2 = prove
 (`!(l:(A#B) list) P Q. ALL (\(x,y). P x /\ Q y) l <=>
     (ALL (\x. P (FST x)) l /\ ALL (\x. Q (SND x)) l)`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[ALL; MAP] THEN REPEAT GEN_TAC THEN
  SUBST1_TAC(ISPEC `h:A#B` (GSYM PAIR)) THEN REWRITE_TAC[FST; SND] THEN
  MESON_TAC[]);;

(* HOL4 ZIP truncates the longer list; HOL Light's ZIP l1 l2 has the       *)
(* length of l1 (HD and TL of l2), so the port assumes                    *)
(* LENGTH l1 <= LENGTH l2 (as list.ml does for LENGTH_ZIP_MIN).           *)
let MEM_ZIP2 = prove
 (`!(l1:A list) (l2:B list) x.
     LENGTH l1 <= LENGTH l2 /\ MEM x (ZIP l1 l2) ==>
     ?n. n < LENGTH l1 /\ n < LENGTH l2 /\ x = (EL n l1,EL n l2)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[ZIP_def; MEM] THEN
  GEN_TAC THEN CASES_ON `l2:B list` THEN
  REWRITE_TAC[LENGTH; ARITH_RULE `~(SUC n <= 0)`; LE_SUC; ZIP_def; MEM] THEN
  REPEAT STRIP_TAC THENL
   [EXISTS_TAC `0` THEN ASM_REWRITE_TAC[EL; HD; LT_0];
    FIRST_X_ASSUM(MP_TAC o SPECL [`a1:B list`; `x:A#B`]) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    EXISTS_TAC `SUC n` THEN ASM_REWRITE_TAC[EL; TL; LT_SUC]]);;

let ZIP_MAP_FST_SND_EQ = prove
 (`!ls:(A#B) list. ZIP (MAP FST ls) (MAP SND ls) = ls`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[MAP; ZIP_def; PAIR]);;

let MAP_FST_I_PAIR_MAP = prove
 (`!(xs:(A#B) list) (f:B->C). MAP FST (MAP (I ## f) xs) = MAP FST xs`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[MAP; FST_PAIR_MAP; I_THM]);;
let _ = cake_add_simps [MAP_FST_I_PAIR_MAP];;

let EVERY_FST_SND = prove
 (`ALL (\(a,b). P a /\ Q b) (ls:(A#B) list) <=>
   ALL P (MAP FST ls) /\ ALL Q (MAP SND ls)`,
  REWRITE_TAC[GSYM ALL_MEM; MEM_MAP; FORALL_PAIR_THM; EXISTS_PAIR_THM] THEN
  MESON_TAC[]);;

let zlookup_def = cake_def
  `zlookup (m:num spt) k = match lookup k m with NONE -> 0 | SOME k -> k`;;

let tlookup_def = cake_def
  `tlookup (m:num spt) k = match lookup k m with NONE -> k | SOME k -> k`;;

let tlookup_id = prove
 (`~(x IN domain names) ==> tlookup names x = x`,
  REWRITE_TAC[tlookup_def; domain_lookup] THEN
  CASES_ON `lookup x (names:num spt)` THEN
  REWRITE_TAC[option_CASE; option_INJ] THEN MESON_TAC[]);;

let tlookup_bij_suff = prove
 (`set_of_list (toList names) = domain names ==>
   BIJ (tlookup names) UNIV UNIV`,
  DISCH_TAC THEN MATCH_MP_TAC BIJ_support THEN
  EXISTS_TAC `domain (names:num spt)` THEN
  REWRITE_TAC[SUBSET_UNIV; tlookup_id] THEN
  SUBGOAL_THEN `set_of_list (toList names) = IMAGE (tlookup names) (domain names)`
    ASSUME_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_SET_OF_LIST; MEM_toList; IN_IMAGE;
                domain_lookup; tlookup_def] THEN
    X_GEN_TAC `y:num` THEN EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_TAC `k:num`) THEN EXISTS_TAC `k:num` THEN
      ASM_REWRITE_TAC[option_CASE] THEN ASM_MESON_TAC[];
      DISCH_THEN(X_CHOOSE_THEN `k:num` (CONJUNCTS_THEN2 MP_TAC
        (X_CHOOSE_TAC `v:num`))) THEN
      ASM_REWRITE_TAC[option_CASE] THEN ASM_MESON_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_IMP] CARD_IMAGE_ID_BIJ) THEN
  REWRITE_TAC[FINITE_domain] THEN
  CONJ_TAC THENL [ASM SET_TAC[]; ASM_MESON_TAC[]]);;

let tlookup_bij_iff = prove
 (`BIJ (tlookup names) UNIV UNIV <=>
   set_of_list (toList names) = domain names`,
  EQ_TAC THEN REWRITE_TAC[tlookup_bij_suff] THEN
  REWRITE_TAC[BIJ; INJ; SURJ; IN_UNIV] THEN STRIP_TAC THEN
  REWRITE_TAC[EXTENSION; IN_SET_OF_LIST; MEM_toList; domain_lookup] THEN
  X_GEN_TAC `x:num` THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_TAC `k:num`) THEN
    ASM_CASES_TAC `k:num = x` THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    SUBGOAL_THEN `tlookup names x = x` ASSUME_TAC THENL
     [MATCH_MP_TAC tlookup_id THEN ASM_REWRITE_TAC[domain_lookup];
      ALL_TAC] THEN
    SUBGOAL_THEN `tlookup names k = x` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[tlookup_def; option_CASE]; ALL_TAC] THEN
    ASM_MESON_TAC[];
    DISCH_THEN(X_CHOOSE_TAC `v:num`) THEN
    ASM_CASES_TAC `x:num = v` THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    SUBGOAL_THEN `tlookup names x = v` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[tlookup_def; option_CASE]; ALL_TAC] THEN
    SUBGOAL_THEN `!k. ~(tlookup names k = x)` ASSUME_TAC THENL
     [X_GEN_TAC `k:num` THEN REWRITE_TAC[tlookup_def] THEN
      CASES_ON `lookup k (names:num spt)` THEN REWRITE_TAC[option_CASE] THEN
      ASM_MESON_TAC[option_DISTINCT];
      ALL_TAC] THEN
    ASM_MESON_TAC[]]);;

(* should be composition of oEL and as-yet-undefined "THE default" *)
let any_el_def = cake_def
  `(any_el n ([]:A list) d = d) /\
   (any_el n (CONS x xs) d = if n = 0 then x else any_el (n - 1) xs d)`;;

let update_resize_def = cake_def
  `update_resize (ls:A list) default v n =
     if n < LENGTH ls then
       LUPDATE v n ls
     else
       LUPDATE v n (APPEND ls (REPLICATE ((n * 2 + 1) - LENGTH ls) default))`;;

(*TODO upstream*)
let MAX_LIST_APPEND = prove
 (`MAX_LIST (APPEND xs ys) = MAX (MAX_LIST xs) (MAX_LIST ys)`,
  SPEC_TAC(`xs:num list`,`xs:num list`) THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[APPEND; MAX_LIST] THEN ARITH_TAC);;
let _ = cake_add_simps [MAX_LIST_APPEND];;

(*Or should it be MAX x (MAX_LIST xs)*)
let MAX_LIST_SNOC = prove
 (`MAX_LIST (SNOC x xs) = MAX (MAX_LIST xs) x`,
  REWRITE_TAC[SNOC_APPEND; MAX_LIST_APPEND; MAX_LIST] THEN ARITH_TAC);;
let _ = cake_add_simps [MAX_LIST_SNOC];;

let MAX_LIST_intro = prove
 (`!ls. P 0 /\ ALL P ls ==> P (MAX_LIST ls)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[MAX_LIST; ALL] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[MAX] THEN COND_CASES_TAC THEN
  ASM_SIMP_TAC[]);;

let MAX_LIST_max = prove
 (`!ls. ALL (\x. x <= MAX_LIST ls) ls`,
  REWRITE_TAC[GSYM ALL_MEM] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC MAX_LIST_PROPERTY THEN ASM_REWRITE_TAC[]);;

(* HOL4: FOLDR MAX 0 ls *)
let FOLDR_MAX_0_MAX_LIST = prove
 (`!ls. ITLIST MAX ls 0 = MAX_LIST ls`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[ITLIST; MAX_LIST]);;

(* never used *)
let list_inter_def = cake_def
  `list_inter (xs:A list) ys = FILTER (\y. MEM y xs) ys`;;

let max3_def = cake_def
  `max3 (x:num) y z = if x > y then (if z > x then z else x)
                      else (if z > y then z else y)`;;
let _ = cake_add_simps [max3_def];;

let ALOOKUP_SNOC = prove
 (CASE_TERM `!(ls:(K#V) list) p k. ALOOKUP (SNOC p ls) k =
     match ALOOKUP ls k with
       SOME v -> SOME v
     | NONE -> if k = FST p then SOME (SND p) else NONE`,
  LIST_INDUCT_TAC THEN SIMP[ALOOKUP_DEF] THEN
  REPEAT GEN_TAC THEN RW[] THEN FS[]);;

let ALOOKUP_GENLIST = prove
 (`!(f:num->A) n k. ALOOKUP (list_of_seq (\i. (i,f i)) n) k =
     if k < n then SOME (f k) else NONE`,
  GEN_TAC THEN INDUCT_TAC THEN
  ASM_REWRITE_TAC[list_of_seq; ALOOKUP_DEF; LT; GSYM SNOC_APPEND;
                  ALOOKUP_SNOC] THEN
  GEN_TAC THEN ASM_CASES_TAC `k < n` THEN ASM_REWRITE_TAC[option_CASE] THEN
  ASM_CASES_TAC `k:num = n` THEN ASM_REWRITE_TAC[]);;

let ALOOKUP_ZIP_FAIL = prove
 (`!(A:K list) (B:V list) x.
     LENGTH A = LENGTH B ==>
     (ALOOKUP (ZIP A B) x = NONE <=> ~MEM x A)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[ALOOKUP_NONE; MAP_ZIP]);;

let MEM_ALOOKUP = prove
 (`!(xs:(K#V) list) x v.
     ALL_DISTINCT (MAP FST xs) ==>
     (MEM (x,v) xs <=> ALOOKUP xs x = SOME v)`,
  MESON_TAC[ALOOKUP_MEM; ALOOKUP_ALL_DISTINCT_MEM]);;

(* TODO - candidate for move to HOL, but in simpler form without accumulator *)
(* only used in inferProg *)
let anub_def = cake_def_wf
  `MEASURE (\p:(K#V) list # K list. LENGTH (FST p))`
  (REWRITE_TAC[measure_THM; LENGTH] THEN ARITH_TAC)
  `(anub ([]:(K#V) list) (acc:K list) = []) /\
   (anub (CONS (k,v) ls) acc =
      if MEM k acc then anub ls acc else
      CONS (k,v) (anub ls (CONS k acc)))`;;

let anub_ind = cake_ind "anub";;

let EVERY_anub_imp = prove
 (`!(ls:(K#V) list) acc x y.
     ALL P (anub (CONS (x,y) ls) acc) /\ ~(x IN set_of_list acc)
     ==> P (x,y) /\ ALL P (anub ls (CONS x acc))`,
  REWRITE_TAC[IN_SET_OF_LIST] THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[anub_def] THEN COND_CASES_TAC THEN REWRITE_TAC[ALL] THEN
  MESON_TAC[]);;

(* terrible rewrite *)
let ALOOKUP_anub = prove
 (`ALOOKUP (anub (ls:(K#V) list) acc) k =
   if MEM k acc then ALOOKUP (anub ls acc) k
   else ALOOKUP ls k`,
  SUBGOAL_THEN
   `!(ls:(K#V) list) acc k.
      ~MEM k acc ==> ALOOKUP (anub ls acc) k = ALOOKUP ls k`
   (fun th -> COND_CASES_TAC THEN ASM_SIMP_TAC[th]) THEN
  MATCH_MP_TAC anub_ind THEN REWRITE_TAC[anub_def; ALOOKUP_DEF] THEN
  REPEAT STRIP_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[ALOOKUP_DEF] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[MEM]);;

(* HOL4: EVERY (combin$C MEM y) (MAP FST x) *)
let anub_eq_nil = prove
 (`anub (x:(K#V) list) y = [] <=> ALL (flip MEM y) (MAP FST x)`,
  SPEC_TAC(`y:K list`,`y:K list`) THEN
  SPEC_TAC(`x:(K#V) list`,`x:(K#V) list`) THEN
  MATCH_MP_TAC anub_ind THEN REWRITE_TAC[anub_def; MAP; ALL; C_THM] THEN
  REPEAT STRIP_TAC THEN COND_CASES_TAC THEN ASM_SIMP_TAC[NOT_CONS_NIL]);;

let EVERY_anub_suff = prove
 (CASE_TERM `!(ls:(K#V) list) acc.
    (!x. ~MEM x acc ==> match ALOOKUP ls x with SOME v -> P (x,v) | NONE -> T)
    ==> ALL P (anub ls acc)`,
  MATCH_MP_TAC anub_ind THEN REWRITE_TAC[anub_def; ALL; ALOOKUP_DEF] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN DISCH_TAC THEN
  COND_CASES_TAC THEN REWRITE_TAC[ALL] THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o C MP (ASSUME `MEM (k:K) acc`));
    CONJ_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `k:K`) THEN ASM_REWRITE_TAC[option_CASE];
      FIRST_X_ASSUM(MATCH_MP_TAC o C MP (ASSUME `~MEM (k:K) acc`))]] THEN
  X_GEN_TAC `x:K` THEN REWRITE_TAC[MEM; DE_MORGAN_THM] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:K`) THEN ASM_REWRITE_TAC[] THEN
  COND_CASES_TAC THEN ASM_MESON_TAC[]);;

let anub_notin_acc = prove
 (`!(ls:(K#V) list) acc. MEM x acc ==> ~MEM x (MAP FST (anub ls acc))`,
  MATCH_MP_TAC anub_ind THEN REWRITE_TAC[anub_def; MAP; MEM] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN DISCH_TAC THEN
  COND_CASES_TAC THEN ASM_SIMP_TAC[MAP; MEM] THEN ASM_MESON_TAC[MEM]);;

let anub_tl_anub = prove
 (`!(x:(K#V) list) y h t. anub x y = CONS h t ==>
     ?a b. t = anub a b /\ set_of_list a SUBSET set_of_list x /\
           set_of_list b SUBSET set_of_list (CONS (FST h) y)`,
  MATCH_MP_TAC anub_ind THEN REWRITE_TAC[anub_def; NOT_CONS_NIL] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN
  COND_CASES_TAC THEN REWRITE_TAC[CONS_11] THENL
   [DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`h:K#V`; `t:(K#V) list`] o
                  C MP (ASSUME `MEM (k:K) acc`)) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC [`a:(K#V) list`; `b:K list`] THEN
    ASM_REWRITE_TAC[set_of_list] THEN
    UNDISCH_TAC `set_of_list (a:(K#V) list) SUBSET set_of_list ls` THEN
    SET_TAC[];
    STRIP_TAC THEN RVEQ_TAC THEN
    MAP_EVERY EXISTS_TAC [`ls:(K#V) list`; `CONS (k:K) acc`] THEN
    REWRITE_TAC[set_of_list; FST] THEN SET_TAC[]]);;

let anub_all_distinct_keys = prove
 (`!(ls:(K#V) list) acc.
     ALL_DISTINCT acc ==>
     ALL_DISTINCT (APPEND (MAP FST (anub ls acc)) acc)`,
  MATCH_MP_TAC anub_ind THEN REWRITE_TAC[anub_def; MAP; APPEND] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN DISCH_TAC THEN
  COND_CASES_TAC THEN ASM_SIMP_TAC[MAP; APPEND] THEN
  FIRST_X_ASSUM(MP_TAC o C MP (ASSUME `~MEM (k:K) acc`)) THEN
  ASM_REWRITE_TAC[ALL_DISTINCT; ALL_DISTINCT_APPEND; MEM_APPEND; MEM] THEN
  MESON_TAC[]);;

let MEM_anub_ALOOKUP = prove
 (`MEM ((k:K),(v:V)) (anub ls []) ==>
   ALOOKUP ls k = SOME v`,
  DISCH_TAC THEN
  MP_TAC(ISPECL [`ls:(K#V) list`; `[]:K list`] anub_all_distinct_keys) THEN
  REWRITE_TAC[ALL_DISTINCT; APPEND_NIL] THEN DISCH_TAC THEN
  ONCE_REWRITE_TAC[GSYM(REWRITE_RULE[MEM]
    (INST [`[]:K list`,`acc:K list`] ALOOKUP_anub))] THEN
  ASM_MESON_TAC[ALOOKUP_ALL_DISTINCT_MEM]);;

(* HOL4: Type num_set = :unit spt and Type num_map = :'a spt; sptree.ml has *)
(* the abbreviation num_set (:1 spt), num_map is written :A spt.          *)

let toAList_domain = prove
 (`!x. MEM x (MAP FST (toAList (t:A spt))) <=> x IN domain t`,
  REWRITE_TAC[MEM_MAP; EXISTS_PAIR_THM; MEM_toAList; domain_lookup; FST] THEN
  MESON_TAC[]);;

let domain_nat_set_from_list = prove
 (`!ls (ns:1 spt). domain (FOLDL (\s n. insert n one s) ns ls) =
                   domain ns UNION set_of_list ls`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[FOLDL; set_of_list; UNION_EMPTY; domain_insert] THEN
  SET_TAC[]);;
let _ = cake_add_simps [domain_nat_set_from_list];;

let wf_nat_set_from_list = prove
 (`!ls (ns:A spt). sptree_wf ns ==> sptree_wf (FOLDL (\s n. insert n z s) ns ls)`,
  LIST_INDUCT_TAC THEN ASM_SIMP_TAC[FOLDL; wf_insert]);;

(* HOL4 BIT is HOL Light's numbit *)
let BIT_11 = prove
 (`!n m. (numbit n = numbit m) <=> (n = m)`,
  REPEAT GEN_TAC THEN EQ_TAC THEN SIMP_TAC[] THEN
  DISCH_THEN(MP_TAC o C AP_THM `2 EXP n`) THEN
  REWRITE_TAC[numbit; GSYM IN_BITS_OF_NUM; BITS_OF_NUM_POW2; IN_SING] THEN
  MESON_TAC[]);;

let BIT_11_2 = prove
 (`!n m. (!z. (z < 2 EXP (MAX n m)) ==> (numbit n z <=> numbit m z)) <=>
         (n = m)`,
  REPEAT GEN_TAC THEN EQ_TAC THEN SIMP_TAC[] THEN
  REWRITE_TAC[numbit; GSYM IN_BITS_OF_NUM] THEN DISCH_TAC THEN
  ASM_CASES_TAC `n:num = m` THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `2 EXP (MIN n m)`) THEN
  REWRITE_TAC[BITS_OF_NUM_POW2; IN_SING; LT_EXP] THEN
  REWRITE_TAC[MAX; MIN] THEN
  COND_CASES_TAC THEN ASM_ARITH_TAC);;

(* only used below in proof of theorem that is in turn used just twice *)
let LOG2_TIMES2 = prove
 (`0 < n ==> (LOG2 (2 * n) = SUC (LOG2 n))`,
  DISCH_TAC THEN MATCH_MP_TAC LOG2_UNIQUE THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP LOG2_PROPERTY) THEN
  REWRITE_TAC[EXP] THEN ARITH_TAC);;

(* only used below in proof of theorem that is in turn used just twice *)
let LOG2_TIMES2_1 = prove
 (`!n. 0 < n ==> (LOG2 (2 * n + 1) = LOG2 (2 * n))`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[LOG2_TIMES2] THEN
  MATCH_MP_TAC LOG2_UNIQUE THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP LOG2_PROPERTY) THEN
  REWRITE_TAC[EXP] THEN ARITH_TAC);;

(* used only twice, both times in candle/set-theory *)
let C_BIT_11 = prove
 (`!n m. (!z. (z <= LOG2 (MAX n m)) ==> (numbit z n <=> numbit z m)) <=>
         (n = m)`,
  REPEAT GEN_TAC THEN EQ_TAC THEN SIMP_TAC[] THEN DISCH_TAC THEN
  ONCE_REWRITE_TAC[GSYM BITS_OF_NUM_EQ] THEN
  REWRITE_TAC[EXTENSION; IN_BITS_OF_NUM; GSYM numbit] THEN
  X_GEN_TAC `z:num` THEN
  ASM_CASES_TAC `z <= LOG2 (MAX n m)` THEN ASM_SIMP_TAC[] THEN
  ASM_CASES_TAC `MAX n m = 0` THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[MAX_EQ_0]) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPEC `MAX n m` LOG2_PROPERTY) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; STRIP_TAC] THEN
  SUBGOAL_THEN `2 EXP SUC (LOG2 (MAX n m)) <= 2 EXP z` ASSUME_TAC THENL
   [REWRITE_TAC[LE_EXP] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `n < 2 EXP z /\ m < 2 EXP z` STRIP_ASSUME_TAC THENL
   [MP_TAC(ARITH_RULE `n <= MAX n m /\ m <= MAX n m`) THEN ASM_ARITH_TAC;
    ASM_SIMP_TAC[NOT_BIT_GT_TWOEXP]]);;

let BIT_num_from_bin_list_leading = prove
 (`!l x. ALL ((>) 2) l /\ LENGTH l <= x ==> ~numbit x (num_from_bin_list l)`,
  REWRITE_TAC[num_from_bin_list_def; o_THM] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC NOT_BIT_GT_TWOEXP THEN
  MATCH_MP_TAC LTE_TRANS THEN EXISTS_TAC `2 EXP LENGTH (REVERSE (l:num list))` THEN
  SIMP_TAC[l2n_lt; ARITH_RULE `0 < 2`] THEN
  ASM_REWRITE_TAC[LENGTH_REVERSE; LE_EXP] THEN ARITH_TAC);;

(* HOL4 $LEAST P is (minimal) P *)
let least_from_def = cake_def
  `least_from P n =
     if (?x. P x /\ n <= x) then minimal x. P x /\ n <= x else (minimal) P`;;

let LEAST_thm = prove
 (`(minimal) P = least_from P 0`,
  REWRITE_TAC[least_from_def; LE_0; ETA_AX] THEN
  COND_CASES_TAC THEN REWRITE_TAC[]);;

let least_from_thm = prove
 (`least_from P n = if P n then n else least_from P (n + 1)`,
  ASM_CASES_TAC `(P:num->bool) n` THEN ASM_REWRITE_TAC[least_from_def] THENL
   [SUBGOAL_THEN `?x. P x /\ n <= x` (fun th -> REWRITE_TAC[th]) THENL
     [ASM_MESON_TAC[LE_REFL]; ALL_TAC] THEN
    MP_TAC(ISPEC `\x. P x /\ n <= x` MINIMAL) THEN
    REWRITE_TAC[] THEN
    MATCH_MP_TAC(TAUT `a /\ (b ==> c) ==> (a <=> b) ==> c`) THEN
    CONJ_TAC THENL [ASM_MESON_TAC[LE_REFL]; ALL_TAC] THEN
    ABBREV_TAC `m = minimal x. P x /\ n <= x` THEN
    DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC (MP_TAC o SPEC `n:num`)) THEN
    ASM_REWRITE_TAC[LE_REFL] THEN ASM_ARITH_TAC;
    SUBGOAL_THEN `(\x. P x /\ n <= x) = (\x. P x /\ n + 1 <= x)` ASSUME_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN
      ASM_CASES_TAC `x:num = n` THEN ASM_REWRITE_TAC[] THEN
      AP_TERM_TAC THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    FIRST_ASSUM(MP_TAC o C AP_THM `x:num`) THEN
    REWRITE_TAC[] THEN DISCH_TAC THEN ASM_REWRITE_TAC[]]);;

(* HOL4 FUNPOW f n x is ITER n f x *)
let FUNPOW_mono = prove
 (`(!x y. (R1:A->B->bool) x y ==> R2 x y) /\
   (!R1 R2. (!x y. R1 x y ==> R2 x y) ==> !x y. f R1 x y ==> f R2 x y) ==>
   !n x y. ITER n f R1 x y ==> ITER n f R2 x y`,
  STRIP_TAC THEN INDUCT_TAC THEN ASM_REWRITE_TAC[ITER] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

let FUNPOW_SUC_PLUS = prove
 (`!n (a:A). ITER n SUC = (+) n`,
  INDUCT_TAC THEN ASM_REWRITE_TAC[ITER; FUN_EQ_THM; I_THM] THEN ARITH_TAC);;

(* used just once; better as
     transitive R ==> transitive (OPTREL R)
   or that with transitive expanded out *)
let OPTREL_trans = prove
 (`!R (x:A option) y z.
     (!a b c. (x = SOME a) /\ (y = SOME b) /\ (z = SOME c) /\ R a b /\ R b c
              ==> R a c) /\
     OPTREL R x y /\ OPTREL R y z ==> OPTREL R x z`,
  REWRITE_TAC[OPTREL_DEF] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN FS[] THEN ASM_MESON_TAC[]);;

let UPDATE_LIST_def = cake_def
  `UPDATE_LIST = FOLDL (flip (UNCURRY ((=+):A->B->(A->B)->A->B)))`;;

(* HOL4: infix =++ (precedence 500, left), an overload of UPDATE_LIST *)
parse_as_infix("=++",(15,"left"));;
override_interface("=++",`UPDATE_LIST:(A->B)->(A#B)list->A->B`);;

let UPDATE_LIST_THM = prove
 (`!f:A->B. (f =++ [] = f) /\
            !h t. (f =++ (CONS h t) = (FST h =+ SND h) f =++ t)`,
  REWRITE_TAC[UPDATE_LIST_def; FOLDL; C_THM] THEN
  REWRITE_TAC[UNCURRY_DEF; FORALL_PAIR_THM; FST; SND] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[] THEN
  CONV_TAC(ONCE_DEPTH_CONV GEN_BETA_CONV) THEN REWRITE_TAC[]);;

let APPLY_UPDATE_LIST_ALOOKUP = prove
 (CASE_TERM `!(ls:(A#B) list) f x. (f =++ ls) x =
     match ALOOKUP (REVERSE ls) x with NONE -> f x | SOME y -> y`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[UPDATE_LIST_THM; REVERSE; ALOOKUP_APPEND;
                                       ALOOKUP_DEF; option_CASE] THEN
  REPEAT GEN_TAC THEN
  CASES_ON `ALOOKUP (REVERSE (t:(A#B) list)) (x:A)` THEN
  ASM_REWRITE_TAC[option_CASE; APPLY_UPDATE_THM] THEN
  COND_CASES_TAC THEN REWRITE_TAC[option_CASE]);;

(* should be using indexedLists$findi, or INDEX_OF *)
let find_index_def = cake_def
  `(find_index (y:A) [] (n:num) = NONE) /\
   (find_index y (CONS x xs) n =
      if x = y then SOME n else find_index y xs (n + 1))`;;

let INDEX_FIND_CONS_EQ_SOME = prove
 (`(INDEX_FIND n f (CONS (x:A) xs) = SOME y) <=>
   (f x /\ (y = (n,x))) \/
   (~f x /\ (INDEX_FIND (n + 1) f xs = SOME y))`,
  REWRITE_TAC[INDEX_FIND_DEF; ADD1] THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[option_INJ] THEN MESON_TAC[]);;

let find_index_INDEX_FIND = prove
 (`!(y:A) xs n. find_index y xs n = OPTION_MAP FST (INDEX_FIND n ((=) y) xs)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[find_index_def; INDEX_FIND_DEF; OPTION_MAP_DEF; ADD1] THEN
  GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[OPTION_MAP_DEF] THEN
  FIRST_X_ASSUM(MP_TAC o check (is_neg o concl)) THEN
  ASM_MESON_TAC[]);;

let find_index_INDEX_OF = prove
 (`find_index (y:A) xs 0 = INDEX_OF y xs`,
  REWRITE_TAC[INDEX_OF_def; find_index_INDEX_FIND; o_THM]);;

(* HOL4 states ~MEM x ls = (find_index x ls n = NONE) *)
let find_index_NOT_MEM = prove
 (`!ls (x:A) n. ~MEM x ls <=> (find_index x ls n = NONE)`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[find_index_def; MEM] THEN
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[option_DISTINCT] THEN ASM_MESON_TAC[]);;

let find_index_MEM = prove
 (`!ls (x:A) n. MEM x ls ==>
     ?i. (find_index x ls n = SOME (n + i)) /\ i < LENGTH ls /\ (EL i ls = x)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[MEM; find_index_def; LENGTH] THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN COND_CASES_TAC THENL
   [EXISTS_TAC `0` THEN ASM_REWRITE_TAC[EL; HD; ADD_CLAUSES; LT_0];
    SUBGOAL_THEN `MEM (x:A) t` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`x:A`; `n + 1`]) THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN EXISTS_TAC `SUC i` THEN
    ASM_REWRITE_TAC[EL; TL; LT_SUC; option_INJ] THEN ARITH_TAC]);;

let find_index_LEAST_EL = prove
 (`!ls (x:A) n. find_index x ls n =
     if MEM x ls then SOME (n + (minimal n. x = EL n ls)) else NONE`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[find_index_def; MEM] THEN
  REPEAT GEN_TAC THEN COND_CASES_TAC THENL
   [ASM_REWRITE_TAC[option_INJ; ARITH_RULE `n = n + m <=> m = 0`] THEN
    MATCH_MP_TAC MINIMAL_UNIQUE THEN ASM_REWRITE_TAC[EL; HD; LT];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(x:A = h \/ MEM x t) <=> MEM x t` SUBST1_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  COND_CASES_TAC THEN REWRITE_TAC[option_INJ] THEN
  SUBGOAL_THEN `(minimal m. (x:A) = EL m (CONS h t)) =
                SUC (minimal m. x = EL m t)` SUBST1_TAC THENL
   [MATCH_MP_TAC MINIMAL_UNIQUE THEN
    MP_TAC(ISPEC `\m. (x:A) = EL m t` MINIMAL) THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC(TAUT `a /\ (b ==> c) ==> (a <=> b) ==> c`) THEN
    CONJ_TAC THENL [ASM_MESON_TAC[MEM_EXISTS_EL]; ALL_TAC] THEN
    STRIP_TAC THEN REWRITE_TAC[EL; TL] THEN
    CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    INDUCT_TAC THEN REWRITE_TAC[EL; HD; TL; LT_SUC] THENL
     [ASM_MESON_TAC[]; ASM_REWRITE_TAC[]];
    ARITH_TAC]);;

let find_index_LESS_LENGTH = prove
 (`!ls (n:A) m i. (find_index n ls m = SOME i) ==> (m <= i) /\ (i < m + LENGTH ls)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[find_index_def; option_DISTINCT; LENGTH] THEN
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[option_INJ] THENL
   [ARITH_TAC;
    DISCH_THEN(MP_TAC o MATCH_MP (ASSUME
      `!(n:A) m i. find_index n t m = SOME i ==> m <= i /\ i < m + LENGTH t`)) THEN
    ARITH_TAC]);;

let ALOOKUP_find_index_NONE = prove
 (`(ALOOKUP (env:(K#V) list) k = NONE) ==> (find_index k (MAP FST env) m = NONE)`,
  REWRITE_TAC[ALOOKUP_NONE] THEN MESON_TAC[find_index_NOT_MEM]);;

let ALOOKUP_find_index_SOME = prove
 (`(ALOOKUP (env:(K#V) list) k = SOME v) ==>
   ?i. (find_index k (MAP FST env) 0 = SOME i) /\
       i < LENGTH env /\ (v = SND (EL i env))`,
  SUBGOAL_THEN
   `!(env:(K#V) list). (ALOOKUP env k = SOME v) ==>
      !m. ?i. (find_index k (MAP FST env) m = SOME (m + i)) /\
              (v = EL i (MAP SND env))`
   ASSUME_TAC THENL
   [LIST_INDUCT_TAC THEN REWRITE_TAC[ALOOKUP_DEF; option_DISTINCT] THEN
    REWRITE_TAC[MAP; find_index_def] THEN COND_CASES_TAC THEN
    REWRITE_TAC[option_INJ] THENL
     [DISCH_TAC THEN GEN_TAC THEN EXISTS_TAC `0` THEN
      ASM_REWRITE_TAC[ADD_CLAUSES; EL; HD];
      DISCH_TAC THEN GEN_TAC THEN FIRST_X_ASSUM(MP_TAC o C MP (ASSUME
        `ALOOKUP (t:(K#V) list) k = SOME v`)) THEN
      DISCH_THEN(X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC o SPEC `m + 1`) THEN
      EXISTS_TAC `SUC i` THEN ASM_REWRITE_TAC[EL; TL; option_INJ] THEN
      ARITH_TAC];
    ALL_TAC] THEN
  DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `0` o C MATCH_MP (ASSUME
    `ALOOKUP (env:(K#V) list) k = SOME v`)) THEN
  REWRITE_TAC[ADD_CLAUSES] THEN STRIP_TAC THEN
  EXISTS_TAC `i:num` THEN ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP find_index_LESS_LENGTH) THEN
  REWRITE_TAC[LENGTH_MAP; ADD_CLAUSES] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[EL_MAP]);;


let find_index_ALL_DISTINCT_EL = prove
 (`!ls n m. ALL_DISTINCT ls /\ n < LENGTH ls ==>
     (find_index (EL n ls:A) ls m = SOME (m + n))`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[LENGTH; LT_0; ARITH_RULE `~(n < 0)`] THEN
  GEN_TAC THEN CASES_ON `n:num` THEN
  REWRITE_TAC[ALL_DISTINCT; EL; HD; TL; find_index_def; ADD_CLAUSES; LT_SUC;
              NOT_SUC] THEN
  REPEAT STRIP_TAC THEN COND_CASES_TAC THENL
   [ASM_MESON_TAC[MEM_EL]; ALL_TAC] THEN
  ASM_SIMP_TAC[] THEN REWRITE_TAC[option_INJ] THEN ARITH_TAC);;
let _ = cake_add_simps [find_index_ALL_DISTINCT_EL];;

let find_index_ALL_DISTINCT_EL_eq = prove
 (`!ls. ALL_DISTINCT ls ==> !(x:A) m i. (find_index x ls m = SOME i) <=>
     ?j. (i = m + j) /\ j < LENGTH ls /\ (x = EL j ls)`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [DISCH_TAC THEN
    SUBGOAL_THEN `MEM (x:A) ls` ASSUME_TAC THENL
     [ASM_MESON_TAC[find_index_NOT_MEM; option_DISTINCT]; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `m:num` o MATCH_MP find_index_MEM) THEN
    DISCH_THEN(X_CHOOSE_THEN `j:num` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `j:num` THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `find_index (x:A) ls m = SOME i` THEN
    ASM_REWRITE_TAC[option_INJ] THEN MESON_TAC[];
    STRIP_TAC THEN ASM_SIMP_TAC[find_index_ALL_DISTINCT_EL]]);;

let find_index_APPEND_same = prove
 (`!l1 (n:A) m i l2. (find_index n l1 m = SOME i) ==>
     (find_index n (APPEND l1 l2) m = SOME i)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[find_index_def; APPEND; option_DISTINCT] THEN
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN ASM_SIMP_TAC[]);;

(* HOL4 m + LENGTH ls + m - j - 1 is (((m + LENGTH ls) + m) - j) - 1 *)
let find_index_ALL_DISTINCT_REVERSE = prove
 (`!ls (x:A) m j. ALL_DISTINCT ls /\ (find_index x ls m = SOME j) ==>
     (find_index x (REVERSE ls) m = SOME ((((m + LENGTH ls) + m) - j) - 1))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP find_index_ALL_DISTINCT_EL_eq) THEN
  DISCH_THEN(fun th -> FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[th])) THEN
  DISCH_THEN(X_CHOOSE_THEN `z:num` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `ALL_DISTINCT (REVERSE ls:A list)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[ALL_DISTINCT_REVERSE]; ALL_TAC] THEN
  ASM_SIMP_TAC[find_index_ALL_DISTINCT_EL_eq] THEN
  EXISTS_TAC `(LENGTH (ls:A list) - z) - 1` THEN
  ASM_SIMP_TAC[LENGTH_REVERSE; EL_REVERSE; ARITH_RULE
    `z < l ==> (l - z) - 1 < l`] THEN
  CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN ASM_ARITH_TAC);;

let THE_find_index_suff = prove
 (`!P (x:A) ls n. (!m. m < LENGTH ls ==> P (m + n)) /\ MEM x ls ==>
     P (THE (find_index x ls n))`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `n:num` o MATCH_MP find_index_MEM) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[THE_DEF] THEN
  ONCE_REWRITE_TAC[ADD_SYM] THEN ASM_SIMP_TAC[]);;

let find_index_APPEND1 = prove
 (`!l1 (n:A) l2 m i. (find_index n (APPEND l1 l2) m = SOME i) /\
     (i < m + LENGTH l1) ==> (find_index n l1 m = SOME i)`,
  LIST_INDUCT_TAC THEN
  REWRITE_TAC[find_index_def; APPEND; LENGTH; ADD_CLAUSES] THENL
   [REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP find_index_LESS_LENGTH) THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
  STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  EXISTS_TAC `l2:A list` THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

let find_index_APPEND2 = prove
 (`!l1 (n:A) l2 m i. (find_index n (APPEND l1 l2) m = SOME i) /\
     (m + LENGTH l1 <= i) ==> (find_index n l2 (m + LENGTH l1) = SOME i)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[find_index_def; APPEND; LENGTH; ADD_CLAUSES] THENL
   [MESON_TAC[]; ALL_TAC] THEN
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[option_INJ] THENL
   [ARITH_TAC; ALL_TAC] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`n:A`; `l2:A list`; `m + 1`; `i:num`]) THEN
  ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[ARITH_RULE `(m + 1) + l = SUC (m + l)`]);;

let find_index_is_MEM = prove
 (`!(x:A) ls n j. (find_index x ls n = SOME j) ==> MEM x ls`,
  MESON_TAC[find_index_NOT_MEM; option_DISTINCT]);;

let find_index_MAP_inj = prove
 (`!ls (x:A) n (f:A->B). (!y. MEM y ls ==> (f x = f y) ==> x = y) ==>
     (find_index (f x) (MAP f ls) n = find_index x ls n)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[find_index_def; MAP; MEM] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `((f:A->B) h = f x) <=> (h = x)` SUBST1_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  COND_CASES_TAC THEN REWRITE_TAC[] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[]);;

let find_index_shift_0 = prove
 (`!ls (x:A) k. find_index x ls k = OPTION_MAP (\x. x + k) (find_index x ls 0)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[find_index_def; OPTION_MAP_DEF] THEN
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN
  REWRITE_TAC[OPTION_MAP_DEF; ADD_CLAUSES] THEN
  ONCE_ASM_REWRITE_TAC[] THEN
  CASES_ON `find_index (x:A) t 0` THEN
  REWRITE_TAC[OPTION_MAP_DEF; option_INJ] THEN ARITH_TAC);;

let find_index_shift = prove
 (`!ls (x:A) k j. (find_index x ls k = SOME j) ==>
     j >= k /\ !n. find_index x ls n = SOME ((j - k) + n)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[find_index_def; option_DISTINCT] THEN
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[option_INJ] THENL
   [DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[SUB_REFL; ADD_CLAUSES] THEN
    ARITH_TAC;
    DISCH_THEN(MP_TAC o MATCH_MP (ASSUME `!(x:A) k j. find_index x t k = SOME j
      ==> j >= k /\ (!n. find_index x t n = SOME ((j - k) + n))`)) THEN
    STRIP_TAC THEN CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    GEN_TAC THEN ASM_REWRITE_TAC[option_INJ] THEN ASM_ARITH_TAC]);;

let find_index_APPEND = prove
 (CASE_TERM `!l1 l2 (x:A) n. find_index x (APPEND l1 l2) n =
    match find_index x l1 n with
      NONE -> find_index x l2 (n + LENGTH l1)
    | SOME x -> SOME x`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[find_index_def; APPEND; LENGTH; option_CASE;
                                   ADD_CLAUSES] THEN
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[option_CASE] THEN
  REWRITE_TAC[ARITH_RULE `(n + 1) + l = SUC (n + l)`]);;

let find_index_in_FILTER_ZIP_EQ = prove
 (`!P (l1:A list) (l2:(A#B) list) x n1 n2 (v1:B list) j1 j2.
     (LENGTH l1 = LENGTH v1) /\
     (FILTER (P o FST) (ZIP l1 v1) = l2) /\
     (find_index x l1 n1 = SOME (n1 + j1)) /\
     (find_index x (MAP FST l2) n2 = SOME (n2 + j2)) /\
     P x
     ==>
     j1 < LENGTH l1 /\ j2 < LENGTH l2 /\
     (EL j1 (ZIP l1 v1) = EL j2 l2)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[find_index_def; option_DISTINCT] THEN
  REPEAT GEN_TAC THEN CASES_ON `v1:B list` THEN
  REWRITE_TAC[LENGTH; NOT_SUC; SUC_INJ; ZIP_def; FILTER; o_THM] THEN
  COND_CASES_TAC THEN REWRITE_TAC[option_INJ] THEN
  STRIP_TAC THEN RVEQ_TAC THEN ASM_CASES_TAC `h:A = x` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[MAP; find_index_def; option_INJ;
                                ARITH_RULE `n = n + m <=> m = 0`]) THEN
    ASM_REWRITE_TAC[EL; HD; LENGTH; LT_0];
    RULE_ASSUM_TAC(REWRITE_RULE[MAP; find_index_def; ASSUME `~(h:A = x)`]) THEN
    MP_TAC(ISPECL [`t:A list`; `x:A`; `n1 + 1`; `n1 + j1`]
      find_index_LESS_LENGTH) THEN
    MP_TAC(ISPECL [`MAP FST (FILTER (P o FST) (ZIP (t:A list) (a1:B list)))`;
                   `x:A`; `n2 + 1`; `n2 + j2`] find_index_LESS_LENGTH) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN STRIP_ASSUME_TAC THEN DISCH_THEN STRIP_ASSUME_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL
      [`FILTER (P o FST) (ZIP (t:A list) (a1:B list))`; `x:A`; `n1 + 1`;
       `n2 + 1`; `a1:B list`; `j1 - 1`; `j2 - 1`]) THEN
    SUBGOAL_THEN
      `(n1 + 1) + (j1 - 1) = n1 + j1 /\ (n2 + 1) + (j2 - 1) = n2 + j2`
      (fun th -> ASM_REWRITE_TAC[th]) THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `j1 = SUC (j1 - 1) /\ j2 = SUC (j2 - 1)` MP_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(CONJUNCTS_THEN (fun th -> ONCE_REWRITE_TAC[th])) THEN
    REWRITE_TAC[EL; TL; LENGTH; LT_SUC] THEN
    REWRITE_TAC[ARITH_RULE `SUC n - 1 = n`];
    ASM_MESON_TAC[];
    RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `~(h:A = x)`]) THEN
    MP_TAC(ISPECL [`t:A list`; `x:A`; `n1 + 1`; `n1 + j1`]
      find_index_LESS_LENGTH) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN STRIP_ASSUME_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL
      [`FILTER (P o FST) (ZIP (t:A list) (a1:B list))`; `x:A`; `n1 + 1`;
       `n2:num`; `a1:B list`; `j1 - 1`; `j2:num`]) THEN
    SUBGOAL_THEN `(n1 + 1) + (j1 - 1) = n1 + j1`
      (fun th -> ASM_REWRITE_TAC[th]) THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `j1 = SUC (j1 - 1)` (fun th -> ONCE_REWRITE_TAC[th]) THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[EL; TL; LENGTH; LT_SUC] THEN
    REWRITE_TAC[ARITH_RULE `SUC n - 1 = n`]]);;

let ALL_DISTINCT_PERM_ALOOKUP_ZIP = prove
 (`!(l1:(K#V) list) l2 l3. ALL_DISTINCT (MAP FST l1) /\ PERM (MAP FST l1) l2
     ==> (set_of_list l1 =
          set_of_list (ZIP l2 (MAP (THE o ALOOKUP (APPEND l1 l3)) l2)))`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[EXTENSION; FORALL_PAIR_THM; IN_SET_OF_LIST] THEN
  ASM_SIMP_TAC[MEM_ZIP; LENGTH_MAP] THEN
  MAP_EVERY X_GEN_TAC [`x:K`; `y:V`] THEN
  SUBGOAL_THEN `!z:K. MEM z l2 <=> MEM z (MAP FST (l1:(K#V) list))`
    ASSUME_TAC THENL [ASM_MESON_TAC[MEM_PERM]; ALL_TAC] THEN
  SUBGOAL_THEN `!z:K. MEM z (MAP FST (l1:(K#V) list)) ==>
                  ALOOKUP (APPEND l1 l3) z = ALOOKUP l1 z`
    ASSUME_TAC THENL
   [REWRITE_TAC[ALOOKUP_APPEND] THEN REPEAT STRIP_TAC THEN
    CASES_ON `ALOOKUP (l1:(K#V) list) z` THEN REWRITE_TAC[option_CASE] THEN
    ASM_MESON_TAC[ALOOKUP_NONE];
    ALL_TAC] THEN
  EQ_TAC THENL
   [DISCH_TAC THEN
    SUBGOAL_THEN `MEM (x:K) l2` MP_TAC THENL
     [ASM_REWRITE_TAC[MEM_MAP; EXISTS_PAIR_THM; FST] THEN
      MAP_EVERY EXISTS_TAC [`x:K`; `y:V`] THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[MEM_EXISTS_EL] THEN MATCH_MP_TAC MONO_EXISTS THEN
    X_GEN_TAC `m:num` THEN STRIP_TAC THEN ASM_SIMP_TAC[EL_MAP; o_THM] THEN
    UNDISCH_TAC `x:K = EL m l2` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    SUBGOAL_THEN `MEM (x:K) (MAP FST (l1:(K#V) list))` ASSUME_TAC THENL
     [REWRITE_TAC[MEM_MAP; EXISTS_PAIR_THM; FST] THEN
      MAP_EVERY EXISTS_TAC [`x:K`; `y:V`] THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_SIMP_TAC[] THEN
    SUBGOAL_THEN `ALOOKUP (l1:(K#V) list) x = SOME y` SUBST1_TAC THENL
     [MATCH_MP_TAC ALOOKUP_ALL_DISTINCT_MEM THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[THE_DEF]];
    DISCH_THEN(X_CHOOSE_THEN `n:num` STRIP_ASSUME_TAC) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[PAIR_EQ]) THEN
    FIRST_X_ASSUM(CONJUNCTS_THEN SUBST_ALL_TAC) THEN
    ASM_SIMP_TAC[EL_MAP; o_THM] THEN
    SUBGOAL_THEN `MEM (EL n l2:K) (MAP FST (l1:(K#V) list))` MP_TAC THENL
     [REWRITE_TAC[GSYM(ASSUME
        `!z:K. MEM z l2 <=> MEM z (MAP FST (l1:(K#V) list))`)] THEN
      MATCH_MP_TAC MEM_EL THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(fun th -> ASSUME_TAC th THEN MP_TAC th) THEN
    REWRITE_TAC[MEM_MAP; EXISTS_PAIR_THM; FST] THEN
    DISCH_THEN(X_CHOOSE_THEN `a:K` (X_CHOOSE_THEN `w:V` STRIP_ASSUME_TAC)) THEN
    ASM_SIMP_TAC[] THEN
    SUBGOAL_THEN `ALOOKUP (l1:(K#V) list) a = SOME w` SUBST1_TAC THENL
     [MATCH_MP_TAC ALOOKUP_ALL_DISTINCT_MEM THEN ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[THE_DEF]]]);;

(* surely better with UNZIP rather than ZIP: i.e., UNZIP l1 = (a,b)...  *)
let PERM_ZIP = prove
 (`!(l1:(A#B) list) l2. PERM l1 l2 ==>
     !a b c d. (l1 = ZIP a b) /\ (l2 = ZIP c d) /\ (LENGTH a = LENGTH b) /\
               (LENGTH c = LENGTH d) ==>
               PERM a c /\ PERM b d`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `a:A list = MAP FST (l1:(A#B) list) /\ b:B list = MAP SND l1 /\
                c:A list = MAP FST (l2:(A#B) list) /\ d:B list = MAP SND l2`
    (fun th -> REWRITE_TAC[th]) THENL
   [ASM_SIMP_TAC[MAP_ZIP]; ASM_SIMP_TAC[PERM_MAP]]);;

(* never used *)
let RTC_invariant = prove
 (`!(R:A->A->bool) P. (!x y. P x /\ R x y ==> P y) ==>
     !x y. RTC R x y ==> P x ==> RTC (R RINTER (\x y. P x /\ P y)) x y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC RTC_INDUCT_R THEN REWRITE_TAC[RTC_REFL] THEN
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[RTC_CASES_R] THEN DISJ2_TAC THEN
  EXISTS_TAC `y:A` THEN REWRITE_TAC[RINTER] THEN ASM_MESON_TAC[]);;

(* never used *)
let RTC_RSUBSET = prove
 (`!(R1:A->A->bool) R2. RSUBSET R1 R2 ==> RSUBSET (RTC R1) (RTC R2)`,
  REWRITE_TAC[RSUBSET_DEF] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC RTC_INDUCT_R THEN REWRITE_TAC[RTC_REFL] THEN
  ASM_MESON_TAC[RTC_CASES_R]);;

let PERM_PART = prove
 (`!P (L:A list) l1 l2 p q. ((p,q) = PART P L l1 l2) ==>
     PERM (APPEND L (APPEND l1 l2)) (APPEND p q)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[PART_DEF; PAIR_EQ; APPEND] THENL
   [REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[PERM_REFL]; ALL_TAC] THEN
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN DISCH_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPECL [`CONS (h:A) l1`; `l2:A list`;
                                  `p:A list`; `q:A list`]);
    FIRST_X_ASSUM(MP_TAC o SPECL [`l1:A list`; `CONS (h:A) l2`;
                                  `p:A list`; `q:A list`])] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] PERM_TRANS) THEN
  REWRITE_TAC[APPEND] THEN
  REWRITE_TAC[GSYM APPEND_ASSOC; APPEND] THEN
  MESON_TAC[CONS_PERM; PERM_REFL; PERM_SYM; APPEND_ASSOC]);;

let misc_PERM_PARTITION = prove
 (`!P (L:A list) A B. ((A,B) = PARTITION P L) ==> PERM L (APPEND A B)`,
  MESON_TAC[PERM_PART; PARTITION_DEF; APPEND_NIL]);;

let option_case_NONE_F = prove
 (CASE_TERM `(match (X:A option) with NONE -> F | SOME x -> P x) <=>
             (?x. (X = SOME x) /\ P x)`,
  CASES_ON `X:A option` THEN REWRITE_TAC[option_CASE; option_DISTINCT;
                                         option_INJ] THEN
  MESON_TAC[]);;

let IS_PREFIX_THM = prove
 (`!(l2:A list) l1. IS_PREFIX l1 l2 <=>
     (LENGTH l2 <= LENGTH l1) /\ !n. n < LENGTH l2 ==> (EL n l2 = EL n l1)`,
  REWRITE_TAC[IS_PREFIX_DEF] THEN
  LIST_INDUCT_TAC THEN REWRITE_TAC[isPREFIX_THM; LENGTH; LE_0; LT_0;
                                   ARITH_RULE `~(n < 0)`] THEN
  GEN_TAC THEN CASES_ON `l1:A list` THEN
  ASM_REWRITE_TAC[isPREFIX_THM; LENGTH; LE_SUC;
                  ARITH_RULE `~(SUC n <= 0)`] THEN
  EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
   [INDUCT_TAC THEN ASM_SIMP_TAC[EL; HD; TL; LT_SUC];
    CONJ_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `0`) THEN REWRITE_TAC[EL; HD; LT_0];
      REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `SUC n`) THEN
      ASM_REWRITE_TAC[EL; TL; LT_SUC]]]);;

let EVERY2_RC_same = prove
 (`ALL2 (RC (R:A->A->bool)) l l`,
  MATCH_MP_TAC EVERY2_refl THEN REWRITE_TAC[RC_DEF]);;
let _ = cake_add_simps [EVERY2_RC_same];;

(* ========================================================================= *)
(* alist: port of HOL4 src/finite_maps/alistScript.sml.                      *)
(* Association lists: ALOOKUP (defined in hol4/vocab.ml), the translations   *)
(* between association lists and finite maps, AFUPDKEY and ADELKEY.         *)
(* HOL4's type abbreviation (A,B)alist is written (A#B)list.                *)
(* ========================================================================= *)

needs "hol4/vocab.ml";;
needs "hol4/finite_map.ml";;

type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Local list lemmas (they belong to the list theory).                       *)
(* ------------------------------------------------------------------------- *)

let FMAPAUX_ALL_DISTINCT_PAIRWISE = prove
 (`!l:A list. ALL_DISTINCT l <=> PAIRWISE (\x y. ~(x = y)) l`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[ALL_DISTINCT; PAIRWISE] THEN
  REWRITE_TAC[GSYM ALL_MEM] THEN MESON_TAC[]);;

let FMAPAUX_ALL_DISTINCT_LIST_OF_SET = prove
 (`!s:A->bool. FINITE s ==> ALL_DISTINCT (list_of_set s)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[FMAPAUX_ALL_DISTINCT_PAIRWISE; GSYM HAS_SIZE_SET_OF_LIST] THEN
  ASM_SIMP_TAC[SET_OF_LIST_OF_SET; LENGTH_LIST_OF_SET; HAS_SIZE]);;

let FMAPAUX_MAP_FST_PAIR = prove
 (`!(f:A->B) l. MAP FST (MAP (\k. (k, f k)) l) = l`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[MAP]);;

(* ------------------------------------------------------------------------- *)
(* Finite maps to association lists and back.                                *)
(* HOL4 SET_TO_LIST is list_of_set (some duplicate-free enumeration).         *)
(* ------------------------------------------------------------------------- *)

let fmap_to_alist_def = new_definition
  `fmap_to_alist (s:(A,B)fmap) = MAP (\k. (k, FAPPLY s k)) (list_of_set (FDOM s))`;;

let fmap_to_alist_FEMPTY = prove
 (`fmap_to_alist (FEMPTY:(A,B)fmap) = []`,
  REWRITE_TAC[fmap_to_alist_def; FDOM_FEMPTY; LIST_OF_SET_EMPTY; MAP]);;

let alist_to_fmap_def = new_definition
  `alist_to_fmap (s:(A#B)list) = ITLIST (\(k,v) f. f |+ (k,v)) s FEMPTY`;;

let alist_to_fmap_thm = prove
 (`(alist_to_fmap ([]:(A#B)list) = FEMPTY) /\
   (!(k:A) (v:B) t. alist_to_fmap (CONS (k,v) t) = alist_to_fmap t |+ (k,v))`,
  REWRITE_TAC[alist_to_fmap_def; ITLIST]);;

let ALOOKUP_def = ALOOKUP_THM;;

let ALOOKUP_FAILS = prove
 (`!(l:(A#B)list) x. (ALOOKUP l x = NONE) <=> !k v. MEM (k,v) l ==> ~(k = x)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[ALOOKUP_THM; MEM] THEN
  SPEC_TAC(`h:A#B`,`h:A#B`) THEN REWRITE_TAC[FORALL_PAIR_THM; ALOOKUP_THM] THEN
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[option_DISTINCT; PAIR_EQ] THEN ASM_MESON_TAC[]);;

let ALOOKUP_NONE = prove
 (`!(l:(A#B)list) x. (ALOOKUP l x = NONE) <=> ~MEM x (MAP FST l)`,
  REWRITE_TAC[ALOOKUP_FAILS; MEM_MAP; EXISTS_PAIR_THM] THEN MESON_TAC[]);;

let ALOOKUP_TABULATE = prove
 (`!(x:A) l (f:A->B). MEM x l ==> (ALOOKUP (MAP (\k. (k, f k)) l) x = SOME (f x))`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[MEM; MAP; ALOOKUP_THM] THEN
  GEN_TAC THEN COND_CASES_TAC THEN ASM_SIMP_TAC[] THEN ASM_MESON_TAC[]);;

let ALOOKUP_EQ_FLOOKUP = prove
 (`(!al:(A#B)list. FLOOKUP (alist_to_fmap al) = ALOOKUP al) /\
   (!fm:(A,B)fmap. ALOOKUP (fmap_to_alist fm) = FLOOKUP fm)`,
  CONJ_TAC THENL
   [LIST_INDUCT_TAC THEN REWRITE_TAC[alist_to_fmap_thm; FUN_EQ_THM] THENL
     [REWRITE_TAC[FLOOKUP_EMPTY; ALOOKUP_THM]; ALL_TAC] THEN
    SPEC_TAC(`h:A#B`,`h:A#B`) THEN
    ASM_REWRITE_TAC[FORALL_PAIR_THM; alist_to_fmap_thm; FLOOKUP_UPDATE;
                    ALOOKUP_THM];
    GEN_TAC THEN REWRITE_TAC[FUN_EQ_THM; fmap_to_alist_def] THEN X_GEN_TAC `x:A` THEN
    REWRITE_TAC[FLOOKUP_DEF] THEN COND_CASES_TAC THENL
     [MATCH_MP_TAC ALOOKUP_TABULATE THEN ASM_SIMP_TAC[MEM_LIST_OF_SET; FDOM_FINITE];
      ASM_SIMP_TAC[ALOOKUP_NONE; FMAPAUX_MAP_FST_PAIR; MEM_LIST_OF_SET;
                   FDOM_FINITE]]]);;

let MEM_fmap_to_alist = prove
 (`!(x:A) (y:B) fm.
     MEM (x,y) (fmap_to_alist fm) <=> x IN FDOM fm /\ (FAPPLY fm x = y)`,
  SIMP_TAC[fmap_to_alist_def; MEM_MAP; MEM_LIST_OF_SET; FDOM_FINITE; PAIR_EQ] THEN
  MESON_TAC[]);;

let MEM_fmap_to_alist_FLOOKUP = prove
 (`!(p:A#B) fm. MEM p (fmap_to_alist fm) <=> (FLOOKUP fm (FST p) = SOME (SND p))`,
  REWRITE_TAC[FORALL_PAIR_THM; MEM_fmap_to_alist; flookup_thm]);;

let MEM_pair_fmap_to_alist_FLOOKUP = prove
 (`!(x:A) (y:B) fm. MEM (x,y) (fmap_to_alist fm) <=> (FLOOKUP fm x = SOME y)`,
  REWRITE_TAC[MEM_fmap_to_alist; flookup_thm]);;

let LENGTH_fmap_to_alist = prove
 (`!fm:(A,B)fmap. LENGTH (fmap_to_alist fm) = CARD (FDOM fm)`,
  SIMP_TAC[fmap_to_alist_def; LENGTH_MAP; LENGTH_LIST_OF_SET; FDOM_FINITE]);;

let fmap_to_alist_to_fmap = prove
 (`!fm:(A,B)fmap. alist_to_fmap (fmap_to_alist fm) = fm`,
  REWRITE_TAC[FLOOKUP_EXT; ALOOKUP_EQ_FLOOKUP]);;

let ALOOKUP_MEM = prove
 (`!(al:(A#B)list) k v. (ALOOKUP al k = SOME v) ==> MEM (k,v) al`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[ALOOKUP_THM; MEM; option_DISTINCT] THEN
  SPEC_TAC(`h:A#B`,`h:A#B`) THEN REWRITE_TAC[FORALL_PAIR_THM; ALOOKUP_THM] THEN
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN
  ASM_SIMP_TAC[option_INJ; PAIR_EQ]);;

let ALOOKUP_SOME_FAPPLY_alist_to_fmap = prove
 (`!(al:(A#B)list) k v. (ALOOKUP al k = SOME v) ==> (FAPPLY (alist_to_fmap al) k = v)`,
  SIMP_TAC[FAPPLY_FLOOKUP; ALOOKUP_EQ_FLOOKUP; THE_DEF]);;

let alist_to_fmap_FAPPLY_MEM = prove
 (`!(al:(A#B)list) z.
     z IN FDOM (alist_to_fmap al) ==> MEM (z, FAPPLY (alist_to_fmap al) z) al`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC ALOOKUP_MEM THEN
  REWRITE_TAC[GSYM(CONJUNCT1 ALOOKUP_EQ_FLOOKUP)] THEN
  ASM_REWRITE_TAC[flookup_thm]);;

let ALOOKUP_MAP = prove
 (`!(f:B->C) (al:(A#B)list).
     ALOOKUP (MAP (\(x,y). (x, f y)) al) = OPTION_MAP f o (ALOOKUP al)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; MAP; ALOOKUP_THM; o_THM; OPTION_MAP_DEF] THEN
  SPEC_TAC(`h:A#B`,`h:A#B`) THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
  POP_ASSUM(MP_TAC o REWRITE_RULE[FUN_EQ_THM; o_THM]) THEN
  SIMP_TAC[ALOOKUP_THM] THEN REPEAT STRIP_TAC THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[OPTION_MAP_DEF]);;

let ALOOKUP_MAP_2 = prove
 (`!(f:A->B->C) (al:(A#B)list) x.
     ALOOKUP (MAP (\(x,y). (x, f x y)) al) x = OPTION_MAP (f x) (ALOOKUP al x)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[MAP; ALOOKUP_THM; OPTION_MAP_DEF] THEN
  SPEC_TAC(`h:A#B`,`h:A#B`) THEN REWRITE_TAC[FORALL_PAIR_THM; ALOOKUP_THM] THEN
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[OPTION_MAP_DEF]);;

let FDOM_alist_to_fmap = prove
 (`!al:(A#B)list. FDOM (alist_to_fmap al) = set_of_list (MAP FST al)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[alist_to_fmap_thm; FDOM_FEMPTY; MAP; set_of_list] THEN
  SPEC_TAC(`h:A#B`,`h:A#B`) THEN
  ASM_REWRITE_TAC[FORALL_PAIR_THM; alist_to_fmap_thm; FDOM_FUPDATE]);;

let alist_to_fmap_APPEND = prove
 (`!(l1:(A#B)list) l2.
     alist_to_fmap (APPEND l1 l2) = FUNION (alist_to_fmap l1) (alist_to_fmap l2)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[APPEND; alist_to_fmap_thm; FUNION_FEMPTY_1] THEN
  SPEC_TAC(`h:A#B`,`h:A#B`) THEN
  ASM_REWRITE_TAC[FORALL_PAIR_THM; alist_to_fmap_thm; FUNION_FUPDATE_1]);;

let alist_to_fmap_prefix = prove
 (`!(ls:(A#B)list) l1 l2.
     (alist_to_fmap l1 = alist_to_fmap l2) ==>
     (alist_to_fmap (APPEND ls l1) = alist_to_fmap (APPEND ls l2))`,
  SIMP_TAC[alist_to_fmap_APPEND]);;

let ALOOKUP_APPEND = prove
 (`!(l1:(A#B)list) l2 k.
     ALOOKUP (APPEND l1 l2) k =
     option_CASE (ALOOKUP l1 k) (ALOOKUP l2 k) (\v. SOME v)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[APPEND; ALOOKUP_THM; option_CASE] THEN
  SPEC_TAC(`h:A#B`,`h:A#B`) THEN REWRITE_TAC[FORALL_PAIR_THM; ALOOKUP_THM] THEN
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[option_CASE]);;

let ALOOKUP_prefix = prove
 (`!(ls:(A#B)list) k ls2 v.
     ((ALOOKUP ls k = SOME v) ==> (ALOOKUP (APPEND ls ls2) k = SOME v)) /\
     ((ALOOKUP ls k = NONE) ==> (ALOOKUP (APPEND ls ls2) k = ALOOKUP ls2 k))`,
  SIMP_TAC[ALOOKUP_APPEND; option_CASE]);;

(* HOL4 proves flookup_fupdate_list near the end of the script; the port   *)
(* proves it here and derives the other FUPDATE_LIST lemmas from it.        *)

let flookup_fupdate_list = prove
 (`!(l:(A#B)list) k m.
     FLOOKUP (m |++ l) k =
     option_CASE (ALOOKUP (REVERSE l) k) (FLOOKUP m k) (\v. SOME v)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[FUPDATE_LIST_THM; REVERSE; ALOOKUP_THM; option_CASE] THEN
  SPEC_TAC(`h:A#B`,`h:A#B`) THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`a:A`; `b:B`; `k:A`; `m:(A,B)fmap`] THEN
  ASM_REWRITE_TAC[ALOOKUP_APPEND; ALOOKUP_THM; FLOOKUP_UPDATE] THEN
  STRUCT_CASES_TAC(ISPEC `ALOOKUP (REVERSE (t:(A#B)list)) k` (cases "option")) THEN
  REWRITE_TAC[option_CASE] THEN COND_CASES_TAC THEN REWRITE_TAC[option_CASE]);;

let FUPDATE_LIST_EQ_APPEND_REVERSE = prove
 (`!(ls:(A#B)list) fm.
     fm |++ ls = alist_to_fmap (APPEND (REVERSE ls) (fmap_to_alist fm))`,
  REWRITE_TAC[FLOOKUP_EXT; FUN_EQ_THM; flookup_fupdate_list; ALOOKUP_EQ_FLOOKUP;
              ALOOKUP_APPEND]);;

let FLOOKUP_FUPDATE_LIST_ALOOKUP_SOME = prove
 (`!(ls:(A#B)list) k v fm.
     (ALOOKUP ls k = SOME v) ==> (FLOOKUP (fm |++ (REVERSE ls)) k = SOME v)`,
  SIMP_TAC[flookup_fupdate_list; REVERSE_REVERSE; option_CASE]);;

let FLOOKUP_FUPDATE_LIST_ALOOKUP_NONE = prove
 (`!(ls:(A#B)list) k fm.
     (ALOOKUP ls k = NONE) ==> (FLOOKUP (fm |++ (REVERSE ls)) k = FLOOKUP fm k)`,
  SIMP_TAC[flookup_fupdate_list; REVERSE_REVERSE; option_CASE]);;

let FUNION_alist_to_fmap = prove
 (`!(ls:(A#B)list) fm. FUNION (alist_to_fmap ls) fm = fm |++ (REVERSE ls)`,
  REWRITE_TAC[FLOOKUP_EXT; FUN_EQ_THM; flookup_fupdate_list; REVERSE_REVERSE;
              FLOOKUP_FUNION; ALOOKUP_EQ_FLOOKUP]);;

let alist_to_fmap_MAP = prove
 (`!(f1:A->C) (f2:B->D) al.
     INJ f1 (set_of_list (MAP FST al)) UNIV ==>
     (alist_to_fmap (MAP (\(x,y). (f1 x, f2 y)) al) =
      MAP_KEYS f1 (f2 o_f alist_to_fmap al))`,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[MAP; alist_to_fmap_thm; o_f_FEMPTY; MAP_KEYS_FEMPTY] THEN
  SPEC_TAC(`h:A#B`,`h:A#B`) THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`a:A`; `b:B`] THEN
  REWRITE_TAC[MAP; set_of_list; alist_to_fmap_thm; o_f_FUPDATE] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `INJ (f1:A->C) (set_of_list (MAP FST (t:(A#B)list))) UNIV`
   (fun th -> FIRST_X_ASSUM(SUBST1_TAC o C MATCH_MP th)) THENL
   [UNDISCH_TAC `INJ (f1:A->C) (a INSERT set_of_list (MAP FST (t:(A#B)list))) UNIV` THEN
    REWRITE_TAC[INJ; IN_INSERT; IN_UNIV] THEN MESON_TAC[];
    ALL_TAC] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC MAP_KEYS_FUPDATE THEN
  ASM_REWRITE_TAC[FDOM_o_f; FDOM_alist_to_fmap]);;

let alist_to_fmap_to_alist = prove
 (`!al:(A#B)list.
     fmap_to_alist (alist_to_fmap al) =
     MAP (\k. (k, THE (ALOOKUP al k))) (list_of_set (set_of_list (MAP FST al)))`,
  REWRITE_TAC[fmap_to_alist_def; FDOM_alist_to_fmap; FAPPLY_FLOOKUP;
              ALOOKUP_EQ_FLOOKUP]);;

let FMAPAUX_MINIMAL_0 = prove
 (`!P. P 0 ==> (minimal) P = 0`,
  GEN_TAC THEN DISCH_TAC THEN MP_TAC(SPEC `P:num->bool` MINIMAL) THEN
  SUBGOAL_THEN `?n. (P:num->bool) n` (fun th -> REWRITE_TAC[th]) THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  STRIP_TAC THEN ASM_MESON_TAC[ARITH_RULE `~(m = 0) ==> 0 < m`]);;

let FMAPAUX_MINIMAL_SUC = prove
 (`!P. ~P 0 /\ (?n. P n) ==> (minimal) P = SUC ((minimal) (\n. P (SUC n)))`,
  GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `?n. (P:num->bool) (SUC n)` ASSUME_TAC THENL
   [ASM_MESON_TAC[num_CASES]; ALL_TAC] THEN
  MP_TAC(SPEC `P:num->bool` MINIMAL) THEN
  MP_TAC(SPEC `\n. (P:num->bool) (SUC n)` MINIMAL) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `a = (minimal) (P:num->bool)` THEN
  ABBREV_TAC `b = (minimal) (\n. (P:num->bool) (SUC n))` THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(a = 0)` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `a = SUC (PRE a)` SUBST_ALL_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[SUC_INJ] THEN
  SUBGOAL_THEN `~(PRE a < b) /\ ~(b < PRE a)` MP_TAC THENL
   [ASM_MESON_TAC[LT_SUC]; ARITH_TAC]);;

let ALOOKUP_LEAST_EL = prove
 (`!(ls:(A#B)list) k.
     ALOOKUP ls k =
     if MEM k (MAP FST ls)
     then SOME (EL (minimal n. EL n (MAP FST ls) = k) (MAP SND ls))
     else NONE`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[ALOOKUP_THM; MAP; MEM] THEN
  SPEC_TAC(`h:A#B`,`h:A#B`) THEN REWRITE_TAC[FORALL_PAIR_THM; ALOOKUP_THM] THEN
  MAP_EVERY X_GEN_TAC [`a:A`; `b:B`; `k:A`] THEN ASM_CASES_TAC `a:A = k` THENL
   [ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(minimal n. EL n (CONS (k:A) (MAP FST (t:(A#B)list))) = k) = 0`
     SUBST1_TAC THENL
     [MATCH_MP_TAC FMAPAUX_MINIMAL_0 THEN REWRITE_TAC[EL; HD];
      REWRITE_TAC[EL; HD]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(k:A = a) <=> F` SUBST1_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `(minimal n. EL n (CONS (a:A) (MAP FST (t:(A#B)list))) = k) =
    SUC (minimal n. EL n (MAP FST t) = k)` SUBST1_TAC THENL
   [MP_TAC(SPEC `\n. EL n (CONS (a:A) (MAP FST (t:(A#B)list))) = k` FMAPAUX_MINIMAL_SUC) THEN
    REWRITE_TAC[EL; HD; TL] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `MEM (k:A) (MAP FST (t:(A#B)list))` THEN
    REWRITE_TAC[MEM_EXISTS_EL] THEN
    STRIP_TAC THEN EXISTS_TAC `SUC i` THEN ASM_REWRITE_TAC[EL; TL];
    REWRITE_TAC[EL; TL]]);;

let ALOOKUP_ALL_DISTINCT_MEM = prove
 (`!(al:(A#B)list) k v.
     ALL_DISTINCT (MAP FST al) /\ MEM (k,v) al ==> (ALOOKUP al k = SOME v)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[MEM; MAP; ALL_DISTINCT] THEN
  SPEC_TAC(`h:A#B`,`h:A#B`) THEN REWRITE_TAC[FORALL_PAIR_THM; ALOOKUP_THM] THEN
  MAP_EVERY X_GEN_TAC [`a:A`; `b:B`; `k:A`; `v:B`] THEN
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THENL
   [ASM_REWRITE_TAC[];
    SUBGOAL_THEN `~(a:A = k)` (fun th -> REWRITE_TAC[th]) THENL
     [UNDISCH_TAC `~MEM (a:A) (MAP FST (t:(A#B)list))` THEN
      REWRITE_TAC[MEM_MAP; EXISTS_PAIR_THM] THEN ASM_MESON_TAC[];
      ASM_MESON_TAC[]]]);;

let ALL_DISTINCT_fmap_to_alist_keys = prove
 (`!fm:(A,B)fmap. ALL_DISTINCT (MAP FST (fmap_to_alist fm))`,
  SIMP_TAC[fmap_to_alist_def; FMAPAUX_MAP_FST_PAIR; FMAPAUX_ALL_DISTINCT_LIST_OF_SET;
           FDOM_FINITE]);;

let fmap_to_alist_inj = prove
 (`!f1 f2:(A,B)fmap. (fmap_to_alist f1 = fmap_to_alist f2) ==> (f1 = f2)`,
  MESON_TAC[fmap_to_alist_to_fmap]);;

let fmap_to_alist_preserves_FDOM = prove
 (`!(fm1:(A,B)fmap) (fm2:(A,B)fmap).
     (FDOM fm1 = FDOM fm2) ==>
     (MAP FST (fmap_to_alist fm1) = MAP FST (fmap_to_alist fm2))`,
  SIMP_TAC[fmap_to_alist_def; FMAPAUX_MAP_FST_PAIR]);;

let ALOOKUP_ALL_DISTINCT_EL = prove
 (`!(ls:(A#B)list) n.
     n < LENGTH ls /\ ALL_DISTINCT (MAP FST ls) ==>
     (ALOOKUP ls (FST (EL n ls)) = SOME (SND (EL n ls)))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC ALOOKUP_ALL_DISTINCT_MEM THEN
  ASM_SIMP_TAC[PAIR; MEM_EL]);;

let ALOOKUP_ZIP_MAP_SND = prove
 (`!(l1:A list) (l2:B list) (k:A) (f:B->C).
     (LENGTH l1 = LENGTH l2) ==>
     (ALOOKUP (ZIP l1 (MAP f l2)) = OPTION_MAP f o (ALOOKUP (ZIP l1 l2)))`,
  LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[LENGTH; NOT_SUC; GSYM NOT_SUC; MAP; ZIP; SUC_INJ] THEN
  REWRITE_TAC[FUN_EQ_THM; o_THM; ALOOKUP_THM; OPTION_MAP_DEF] THEN
  REPEAT STRIP_TAC THEN COND_CASES_TAC THEN
  ASM_SIMP_TAC[OPTION_MAP_DEF; o_THM]);;

let ALOOKUP_FILTER = prove
 (`!(ls:(A#B)list) x (P:A->bool).
     ALOOKUP (FILTER (\(k,v). P k) ls) x = if P x then ALOOKUP ls x else NONE`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[FILTER; ALOOKUP_THM; COND_ID] THEN
  SPEC_TAC(`h:A#B`,`h:A#B`) THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`a:A`; `b:B`; `x:A`; `P:A->bool`] THEN
  ASM_CASES_TAC `(P:A->bool) a` THEN ASM_REWRITE_TAC[ALOOKUP_THM] THEN
  ASM_MESON_TAC[]);;

let ALOOKUP_APPEND_same = prove
 (`!(l1:(A#B)list) l2 l.
     (ALOOKUP l1 = ALOOKUP l2) ==> (ALOOKUP (APPEND l1 l) = ALOOKUP (APPEND l2 l))`,
  SIMP_TAC[FUN_EQ_THM; ALOOKUP_APPEND]);;

let ALOOKUP_IN_FRANGE = prove
 (`!(ls:(A#B)list) k v. (ALOOKUP ls k = SOME v) ==> v IN FRANGE (alist_to_fmap ls)`,
  REWRITE_TAC[FRANGE_FLOOKUP; ALOOKUP_EQ_FLOOKUP] THEN MESON_TAC[]);;

let FRANGE_alist_to_fmap_SUBSET = prove
 (`!ls:(A#B)list. FRANGE (alist_to_fmap ls) SUBSET IMAGE SND (set_of_list ls)`,
  REWRITE_TAC[SUBSET; FRANGE_FLOOKUP; ALOOKUP_EQ_FLOOKUP; IN_IMAGE;
              IN_SET_OF_LIST] THEN
  MESON_TAC[ALOOKUP_MEM; SND]);;

let IN_FRANGE_alist_to_fmap_suff = prove
 (`!(P:B->bool) (ls:(A#B)list).
     (!v. MEM v (MAP SND ls) ==> P v) ==>
     (!v. v IN FRANGE (alist_to_fmap ls) ==> P v)`,
  REPEAT GEN_TAC THEN MP_TAC(SPEC `ls:(A#B)list` FRANGE_alist_to_fmap_SUBSET) THEN
  REWRITE_TAC[SUBSET; IN_IMAGE; IN_SET_OF_LIST; MEM_MAP] THEN MESON_TAC[]);;

let alist_to_fmap_MAP_matchable = prove
 (`!(f1:A->C) (f2:B->D) al mal v.
     INJ f1 (set_of_list (MAP FST al)) UNIV /\
     (mal = MAP (\(x,y). (f1 x, f2 y)) al) /\
     (v = MAP_KEYS f1 (f2 o_f alist_to_fmap al)) ==>
     (alist_to_fmap mal = v)`,
  MESON_TAC[alist_to_fmap_MAP]);;

let MAP_values_fmap_to_alist = prove
 (`!(f:B->C) (fm:(A,B)fmap).
     MAP (\(k,v). (k, f v)) (fmap_to_alist fm) = fmap_to_alist (f o_f fm)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[fmap_to_alist_def; FDOM_o_f; GSYM MAP_o] THEN
  MATCH_MP_TAC MAP_EQ THEN REWRITE_TAC[GSYM ALL_MEM; o_THM] THEN
  SIMP_TAC[MEM_LIST_OF_SET; FDOM_FINITE; o_f_FAPPLY]);;

let FMAPAUX_INJ_I = prove
 (`!(s:A->bool) t. INJ I s t <=> s SUBSET t`,
  REWRITE_TAC[INJ; SUBSET; I_THM] THEN MESON_TAC[]);;

let MAP_KEYS_I = prove
 (`!fm:(A,B)fmap. MAP_KEYS I fm = fm`,
  GEN_TAC THEN REWRITE_TAC[fmap_EXT; MAP_KEYS_def; IMAGE_I] THEN
  MP_TAC(ISPECL [`I:A->A`; `fm:(A,B)fmap`] MAP_KEYS_def) THEN
  REWRITE_TAC[FMAPAUX_INJ_I; SUBSET_UNIV; I_THM] THEN SIMP_TAC[]);;

let alist_to_fmap_MAP_values = prove
 (`!(f:B->C) (al:(A#B)list).
     alist_to_fmap (MAP (\(k,v). (k, f v)) al) = f o_f (alist_to_fmap al)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[MAP; alist_to_fmap_thm; o_f_FEMPTY] THEN
  SPEC_TAC(`h:A#B`,`h:A#B`) THEN
  ASM_REWRITE_TAC[FORALL_PAIR_THM; alist_to_fmap_thm; o_f_FUPDATE]);;

let set_MAP_FST_fmap_to_alist = prove
 (`!fm:(A,B)fmap. set_of_list (MAP FST (fmap_to_alist fm)) = FDOM fm`,
  MESON_TAC[fmap_to_alist_to_fmap; FDOM_alist_to_fmap]);;

let alookup_distinct_reverse = prove
 (`!(l:(A#B)list) k.
     ALL_DISTINCT (MAP FST l) ==> (ALOOKUP (REVERSE l) k = ALOOKUP l k)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[REVERSE; MAP; ALL_DISTINCT] THEN
  SPEC_TAC(`h:A#B`,`h:A#B`) THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`a:A`; `b:B`; `k:A`] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[ALOOKUP_APPEND; ALOOKUP_THM] THEN
  COND_CASES_TAC THENL
   [SUBGOAL_THEN `ALOOKUP (t:(A#B)list) k = NONE` (fun th -> REWRITE_TAC[th; option_CASE]) THEN
    ASM_MESON_TAC[ALOOKUP_NONE];
    STRUCT_CASES_TAC(ISPEC `ALOOKUP (t:(A#B)list) k` (cases "option")) THEN
    REWRITE_TAC[option_CASE]]);;

let fupdate_list_funion = prove
 (`!(m:(A,B)fmap) l. m |++ l = FUNION (FEMPTY |++ l) m`,
  REWRITE_TAC[FLOOKUP_EXT; FUN_EQ_THM; flookup_fupdate_list; FLOOKUP_FUNION;
              FLOOKUP_EMPTY] THEN
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `ALOOKUP (REVERSE (l:(A#B)list)) x` (cases "option")) THEN
  REWRITE_TAC[option_CASE]);;

let mem_to_flookup = prove
 (`!(x:A) (y:B) l.
     ALL_DISTINCT (MAP FST l) /\ MEM (x,y) l ==> (FLOOKUP (FEMPTY |++ l) x = SOME y)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[flookup_fupdate_list; alookup_distinct_reverse] THEN
  SUBGOAL_THEN `ALOOKUP (l:(A#B)list) x = SOME (y:B)`
   (fun th -> REWRITE_TAC[th; option_CASE]) THEN
  MATCH_MP_TAC ALOOKUP_ALL_DISTINCT_MEM THEN ASM_REWRITE_TAC[]);;

let alookup_filter = prove
 (`!(f:C) (l:(A#B)list) x. ALOOKUP l x = ALOOKUP (FILTER (\(x',y). x = x') l) x`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[FILTER; ALOOKUP_THM] THEN
  SPEC_TAC(`h:A#B`,`h:A#B`) THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`a:A`; `b:B`; `x:A`] THEN
  ASM_CASES_TAC `x:A = a` THEN ASM_REWRITE_TAC[ALOOKUP_THM] THEN
  ASM_MESON_TAC[]);;

let alist_range_def = new_definition
  `alist_range (m:(A#B)list) = {v | ?k. ALOOKUP m k = SOME v}`;;

let FEVERY_alist_to_fmap = prove
 (`!(P:A#B->bool) ls. ALL P ls ==> FEVERY P (alist_to_fmap ls)`,
  REWRITE_TAC[FEVERY_ALL_FLOOKUP; ALOOKUP_EQ_FLOOKUP; GSYM ALL_MEM] THEN
  MESON_TAC[ALOOKUP_MEM]);;

let ALL_DISTINCT_FEVERY_alist_to_fmap = prove
 (`!(P:A#B->bool) ls.
     ALL_DISTINCT (MAP FST ls) ==> (FEVERY P (alist_to_fmap ls) <=> ALL P ls)`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN REWRITE_TAC[FEVERY_alist_to_fmap] THEN
  REWRITE_TAC[FEVERY_ALL_FLOOKUP; ALOOKUP_EQ_FLOOKUP; GSYM ALL_MEM] THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN ASM_MESON_TAC[ALOOKUP_ALL_DISTINCT_MEM]);;

(* ------------------------------------------------------------------------- *)
(* Updating and deleting a key in an association list.                       *)
(* ------------------------------------------------------------------------- *)

let AFUPDKEY_def = define
  `(AFUPDKEY (k:A) (f:B->B) [] = []) /\
   (AFUPDKEY k f (CONS (k',v) rest) =
      if k = k' then CONS (k,f v) rest else CONS (k',v) (AFUPDKEY k f rest))`;;

let AFUPDKEY_ALOOKUP = prove
 (`!(k2:A) (f:B->B) al k1.
     ALOOKUP (AFUPDKEY k2 f al) k1 =
     option_CASE (ALOOKUP al k1) NONE
       (\v. if k1 = k2 then SOME (f v) else SOME v)`,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[AFUPDKEY_def; ALOOKUP_THM; option_CASE] THEN
  SPEC_TAC(`h:A#B`,`h:A#B`) THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`a:A`; `b:B`; `k1:A`] THEN
  REWRITE_TAC[AFUPDKEY_def] THEN
  ASM_CASES_TAC `a:A = k1` THEN ASM_CASES_TAC `k2:A = a` THEN
  ASM_REWRITE_TAC[ALOOKUP_THM; option_CASE] THEN
  ((STRUCT_CASES_TAC(ISPEC `ALOOKUP (t:(A#B)list) k1` (cases "option")) THEN
    REWRITE_TAC[option_CASE] THEN NO_TAC) ORELSE
   ASM_MESON_TAC[]));;

let MAP_FST_AFUPDKEY = prove
 (`!(f:A) (k:B->B) alist. MAP FST (AFUPDKEY f k alist) = MAP FST alist`,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[AFUPDKEY_def; MAP] THEN
  SPEC_TAC(`h:A#B`,`h:A#B`) THEN REWRITE_TAC[FORALL_PAIR_THM; AFUPDKEY_def] THEN
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[MAP]);;

let AFUPDKEY_unchanged = prove
 (`!(k:A) (f:B->B) alist.
     (!v. (ALOOKUP alist k = SOME v) ==> (f v = v)) ==> (AFUPDKEY k f alist = alist)`,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[AFUPDKEY_def] THEN
  SPEC_TAC(`h:A#B`,`h:A#B`) THEN REWRITE_TAC[FORALL_PAIR_THM; AFUPDKEY_def] THEN
  MAP_EVERY X_GEN_TAC [`a:A`; `b:B`] THEN REWRITE_TAC[ALOOKUP_THM] THEN
  ASM_CASES_TAC `a:A = k` THEN ASM_REWRITE_TAC[CONS_11; PAIR_EQ; option_INJ] THEN
  ASM_MESON_TAC[]);;

let AFUPDKEY_o = prove
 (`!(k:A) (f1:B->B) f2 al.
     AFUPDKEY k f1 (AFUPDKEY k f2 al) = AFUPDKEY k (f1 o f2) al`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[AFUPDKEY_def] THEN
  SPEC_TAC(`h:A#B`,`h:A#B`) THEN REWRITE_TAC[FORALL_PAIR_THM; AFUPDKEY_def] THEN
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[AFUPDKEY_def; o_THM]);;

let AFUPDKEY_eq = prove
 (`!(k:A) (f1:B->B) l f2.
     (!v. (ALOOKUP l k = SOME v) ==> (f1 v = f2 v)) ==>
     (AFUPDKEY k f1 l = AFUPDKEY k f2 l)`,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[AFUPDKEY_def] THEN
  SPEC_TAC(`h:A#B`,`h:A#B`) THEN REWRITE_TAC[FORALL_PAIR_THM; AFUPDKEY_def] THEN
  MAP_EVERY X_GEN_TAC [`a:A`; `b:B`; `f2:B->B`] THEN REWRITE_TAC[ALOOKUP_THM] THEN
  ASM_CASES_TAC `a:A = k` THEN ASM_REWRITE_TAC[CONS_11; PAIR_EQ; option_INJ] THEN
  ASM_MESON_TAC[]);;

let AFUPDKEY_I = prove
 (`!n:A. AFUPDKEY n (I:B->B) = I`,
  GEN_TAC THEN REWRITE_TAC[FUN_EQ_THM; I_THM] THEN
  MATCH_MP_TAC list_INDUCT THEN REWRITE_TAC[AFUPDKEY_def] THEN
  REWRITE_TAC[FORALL_PAIR_THM; AFUPDKEY_def; I_THM] THEN MESON_TAC[]);;

let LENGTH_AFUPDKEY = prove
 (`!(ls:(A#B)list) (k:A) (f:B->B). LENGTH (AFUPDKEY k f ls) = LENGTH ls`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[AFUPDKEY_def] THEN
  SPEC_TAC(`h:A#B`,`h:A#B`) THEN REWRITE_TAC[FORALL_PAIR_THM; AFUPDKEY_def] THEN
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[LENGTH]);;

let AFUPDKEY_comm = prove
 (`!(k1:A) k2 (f1:B->B) f2 l.
     ~(k1 = k2) ==>
     (AFUPDKEY k2 f2 (AFUPDKEY k1 f1 l) = AFUPDKEY k1 f1 (AFUPDKEY k2 f2 l))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN SPEC_TAC(`l:(A#B)list`,`l:(A#B)list`) THEN
  LIST_INDUCT_TAC THEN REWRITE_TAC[AFUPDKEY_def] THEN
  SPEC_TAC(`h:A#B`,`h:A#B`) THEN REWRITE_TAC[FORALL_PAIR_THM; AFUPDKEY_def] THEN
  MAP_EVERY X_GEN_TAC [`a:A`; `b:B`] THEN
  ASM_CASES_TAC `k1:A = a` THEN ASM_CASES_TAC `k2:A = a` THEN
  ASM_REWRITE_TAC[AFUPDKEY_def] THEN ASM_MESON_TAC[]);;

let ADELKEY_def = new_definition
  `ADELKEY (k:A) (alist:(A#B)list) = FILTER (\p. ~(FST p = k)) alist`;;

let MEM_ADELKEY = prove
 (`!(al:(A#B)list) (k1:A) (v:B) k2.
     MEM (k1,v) (ADELKEY k2 al) <=> ~(k1 = k2) /\ MEM (k1,v) al`,
  REWRITE_TAC[ADELKEY_def; MEM_FILTER] THEN MESON_TAC[]);;

let ALOOKUP_ADELKEY = prove
 (`!(al:(A#B)list) (k1:A) k2.
     ALOOKUP (ADELKEY k1 al) k2 = if k1 = k2 then NONE else ALOOKUP al k2`,
  REWRITE_TAC[ADELKEY_def] THEN
  LIST_INDUCT_TAC THEN REWRITE_TAC[FILTER; ALOOKUP_THM; COND_ID] THEN
  SPEC_TAC(`h:A#B`,`h:A#B`) THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`a:A`; `b:B`; `k1:A`; `k2:A`] THEN
  ASM_CASES_TAC `a:A = k1` THEN ASM_REWRITE_TAC[ALOOKUP_THM] THEN
  ASM_MESON_TAC[]);;

let ADELKEY_AFUPDKEY_same = prove
 (`!(fd:A) (f:B->B) ls. ADELKEY fd (AFUPDKEY fd f ls) = ADELKEY fd ls`,
  GEN_TAC THEN GEN_TAC THEN REWRITE_TAC[ADELKEY_def] THEN
  LIST_INDUCT_TAC THEN REWRITE_TAC[AFUPDKEY_def] THEN
  SPEC_TAC(`h:A#B`,`h:A#B`) THEN REWRITE_TAC[FORALL_PAIR_THM; AFUPDKEY_def] THEN
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[FILTER] THEN
  ASM_MESON_TAC[]);;

let ADELKEY_unchanged = prove
 (`!(x:A) (ls:(A#B)list). ((ADELKEY x ls = ls) <=> ~MEM x (MAP FST ls))`,
  GEN_TAC THEN REWRITE_TAC[ADELKEY_def] THEN
  LIST_INDUCT_TAC THEN REWRITE_TAC[FILTER; MAP; MEM] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[CONS_11] THEN
  DISCH_THEN(MP_TAC o AP_TERM `LENGTH:(A#B)list->num`) THEN
  MP_TAC(ISPECL [`\p:A#B. ~(FST p = x)`; `t:(A#B)list`] LENGTH_FILTER) THEN
  REWRITE_TAC[LENGTH] THEN ARITH_TAC);;

let ADELKEY_AFUPDKEY = prove
 (`!ls (f:B->B) (x:A) y.
     ~(x = y) ==> (ADELKEY x (AFUPDKEY y f ls) = AFUPDKEY y f (ADELKEY x ls))`,
  REWRITE_TAC[ADELKEY_def] THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[AFUPDKEY_def; FILTER] THEN
  SPEC_TAC(`h:A#B`,`h:A#B`) THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`a:A`; `b:B`; `f:B->B`; `x:A`; `y:A`] THEN DISCH_TAC THEN
  REWRITE_TAC[AFUPDKEY_def] THEN
  ASM_CASES_TAC `y:A = a` THEN ASM_REWRITE_TAC[FILTER] THENL
   [FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
    SUBGOAL_THEN `~(y:A = x)` (fun th -> REWRITE_TAC[th; AFUPDKEY_def]) THEN
    ASM_MESON_TAC[];
    COND_CASES_TAC THEN ASM_SIMP_TAC[AFUPDKEY_def]]);;

let FLOOKUP_FUPDATE_LIST = prove
 (`!(xs:(A#B)list) k m.
     FLOOKUP (m |++ xs) k =
     option_CASE (ALOOKUP (REVERSE xs) k) (FLOOKUP m k) (\x. SOME x)`,
  REWRITE_TAC[flookup_fupdate_list]);;

(* ------------------------------------------------------------------------- *)
(* The HOL4 [simp] theorems of this theory, for the project simpset.         *)
(* (ALOOKUP_SOME_FAPPLY_alist_to_fmap is left out: its v occurs only in the  *)
(* hypothesis and the right side, which HOL Light's simplifier cannot use.) *)
(* ------------------------------------------------------------------------- *)

let _ = cake_add_simps
  [fmap_to_alist_FEMPTY; alist_to_fmap_thm; ALOOKUP_def; ALOOKUP_EQ_FLOOKUP;
   MEM_pair_fmap_to_alist_FLOOKUP; LENGTH_fmap_to_alist; fmap_to_alist_to_fmap;
   FDOM_alist_to_fmap; alist_to_fmap_APPEND; ALL_DISTINCT_fmap_to_alist_keys;
   MAP_KEYS_I; set_MAP_FST_fmap_to_alist; MAP_FST_AFUPDKEY; LENGTH_AFUPDKEY;
   MEM_ADELKEY; ADELKEY_AFUPDKEY_same];;

(* ------------------------------------------------------------------------- *)
(* Lemmas used by several later files.                                       *)
(* ------------------------------------------------------------------------- *)

let FMAPAUX_FEMPTY_FUPDATE_LIST = prove
 (`!l:(A#B)list. ALL_DISTINCT (MAP FST l) ==> FEMPTY |++ l = alist_to_fmap l`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[fmap_eq_flookup; FLOOKUP_FUPDATE_LIST] THEN
  ASM_SIMP_TAC[alookup_distinct_reverse; CONJUNCT1 ALOOKUP_EQ_FLOOKUP; FLOOKUP_EMPTY] THEN
  GEN_TAC THEN QCASES_ON "ALOOKUP (l:(A#B)list) x" THEN REWRITE_TAC[case_def "option"]);;
